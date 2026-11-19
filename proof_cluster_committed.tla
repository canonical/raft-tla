--------------- MODULE proof_cluster_committed ----------------
\* proof_cluster_committed.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_cluster_committed_base

\* All servers that have replicated a given log entry at a specific index and term.
ClusterReplicated(index, term) == { i \in Server : /\ index \in DOMAIN log[i]
                                                   /\ log[i][index].term = term }

\* All servers that have agreed on a given log entry at a specific index and term during the entry term itself.
\* A leader can only commit entries replicated in its own term. Similarly, a cluster-wide agreement on an entry
\* requires that it has been replicated by a quorum of servers *in the term it was created in*. This property
\* is useful as it captures the same term-only agreement, but from the holistic point of view of the entire cluster.
\* Nodes can only learn about agreement *after* it happened, but once it happened, the cluster i guaranteed to 
\* *eventually* learn about it. This makes this property somehow more stable and easier to reason about.
ClusterAgree(index, term) == { 
    i \in ClusterReplicated(index, term) :
        \* either the one that generated the entry
        \/ Won(i, term)
        \* or a follower that has acknowledged the entry
        \/ \E m \in messages: 
            /\ m.mtype = AppendEntriesResponse
            /\ m.mmatchIndex = index
            /\ m.mterm = term 
            /\ m.msuccess = TRUE 
            /\ m.msource = i }

ClusterEntries ==
    UNION {
        {[index |-> k, term |-> log[i][k].term] : k \in DOMAIN log[i]} :
        i \in Server
    }

\* This is the set of log entries that have been agreed upon. Given that entries
\* can only be agreed in their own term, this set is *sparse* and does not contain
\* all committed entries.
\* This set can only grow over time as more entries are agreed upon.
ClusterAgreeEntries ==
    {entry \in ClusterEntries : ClusterAgree(entry.index, entry.term) \in Quorum}

StableClusterAgreeEntriesInv == ClusterAgreeEntries \subseteq ClusterAgreeEntries'

EntryAgreementEvidence(server, index, term) ==
    \/ Won(server, term)
    \/ \E response \in messages:
           /\ response.mtype = AppendEntriesResponse
           /\ response.msuccess
           /\ response.msource = server
           /\ response.mterm = term
           /\ response.mmatchIndex = index

\* Servers that have already agreed, or can still agree without decreasing their term.
ClusterMightAgree(index, term) ==
    {server \in Server:
        currentTerm[server] <= term \/ EntryAgreementEvidence(server, index, term)}

HistoricalEntryKeys ==
    {[index |-> edge.index, term |-> edge.term]: edge \in HistoricalEntryEdges}

ClusterAgreeCandidateEntries ==
    {entry \in HistoricalEntryKeys:
        ClusterMightAgree(entry.index, entry.term) \in Quorum}

VoteRequestCoversEntry(request, entry) ==
    \/ request.mlastLogTerm > entry.term
    \/ /\ request.mlastLogTerm = entry.term
       /\ request.mlastLogIndex >= entry.index

PositiveVoteRequestOriginInv ==
    \A response \in messages:
        response.mtype = RequestVoteResponse /\ response.mvoteGranted =>
            \E request \in messages:
                /\ request.mtype = RequestVoteRequest
                /\ request.msource = response.mdest
                /\ request.mdest = response.msource
                /\ request.mterm = response.mterm

CandidateRequestSnapshotInv ==
    \A candidate \in Server: \A request \in messages:
        /\ state[candidate] = Candidate
        /\ request.mtype = RequestVoteRequest
        /\ request.msource = candidate
        /\ request.mterm = currentTerm[candidate]
        => /\ request.mlastLogTerm = LastTerm(log[candidate])
           /\ request.mlastLogIndex = Len(log[candidate])

AppendRequestSenderWonInv ==
    \A request \in AppendRequests: Won(request.msource, request.mterm)

AppendRequestSenderNotCandidateInv ==
    \A request \in AppendRequests:
        request.mterm = currentTerm[request.msource] => state[request.msource] # Candidate

SuccessfulResponseRecipientWonInv ==
    \A response \in messages:
        response.mtype = AppendEntriesResponse /\ response.msuccess =>
            Won(response.mdest, response.mterm)

RequestAcknowledgmentAnchorInv ==
    \A request \in AppendRequests: \A entry \in HistoricalEntryKeys:
        /\ entry.term = request.mterm
        /\ entry.index = request.mprevLogIndex + Len(request.mentries)
        => IF request.mentries = << >>
           THEN request.mprevLogTerm = entry.term
           ELSE request.mentries[1].term = entry.term

CandidateEntryEvidenceRetainedInv ==
    \A entry \in ClusterAgreeCandidateEntries: \A server \in Server:
        EntryAgreementEvidence(server, entry.index, entry.term) =>
            LogHasTermAt(server, entry.term, entry.index)

CandidateNewerLogPrefixesInv ==
    \A server \in Server: \A index \in DOMAIN log[server]:
        \A entry \in ClusterAgreeCandidateEntries:
            entry.term < log[server][index].term =>
                /\ entry.index <= index
                /\ LogHasTermAt(server, entry.term, entry.index)

HistoricalVoteProtectionInv ==
    \A request \in messages: \A entry \in ClusterAgreeCandidateEntries:
        /\ request.mtype = RequestVoteRequest
        /\ entry.term < request.mterm
        /\ Grant(request.mdest, request.msource, request.mterm)
        /\ EntryAgreementEvidence(request.mdest, entry.index, entry.term)
        => VoteRequestCoversEntry(request, entry)

CandidateAppendPrefixInv ==
    \A request \in AppendRequests: \A entry \in ClusterAgreeCandidateEntries:
        entry.term <= request.mterm =>
            \A server \in ClusterReplicated(entry.index, entry.term):
                /\ request.mprevLogIndex < entry.index
                /\ request.mentries # << >>
                => request.mentries[1].term = log[server][request.mprevLogIndex + 1].term

HistoricalNewerEntryBoundaryInv ==
    \A edge \in HistoricalEntryEdges: \A entry \in ClusterAgreeCandidateEntries:
        entry.term < edge.term =>
            /\ entry.index < edge.index
            /\ entry.term <= edge.previous

HistoricalSameTermBoundaryInv ==
    \A left, right \in HistoricalEntryEdges:
        left.term = right.term /\ left.index < right.index =>
            right.previous = right.term

ActiveAppendRequestSnapshotInv ==
    \A request \in AppendRequests:
        /\ currentTerm[request.msource] = request.mterm
        /\ state[request.msource] = Leader
        => /\ request.mprevLogIndex > 0 =>
                  log[request.msource][request.mprevLogIndex].term = request.mprevLogTerm
           /\ \A offset \in DOMAIN request.mentries:
                  request.mentries[offset] =
                      log[request.msource][request.mprevLogIndex + offset]

VoteRequestsUniformInv ==
    \A left, right \in messages:
        /\ left.mtype = RequestVoteRequest /\ right.mtype = RequestVoteRequest
        /\ left.msource = right.msource /\ left.mterm = right.mterm
        => /\ left.mlastLogTerm = right.mlastLogTerm
           /\ left.mlastLogIndex = right.mlastLogIndex

LeaderCandidateEntryInv ==
    \A leader \in Server: \A entry \in ClusterAgreeCandidateEntries:
        /\ state[leader] = Leader /\ entry.term <= currentTerm[leader]
        => LogHasTermAt(leader, entry.term, entry.index)

CandidateEntryJointInv ==
    /\ CandidateEntryEvidenceRetainedInv
    /\ CandidateAppendPrefixInv
    /\ HistoricalNewerEntryBoundaryInv
    /\ HistoricalVoteProtectionInv

SameTermEntryIntervalsInv ==
    \A left, right \in Server:
        \A high \in DOMAIN log[left]: \A low \in DOMAIN log[right]:
            /\ low <= high
            /\ log[left][high].term = log[right][low].term
            => /\ low \in DOMAIN log[left]
               /\ log[left][low].term = log[right][low].term


SharedLogPrefix(left, right, endpoint) ==
    /\ endpoint \in DOMAIN log[left]
    /\ endpoint \in DOMAIN log[right]
    /\ SubSeq(log[left], 1, endpoint) = SubSeq(log[right], 1, endpoint)

AppendRequestPrefixCompatible(request, entries, endpoint) ==
    /\ request.mprevLogIndex < endpoint
    /\ request.mentries # << >>
    => request.mentries[1].term = entries[request.mprevLogIndex + 1].term

LeaderClusterAgreeInv ==
    \A leader \in Server: \A entry \in ClusterAgreeEntries:
        /\ state[leader] = Leader
        /\ entry.term <= currentTerm[leader]
        => /\ entry.index \in DOMAIN log[leader]
           /\ log[leader][entry.index].term = entry.term

ClusterAgreeAppendInv ==
    \A request \in AppendRequests: \A entry \in ClusterAgreeEntries:
        entry.term <= request.mterm =>
            \A server \in ClusterReplicated(entry.index, entry.term):
                AppendRequestPrefixCompatible(request, log[server], entry.index)

ClusterAgreeSupportInv == LeaderClusterAgreeInv /\ ClusterAgreeAppendInv

CandidateEntryBaseInv ==
    /\ InductiveInvariant /\ LogMatchingInv /\ EntryEdgeConsistency
    /\ TermOrderingInv /\ CandidateCurrentTermFree /\ AppendRequestRootTerm
    /\ AppendRequestSenderWonInv /\ SuccessfulResponseRecipientWonInv
    /\ HistoricalSameTermBoundaryInv
    /\ AppendRequestSenderNotCandidateInv

ClusterAgreeProofInv ==
    /\ InductiveInvariant
    /\ LogMatchingInv
    /\ EntryEdgeConsistency
    /\ TermOrderingInv
    /\ CandidateCurrentTermFree
    /\ ClusterAgreeSupportInv

ClusterAgreeCandidateProofInv ==
    /\ InductiveInvariant
    /\ LogMatchingInv
    /\ EntryEdgeConsistency
    /\ TermOrderingInv
    /\ CandidateCurrentTermFree
    /\ PositiveVoteRequestOriginInv
    /\ CandidateRequestSnapshotInv
    /\ GrantTermBoundInv
    /\ CandidateEntryEvidenceRetainedInv
    /\ CandidateNewerLogPrefixesInv
    /\ HistoricalVoteProtectionInv
    /\ SameTermEntryIntervalsInv

CandidateEntryAuxiliaryInv ==
    /\ PositiveVoteRequestOriginInv
    /\ CandidateRequestSnapshotInv
    /\ ActiveAppendRequestSnapshotInv
    /\ VoteRequestsUniformInv
    /\ RequestAcknowledgmentAnchorInv

LeaderCompletenessInductionInv ==
    /\ CandidateEntryAuxiliaryInv
    /\ LeaderCandidateEntryInv
    /\ CandidateEntryJointInv

\* Any new elected leader must have all cluster-agreed entries in its log.
\* This is a hard requirement for any new leader in the cluster.
NewLeaderCandidateEntryCompleteness ==
    \A leader \in Server:
        BecomeLeader(leader) =>
            \A entry \in ClusterAgreeCandidateEntries':
                entry.term <= currentTerm'[leader] =>
                    LogHasTermAt(leader, entry.term, entry.index)'

---------------------------------------------------------------

LEMMA ReplicationAndMessagesGrowClusterAgreeEntries ==
    /\ messages \subseteq messages'
    /\ \A server \in Server: \A index \in DOMAIN log[server]:
           /\ index \in DOMAIN log'[server]
           /\ log'[server][index].term = log[server][index].term
    => StableClusterAgreeEntriesInv
<1> SUFFICES ASSUME messages \subseteq messages',
                    \A server \in Server: \A index \in DOMAIN log[server]:
                        /\ index \in DOMAIN log'[server]
                        /\ log'[server][index].term = log[server][index].term,
                    NEW entry \in ClusterAgreeEntries
             PROVE entry \in ClusterAgreeEntries'
    BY DEF StableClusterAgreeEntriesInv
<1>replicated. \A index, term:
        ClusterReplicated(index, term) \subseteq ClusterReplicated(index, term)'
    BY DEF ClusterReplicated
<1>won. \A server, term: Won(server, term) => Won(server, term)'
    BY DEF Won, Started, VoteFor, Grant
<1>agree. ClusterAgree(entry.index, entry.term)
              \subseteq ClusterAgree(entry.index, entry.term)'
    BY <1>replicated, <1>won DEF ClusterAgree
<1>entries. entry \in ClusterEntries'
    BY DEF ClusterAgreeEntries, ClusterEntries
<1>quorum. ClusterAgree(entry.index, entry.term)' \in Quorum
    BY <1>agree, QuorumSuperset
    DEF ClusterAgreeEntries, ClusterAgree, ClusterReplicated
<1> QED BY <1>entries, <1>quorum DEF ClusterAgreeEntries

LEMMA UnchangedLogPreservesClusterAgreeEntries ==
    /\ messages \subseteq messages'
    /\ UNCHANGED log
    => StableClusterAgreeEntriesInv
    BY ReplicationAndMessagesGrowClusterAgreeEntries

LEMMA RestartPreservesClusterAgreeEntries ==
    \A i \in Server:
        InductiveInvariant /\ Restart(i) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF Restart

LEMMA TimeoutPreservesClusterAgreeEntries ==
    \A i \in Server:
        InductiveInvariant /\ Timeout(i) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries
    DEF Timeout, WithMessages

LEMMA BecomeLeaderPreservesClusterAgreeEntries ==
    \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF BecomeLeader

LEMMA ClientRequestPreservesClusterAgreeEntries ==
    \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => StableClusterAgreeEntriesInv
<1> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                    InductiveInvariant, ClientRequest(i, v)
             PROVE StableClusterAgreeEntriesInv
    OBVIOUS
<1>types. /\ log \in [Server -> Seq(LogEntry)]
            /\ [term |-> currentTerm[i], value |-> v] \in LogEntry
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK, LogEntry
<1>retain. \A server \in Server: \A index \in DOMAIN log[server]:
        /\ index \in DOMAIN log'[server]
        /\ log'[server][index].term = log[server][index].term
    <2> SUFFICES ASSUME NEW server \in Server, NEW index \in DOMAIN log[server]
                 PROVE /\ index \in DOMAIN log'[server]
                       /\ log'[server][index].term = log[server][index].term
        OBVIOUS
    <2>other. CASE server # i
        BY <2>other, <1>types DEF ClientRequest
    <2>same. CASE server = i
        BY <2>same, <1>types, AppendProperties, LenProperties
        DEF ClientRequest
    <2> QED BY <2>other, <2>same
<1> QED BY <1>retain, ReplicationAndMessagesGrowClusterAgreeEntries
    DEF ClientRequest

LEMMA AdvanceCommitIndexPreservesClusterAgreeEntries ==
    \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF AdvanceCommitIndex

LEMMA AppendEntriesPreservesClusterAgreeEntries ==
    \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries
    DEF AppendEntries, Send, WithMessage, WithMessages

LEMMA LeaderStepDownPreservesClusterAgreeEntries ==
    \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF LeaderStepDown

LEMMA UpdateTermPreservesClusterAgreeEntries ==
    \A m \in messages:
        InductiveInvariant /\ UpdateTerm(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF UpdateTerm

LEMMA HandleRequestVoteRequestPreservesClusterAgreeEntries ==
    \A m \in messages:
        /\ InductiveInvariant /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries
    DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages

LEMMA HandleRequestVoteResponsePreservesClusterAgreeEntries ==
    \A m \in messages:
        /\ InductiveInvariant /\ m.mtype = RequestVoteResponse
        /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF HandleRequestVoteResponse

LEMMA ClusterAgreeSupportInvInit == Init => ClusterAgreeSupportInv
    BY DEF Init, InitServerVars, InitLogVars, ClusterAgreeSupportInv,
        LeaderClusterAgreeInv, ClusterAgreeAppendInv, ClusterAgreeEntries, ClusterEntries

LEMMA AppendRequestPreservesCompatiblePrefix ==
    \A m \in messages: \A endpoint \in DOMAIN log[m.mdest]:
        /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
        /\ AppendRequestPrefixCompatible(m, log[m.mdest], endpoint)
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => /\ endpoint \in DOMAIN log'[m.mdest]
           /\ SubSeq(log'[m.mdest], 1, endpoint)
                  = SubSeq(log[m.mdest], 1, endpoint)
<1> SUFFICES ASSUME NEW m \in messages,
                    NEW endpoint \in DOMAIN log[m.mdest],
                    InductiveInvariant, m.mtype = AppendEntriesRequest,
                    AppendRequestPrefixCompatible(m, log[m.mdest], endpoint),
                    HandleAppendEntriesRequest(m.mdest, m.msource, m)
             PROVE /\ endpoint \in DOMAIN log'[m.mdest]
                   /\ SubSeq(log'[m.mdest], 1, endpoint)
                          = SubSeq(log[m.mdest], 1, endpoint)
    OBVIOUS
<1>types. /\ m.mdest \in Server /\ m.msource \in Server
            /\ m.mprevLogIndex \in Nat
            /\ log \in [Server -> Seq(LogEntry)]
            /\ log' \in [Server -> Seq(LogEntry)]
            /\ endpoint \in 1..Len(log[m.mdest])
    BY MessageFieldsTypeOK, HandleAppendEntriesRequestLogVarsTypeOK, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1>unchanged. CASE log' = log
    BY <1>unchanged
<1>changed. CASE log' # log
    <2>shape. /\ m.mprevLogIndex \in 0..Len(log[m.mdest])
                /\ Len(log'[m.mdest]) = m.mprevLogIndex + 1
        BY <1>changed, <1>types, AppendRequestChangedLogShape
    <2>cut. endpoint <= m.mprevLogIndex
        BY <1>changed, <1>types, SMT
        DEF AppendRequestPrefixCompatible, HandleAppendEntriesRequest
    <2>domain. endpoint \in DOMAIN log'[m.mdest]
        BY <1>types, <2>shape, <2>cut, LenProperties
    <2> QED BY <1>types, <2>shape, <2>cut, <2>domain,
        AppendRequestRetainsMatchedPrefix
<1> QED BY <1>unchanged, <1>changed

LEMMA LeaderClusterAgreeGivesSharedPrefix ==
    InductiveInvariant /\ LogMatchingInv /\ LeaderClusterAgreeInv =>
        \A leader \in Server: \A entry \in ClusterAgreeEntries:
            /\ state[leader] = Leader
            /\ entry.term <= currentTerm[leader]
            => \A server \in ClusterReplicated(entry.index, entry.term):
                   SharedLogPrefix(leader, server, entry.index)
<1> SUFFICES ASSUME InductiveInvariant, LogMatchingInv, LeaderClusterAgreeInv,
                    NEW leader \in Server, NEW entry \in ClusterAgreeEntries,
                    state[leader] = Leader, entry.term <= currentTerm[leader],
                    NEW server \in ClusterReplicated(entry.index, entry.term)
             PROVE SharedLogPrefix(leader, server, entry.index)
    OBVIOUS
<1>leader. /\ entry.index \in DOMAIN log[leader]
             /\ log[leader][entry.index].term = entry.term
    BY DEF LeaderClusterAgreeInv
<1>server. /\ server \in Server
             /\ entry.index \in DOMAIN log[server]
             /\ log[server][entry.index].term = entry.term
    BY DEF ClusterReplicated
<1>domain. entry.index \in (1..Len(log[leader])) \cap (1..Len(log[server]))
    BY <1>leader, <1>server, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1> QED BY <1>leader, <1>server, <1>domain
    DEF SharedLogPrefix, LogMatchingInv

LEMMA SharedPrefixTransfersRequestCompatibility ==
    \A left, right \in Server, m \in messages:
        \A endpoint \in DOMAIN log[left]:
            /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
            /\ SharedLogPrefix(left, right, endpoint)
            /\ AppendRequestPrefixCompatible(m, log[left], endpoint)
            => AppendRequestPrefixCompatible(m, log[right], endpoint)
<1> SUFFICES ASSUME NEW left \in Server, NEW right \in Server, NEW m \in messages,
                    NEW endpoint \in DOMAIN log[left],
                    InductiveInvariant, m.mtype = AppendEntriesRequest,
                    SharedLogPrefix(left, right, endpoint),
                    AppendRequestPrefixCompatible(m, log[left], endpoint),
                    m.mprevLogIndex < endpoint, m.mentries # << >>
             PROVE m.mentries[1].term = log[right][m.mprevLogIndex + 1].term
    BY DEF AppendRequestPrefixCompatible
<1>types. /\ log[left] \in Seq(LogEntry) /\ log[right] \in Seq(LogEntry)
            /\ m.mprevLogIndex \in Nat /\ endpoint \in Nat
            /\ m.mprevLogIndex + 1 \in 1..endpoint
            /\ endpoint <= Len(log[left]) /\ endpoint <= Len(log[right])
    BY MessageFieldsTypeOK, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, MsgTypeOK, SharedLogPrefix
<1>entry. log[left][m.mprevLogIndex + 1] = log[right][m.mprevLogIndex + 1]
    BY <1>types, EqualLogPrefixesEntryEqual DEF SharedLogPrefix
<1> QED BY <1>entry DEF AppendRequestPrefixCompatible

LEMMA AppendRequestPreservesSharedPrefix ==
    \A leader \in Server, m \in messages:
        \A endpoint \in DOMAIN log[m.mdest]:
            /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
            /\ leader # m.mdest
            /\ SharedLogPrefix(leader, m.mdest, endpoint)
            /\ AppendRequestPrefixCompatible(m, log[leader], endpoint)
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => SharedLogPrefix(leader, m.mdest, endpoint)'
<1> SUFFICES ASSUME NEW leader \in Server, NEW m \in messages,
                    NEW endpoint \in DOMAIN log[m.mdest],
                    InductiveInvariant, m.mtype = AppendEntriesRequest,
                    leader # m.mdest,
                    SharedLogPrefix(leader, m.mdest, endpoint),
                    AppendRequestPrefixCompatible(m, log[leader], endpoint),
                    HandleAppendEntriesRequest(m.mdest, m.msource, m)
             PROVE SharedLogPrefix(leader, m.mdest, endpoint)'
    OBVIOUS
<1>types. /\ m.mdest \in Server /\ m.msource \in Server
            /\ log \in [Server -> Seq(LogEntry)]
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1>leader. log'[leader] = log[leader]
    BY <1>types DEF HandleAppendEntriesRequest
<1>compatible. AppendRequestPrefixCompatible(m, log[m.mdest], endpoint)
    BY <1>types, SharedPrefixTransfersRequestCompatibility DEF SharedLogPrefix
<1>prefix. /\ endpoint \in DOMAIN log'[m.mdest]
             /\ SubSeq(log'[m.mdest], 1, endpoint)
                    = SubSeq(log[m.mdest], 1, endpoint)
    BY <1>compatible, AppendRequestPreservesCompatiblePrefix
<1> QED BY <1>leader, <1>prefix DEF SharedLogPrefix

LEMMA CompatibleAppendPreservesClusterReplicas ==
    \A m \in messages:
        /\ InductiveInvariant /\ ClusterAgreeAppendInv
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => \A entry \in ClusterAgreeEntries:
               ClusterReplicated(entry.index, entry.term)
                   \subseteq ClusterReplicated(entry.index, entry.term)'
<1> SUFFICES ASSUME NEW m \in messages, InductiveInvariant, ClusterAgreeAppendInv,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(m.mdest, m.msource, m),
                    NEW entry \in ClusterAgreeEntries,
                    NEW server \in ClusterReplicated(entry.index, entry.term)
             PROVE server \in ClusterReplicated(entry.index, entry.term)'
    OBVIOUS
<1>types. /\ m.mdest \in Server /\ m.msource \in Server
            /\ server \in Server
            /\ log \in [Server -> Seq(LogEntry)]
            /\ log' \in [Server -> Seq(LogEntry)]
            /\ entry.index \in DOMAIN log[server]
            /\ log[server][entry.index].term = entry.term
    BY MessageFieldsTypeOK, HandleAppendEntriesRequestLogVarsTypeOK
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK, ClusterReplicated
<1>other. CASE server # m.mdest
    BY <1>other, <1>types DEF HandleAppendEntriesRequest, ClusterReplicated
<1>same. CASE server = m.mdest
    <2>unchanged. CASE log' = log
        BY <2>unchanged DEF ClusterReplicated
    <2>changed. CASE log' # log
        <3>term. /\ m.mterm = currentTerm[m.mdest]
                  /\ entry.term <= m.mterm
            BY <1>same, <1>types, <2>changed, SMT
            DEF HandleAppendEntriesRequest, InductiveInvariant, LogTermBoundInv
        <3>compatible. AppendRequestPrefixCompatible(m, log[m.mdest], entry.index)
            BY <1>same, <3>term DEF ClusterAgreeAppendInv, AppendRequests
        <3>prefix. /\ entry.index \in DOMAIN log'[server]
                    /\ SubSeq(log'[server], 1, entry.index)
                           = SubSeq(log[server], 1, entry.index)
            BY <1>same, <1>types, <3>compatible, AppendRequestPreservesCompatiblePrefix
        <3>domain. /\ entry.index \in Nat
                    /\ entry.index \in 1..entry.index
                    /\ entry.index <= Len(log[server])
                    /\ entry.index <= Len(log'[server])
            BY <1>types, <3>prefix, LenProperties
        <3>entry. log'[server][entry.index] = log[server][entry.index]
            BY <1>types, <3>prefix, <3>domain, EqualLogPrefixesEntryEqual
        <3> QED BY <1>types, <3>prefix, <3>entry DEF ClusterReplicated
    <2> QED BY <2>unchanged, <2>changed
<1> QED BY <1>other, <1>same

LEMMA ClusterAgreeReplicasAndMessagesPreserveEntries ==
    /\ messages \subseteq messages'
    /\ \A entry \in ClusterAgreeEntries:
           ClusterReplicated(entry.index, entry.term)
               \subseteq ClusterReplicated(entry.index, entry.term)'
    => StableClusterAgreeEntriesInv
<1> SUFFICES ASSUME messages \subseteq messages',
                    \A entry \in ClusterAgreeEntries:
                        ClusterReplicated(entry.index, entry.term)
                            \subseteq ClusterReplicated(entry.index, entry.term)',
                    NEW entry \in ClusterAgreeEntries
             PROVE entry \in ClusterAgreeEntries'
    BY DEF StableClusterAgreeEntriesInv
<1>won. \A server, term: Won(server, term) => Won(server, term)'
    BY DEF Won, Started, VoteFor, Grant
<1>agree. ClusterAgree(entry.index, entry.term)
              \subseteq ClusterAgree(entry.index, entry.term)'
    BY <1>won DEF ClusterAgree
<1>entries. entry \in ClusterEntries'
    BY DEF ClusterAgreeEntries, ClusterEntries, ClusterReplicated
<1>quorum. ClusterAgree(entry.index, entry.term)' \in Quorum
    BY <1>agree, QuorumSuperset
    DEF ClusterAgreeEntries, ClusterAgree, ClusterReplicated
<1> QED BY <1>entries, <1>quorum DEF ClusterAgreeEntries

LEMMA ClusterAgreeAppendInvSufficesForStability ==
    \A m \in messages:
        /\ InductiveInvariant /\ ClusterAgreeAppendInv
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
    BY CompatibleAppendPreservesClusterReplicas,
       ClusterAgreeReplicasAndMessagesPreserveEntries
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages

LEMMA ClusterAgreeSupportInvSufficesForNext ==
    InductiveInvariant /\ ClusterAgreeSupportInv /\ [Next]_vars
    => StableClusterAgreeEntriesInv
<1>append. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>append, ClusterAgreeAppendInvSufficesForStability DEF ClusterAgreeSupportInv
<1>client. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    BY <1>client, ClientRequestPreservesClusterAgreeEntries
<1>unchanged. CASE UNCHANGED log
    BY <1>unchanged, MessagesMonotonicNext, UnchangedLogPreservesClusterAgreeEntries
<1> QED BY <1>append, <1>client, <1>unchanged, LogChangingActionNext

LEMMA HandleAppendEntriesRequestPreservesClusterAgreeEntries ==
    \A m \in messages:
        /\ InductiveInvariant /\ ClusterAgreeSupportInv
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
<1> SUFFICES ASSUME NEW m \in messages, InductiveInvariant, ClusterAgreeSupportInv,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(m.mdest, m.msource, m)
             PROVE StableClusterAgreeEntriesInv
    OBVIOUS
<1>unchanged. CASE UNCHANGED log
    BY <1>unchanged, UnchangedLogPreservesClusterAgreeEntries
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>changed. CASE log' # log
    <2>types. /\ TypeOK /\ m.mdest \in Server /\ m.msource \in Server
                /\ log \in [Server -> Seq(LogEntry)]
                /\ log' \in [Server -> Seq(LogEntry)]
        BY MessageFieldsTypeOK, HandleAppendEntriesRequestLogVarsTypeOK
        DEF InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
    <2>shape. /\ m.mprevLogIndex \in 0..Len(log[m.mdest])
                /\ Len(log'[m.mdest]) = m.mprevLogIndex + 1
        BY <1>changed, <2>types, AppendRequestChangedLogShape
    <2>append. CASE m.mprevLogIndex = Len(log[m.mdest])
        <3>retain. \A server \in Server: \A index \in DOMAIN log[server]:
                /\ index \in DOMAIN log'[server]
                /\ log'[server][index].term = log[server][index].term
            <4> SUFFICES ASSUME NEW server \in Server,
                                NEW index \in DOMAIN log[server]
                         PROVE /\ index \in DOMAIN log'[server]
                               /\ log'[server][index].term = log[server][index].term
                OBVIOUS
            <4>other. CASE server # m.mdest
                BY <4>other, <2>types DEF HandleAppendEntriesRequest
            <4>same. CASE server = m.mdest
                <5>domain. /\ index \in 1..m.mprevLogIndex
                             /\ index \in DOMAIN log'[server]
                    BY <4>same, <2>append, <2>types, <2>shape, LenProperties
                <5> QED BY <4>same, <2>append, <2>types, <5>domain,
                    AppendRequestRetainsMatchedPrefix
            <4> QED BY <4>other, <4>same
        <3> QED BY <3>retain, ReplicationAndMessagesGrowClusterAgreeEntries
            DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
    <2>truncate. CASE m.mprevLogIndex < Len(log[m.mdest])
        BY ClusterAgreeAppendInvSufficesForStability DEF ClusterAgreeSupportInv
    <2> QED BY <2>shape, <2>append, <2>truncate
<1> QED BY <1>unchanged, <1>changed

LEMMA HandleAppendEntriesResponsePreservesClusterAgreeEntries ==
    \A m \in messages:
        /\ InductiveInvariant /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
        => StableClusterAgreeEntriesInv
    BY UnchangedLogPreservesClusterAgreeEntries DEF HandleAppendEntriesResponse

LEMMA NextGrowsClusterAgree ==
    InductiveInvariant /\ ClusterAgreeSupportInv /\ Next => StableClusterAgreeEntriesInv
<1>restart. CASE \E i \in Server: Restart(i)
    BY <1>restart, RestartPreservesClusterAgreeEntries
<1>timeout. CASE \E i \in Server: Timeout(i)
    BY <1>timeout, TimeoutPreservesClusterAgreeEntries
<1>leader. CASE \E i \in Server: BecomeLeader(i)
    BY <1>leader, BecomeLeaderPreservesClusterAgreeEntries
<1>client. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    BY <1>client, ClientRequestPreservesClusterAgreeEntries
<1>commit. CASE \E i \in Server: AdvanceCommitIndex(i)
    BY <1>commit, AdvanceCommitIndexPreservesClusterAgreeEntries
<1>send. CASE \E i, j \in Server: AppendEntries(i, j)
    BY <1>send, AppendEntriesPreservesClusterAgreeEntries
<1>stepdown. CASE \E i \in Server: LeaderStepDown(i)
    BY <1>stepdown, LeaderStepDownPreservesClusterAgreeEntries
<1>update. CASE \E m \in messages: UpdateTerm(m.mdest, m.msource, m)
    BY <1>update, UpdateTermPreservesClusterAgreeEntries
<1>voteRequest. CASE \E m \in messages:
        /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
    BY <1>voteRequest, HandleRequestVoteRequestPreservesClusterAgreeEntries
<1>voteResponse. CASE \E m \in messages:
        /\ m.mtype = RequestVoteResponse
        /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
    BY <1>voteResponse, HandleRequestVoteResponsePreservesClusterAgreeEntries
<1>appendRequest. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>appendRequest, HandleAppendEntriesRequestPreservesClusterAgreeEntries
<1>appendResponse. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
    BY <1>appendResponse, HandleAppendEntriesResponsePreservesClusterAgreeEntries
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client, <1>commit,
    <1>send, <1>stepdown, <1>update, <1>voteRequest, <1>voteResponse,
    <1>appendRequest, <1>appendResponse
    DEF Next, Receive, HandleMsg

LEMMA AppendRequestSenderWonInit == Init => AppendRequestSenderWonInv
    BY DEF Init, AppendRequestSenderWonInv, AppendRequests

LEMMA AppendRequestSenderWonNext ==
    /\ InductiveInvariant /\ AppendRequestSenderWonInv /\ [Next]_vars
    => AppendRequestSenderWonInv'
<1> SUFFICES ASSUME InductiveInvariant, AppendRequestSenderWonInv, [Next]_vars,
                    NEW request \in AppendRequests'
             PROVE Won(request.msource, request.mterm)'
    BY DEF AppendRequestSenderWonInv
<1>old. CASE request \in messages
    BY <1>old, WonMonotonicNext DEF AppendRequestSenderWonInv, AppendRequests
<1>new. CASE request \notin messages
    <2> PICK sender, recipient \in Server:
            /\ AppendEntries(sender, recipient)
            /\ request = AppendEntriesMessage(sender, recipient)
        BY <1>new, NewAppendRequestOrigin DEF AppendRequests
    <2>won. Won(sender, currentTerm[sender])
        BY ActiveLeaderWon DEF AppendEntries
    <2> QED BY <2>won, WonMonotonicNext DEF AppendEntriesMessage
<1> QED BY <1>old, <1>new

LEMMA SuccessfulResponseRecipientWonInit == Init => SuccessfulResponseRecipientWonInv
    BY DEF Init, SuccessfulResponseRecipientWonInv

LEMMA NewSuccessfulAppendResponseOrigin ==
    /\ InductiveInvariant /\ [Next]_vars
    => \A response \in messages' \ messages:
           response.mtype = AppendEntriesResponse /\ response.msuccess =>
               \E request \in AppendRequests:
                   /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
                   /\ response.mdest = request.msource
                   /\ response.mterm = request.mterm
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    NEW response \in messages' \ messages,
                    response.mtype = AppendEntriesResponse, response.msuccess
             PROVE \E request \in AppendRequests:
                   /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
                   /\ response.mdest = request.msource
                   /\ response.mterm = request.mterm
    OBVIOUS
<1>receive. CASE \E request \in messages: Receive(request)
    BY <1>receive, MessageFieldsTypeOK, MessageTypesDistinct
    DEF InductiveInvariant, TypeOK, MsgTypeOK, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        AppendRequests, Send, WithMessage, WithMessages
<1>other. CASE ~(\E request \in messages: Receive(request))
    BY <1>other, MessageTypesDistinct
    DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, AppendEntriesMessage, LeaderStepDown,
        Send, WithMessage, WithMessages, RequestVoteRequests
<1> QED BY <1>receive, <1>other

LEMMA SuccessfulResponseRecipientWonNext ==
    /\ InductiveInvariant /\ AppendRequestSenderWonInv
    /\ SuccessfulResponseRecipientWonInv /\ [Next]_vars
    => SuccessfulResponseRecipientWonInv'
<1> SUFFICES ASSUME InductiveInvariant, AppendRequestSenderWonInv,
                    SuccessfulResponseRecipientWonInv, [Next]_vars,
                    NEW response \in messages',
                    response.mtype = AppendEntriesResponse, response.msuccess
             PROVE Won(response.mdest, response.mterm)'
    BY DEF SuccessfulResponseRecipientWonInv
<1>old. CASE response \in messages
    BY <1>old, WonMonotonicNext DEF SuccessfulResponseRecipientWonInv
<1>new. CASE response \notin messages
    <2> PICK request \in AppendRequests:
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
            /\ response.mdest = request.msource
            /\ response.mterm = request.mterm
        BY <1>new, NewSuccessfulAppendResponseOrigin
    <2> QED BY WonMonotonicNext DEF AppendRequestSenderWonInv
<1> QED BY <1>old, <1>new

LEMMA UncreatedEntryHasNoHigherTermEvidence ==
    \A leader, server \in Server: \A index \in Nat:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ state[leader] = Leader /\ Len(log[leader]) < index
        /\ currentTerm[leader] < currentTerm[server]
        => ~EntryAgreementEvidence(server, index, currentTerm[leader])
<1> SUFFICES ASSUME NEW leader \in Server, NEW server \in Server,
                    NEW index \in Nat, InductiveInvariant,
                    SuccessfulResponseRecipientWonInv, state[leader] = Leader,
                    Len(log[leader]) < index,
                    currentTerm[leader] < currentTerm[server],
                    EntryAgreementEvidence(server, index, currentTerm[leader])
             PROVE FALSE
    OBVIOUS
<1>types. /\ currentTerm[leader] \in Nat /\ currentTerm[server] \in Nat
            /\ Len(log[leader]) \in Nat
    BY LenProperties DEF InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>leaderWon. Won(leader, currentTerm[leader]) BY ActiveLeaderWon
<1>owner. CASE Won(server, currentTerm[leader])
    <2>same. server = leader
        BY <1>owner, <1>leaderWon, <1>types, WonUnique DEF InductiveInvariant
    <2> QED BY <2>same, SMT
<1>ack. CASE ~Won(server, currentTerm[leader])
    <2> PICK response \in messages:
            /\ response.mtype = AppendEntriesResponse /\ response.msuccess
            /\ response.msource = server /\ response.mterm = currentTerm[leader]
            /\ response.mmatchIndex = index
        BY <1>ack DEF EntryAgreementEvidence
    <2>recipientWon. Won(response.mdest, currentTerm[leader])
        BY DEF SuccessfulResponseRecipientWonInv
    <2>recipient. response.mdest = leader
        BY <2>recipientWon, <1>leaderWon, <1>types, MessageFieldsTypeOK, WonUnique
        DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>bound. index <= Len(log[leader])
        BY <2>recipient DEF InductiveInvariant, ResponseIndexBound
    <2> QED BY <2>bound, <1>types, SMT
<1> QED BY <1>owner, <1>ack

LEMMA HistoricalHigherElectionExcludesUncreatedEntry ==
    \A leader, candidate \in Server: \A term, index \in Nat:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ state[leader] = Leader /\ Won(candidate, term)
        /\ term <= currentTerm[candidate] /\ currentTerm[leader] < term
        /\ Len(log[leader]) < index
        => ClusterMightAgree(index, currentTerm[leader]) \notin Quorum
<1> SUFFICES ASSUME NEW leader \in Server, NEW candidate \in Server,
                    NEW term \in Nat, NEW index \in Nat, InductiveInvariant,
                    SuccessfulResponseRecipientWonInv, state[leader] = Leader,
                    Won(candidate, term), term <= currentTerm[candidate],
                    currentTerm[leader] < term, Len(log[leader]) < index,
                    ClusterMightAgree(index, currentTerm[leader]) \in Quorum
             PROVE FALSE
    OBVIOUS
<1>leaderWon. Won(leader, currentTerm[leader]) BY ActiveLeaderWon
<1> PICK quorum \in Quorum: \A voter \in quorum: VoteFor(voter, candidate, term)
    BY DEF Won
<1>intersection. quorum \cap ClusterMightAgree(index, currentTerm[leader]) # {}
    BY QuorumsIntersect
<1> PICK voter \in quorum \cap ClusterMightAgree(index, currentTerm[leader]): TRUE
    BY <1>intersection
<1>types. /\ voter \in Server /\ currentTerm[voter] \in Nat
            /\ currentTerm[leader] \in Nat /\ Len(log[leader]) \in Nat
    BY LenProperties
    DEF ClusterMightAgree, InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>higher. term <= currentTerm[voter]
    BY <1>types, GrantTermBoundFromSendInvariant, SMT DEF VoteFor, GrantTermBoundInv
<1>evidence. EntryAgreementEvidence(voter, index, currentTerm[leader])
    BY <1>higher, <1>types, SMT DEF ClusterMightAgree
<1>owner. CASE Won(voter, currentTerm[leader])
    <2>same. voter = leader
        BY <1>owner, <1>leaderWon, <1>types, WonUnique DEF InductiveInvariant
    <2> QED BY <2>same, <1>higher, <1>types, SMT
<1>ack. CASE ~Won(voter, currentTerm[leader])
    <2> PICK response \in messages:
            /\ response.mtype = AppendEntriesResponse /\ response.msuccess
            /\ response.msource = voter /\ response.mterm = currentTerm[leader]
            /\ response.mmatchIndex = index
        BY <1>evidence, <1>ack DEF EntryAgreementEvidence
    <2>recipientWon. Won(response.mdest, currentTerm[leader])
        BY DEF SuccessfulResponseRecipientWonInv
    <2>recipient. response.mdest = leader
        BY <2>recipientWon, <1>leaderWon, <1>types, MessageFieldsTypeOK, WonUnique
        DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>bound. index <= Len(log[leader])
        BY <2>recipient DEF InductiveInvariant, ResponseIndexBound
    <2> QED BY <2>bound, <1>types, SMT
<1> QED BY <1>owner, <1>ack

LEMMA HigherElectionExcludesUncreatedEntry ==
    \A leader, candidate \in Server: \A index \in Nat:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ state[leader] = Leader
        /\ Won(candidate, currentTerm[candidate])
        /\ currentTerm[leader] < currentTerm[candidate]
        /\ Len(log[leader]) < index
        => ClusterMightAgree(index, currentTerm[leader]) \notin Quorum
<1> SUFFICES ASSUME NEW leader \in Server, NEW candidate \in Server,
                    NEW index \in Nat, InductiveInvariant,
                    SuccessfulResponseRecipientWonInv, state[leader] = Leader,
                    Won(candidate, currentTerm[candidate]),
                    currentTerm[leader] < currentTerm[candidate],
                    Len(log[leader]) < index,
                    ClusterMightAgree(index, currentTerm[leader]) \in Quorum
             PROVE FALSE
    OBVIOUS
<1>leaderWon. Won(leader, currentTerm[leader]) BY ActiveLeaderWon
<1> PICK quorum \in Quorum:
        \A voter \in quorum: VoteFor(voter, candidate, currentTerm[candidate])
    BY DEF Won
<1>intersection.
        quorum \cap ClusterMightAgree(index, currentTerm[leader]) # {}
    BY QuorumsIntersect
<1> PICK voter \in quorum \cap ClusterMightAgree(index, currentTerm[leader]): TRUE
    BY <1>intersection
<1>types. /\ voter \in Server /\ currentTerm[voter] \in Nat
            /\ currentTerm[leader] \in Nat /\ currentTerm[candidate] \in Nat
    BY DEF ClusterMightAgree, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>higher. currentTerm[candidate] <= currentTerm[voter]
    BY HigherElectionVotersHaveHigherTerms
<1>evidence. EntryAgreementEvidence(voter, index, currentTerm[leader])
    BY <1>higher, <1>types, SMT DEF ClusterMightAgree
<1>owner. CASE Won(voter, currentTerm[leader])
    <2>same. voter = leader
        BY <1>owner, <1>leaderWon, <1>types, WonUnique
        DEF InductiveInvariant
    <2> QED BY <2>same, <1>higher, <1>types, SMT
<1>ack. CASE ~Won(voter, currentTerm[leader])
    <2> PICK response \in messages:
            /\ response.mtype = AppendEntriesResponse /\ response.msuccess
            /\ response.msource = voter /\ response.mterm = currentTerm[leader]
            /\ response.mmatchIndex = index
        BY <1>evidence, <1>ack DEF EntryAgreementEvidence
    <2>recipientWon. Won(response.mdest, currentTerm[leader])
        BY DEF SuccessfulResponseRecipientWonInv
    <2>recipient. response.mdest = leader
        BY <2>recipientWon, <1>leaderWon, <1>types,
            MessageFieldsTypeOK, WonUnique
        DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>bound. index <= Len(log[leader])
        BY <2>recipient
        DEF InductiveInvariant, ResponseIndexBound
    <2>length. Len(log[leader]) \in Nat
        BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK
    <2> QED BY <2>bound, <2>length, SMT
<1> QED BY <1>owner, <1>ack

LEMMA FutureTermEntryCannotBeInLog ==
    \A server \in Server: \A entry \in HistoricalEntryKeys:
        /\ InductiveInvariant /\ currentTerm[server] < entry.term
        => ~(/\ entry.index \in DOMAIN log[server]
             /\ log[server][entry.index].term = entry.term)
    BY ElementOfSeq, SMT
    DEF InductiveInvariant, LogTermBoundInv, TypeOK, ServerVarsTypeOK,
        LogVarsTypeOK, LogEntry

LEMMA ClusterAgreeEntriesAreCandidateEntries ==
    ClusterAgreeEntries \subseteq ClusterAgreeCandidateEntries
    BY QuorumSuperset
    DEF ClusterAgreeEntries, ClusterEntries, ClusterAgreeCandidateEntries,
        HistoricalEntryKeys, HistoricalEntryEdges, ClusterMightAgree,
        ClusterAgree, ClusterReplicated, EntryAgreementEvidence, LogEntryEdge

LEMMA ClusterAgreeEntriesAreCandidateEntriesNext ==
    ClusterAgreeEntries' \subseteq ClusterAgreeCandidateEntries'
    BY QuorumSuperset
    DEF ClusterAgreeEntries, ClusterEntries, ClusterAgreeCandidateEntries,
        HistoricalEntryKeys, HistoricalEntryEdges, ClusterMightAgree,
        ClusterAgree, ClusterReplicated, EntryAgreementEvidence, LogEntryEdge

LEMMA HistoricalEntryEdgeHasTermOwner ==
    InductiveInvariant => \A edge \in HistoricalEntryEdges:
        /\ edge.index \in Nat /\ edge.term \in Nat
        /\ \E owner \in Server: TermOwner(owner, edge.term, edge.index)
<1> SUFFICES ASSUME InductiveInvariant, NEW edge \in HistoricalEntryEdges
             PROVE /\ edge.index \in Nat /\ edge.term \in Nat
                   /\ \E owner \in Server: TermOwner(owner, edge.term, edge.index)
    OBVIOUS
<1>log. CASE \E server \in Server: \E index \in DOMAIN log[server]:
        edge = LogEntryEdge(log[server], index)
    BY <1>log, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LogEntry,
        LogEntryEdge, LogElectionInv
<1>request. CASE \E request \in AppendRequests: \E index \in DOMAIN request.mentries:
        edge = RequestEntryEdge(request, index)
    BY <1>request, MessageFieldsTypeOK, LenProperties, SMT
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogEntry, AppendRequests,
        RequestEntryEdge, MessageElectionInv
<1> QED BY <1>log, <1>request DEF HistoricalEntryEdges

LEMMA HistoricalEntryKeyHasWinner ==
    InductiveInvariant => \A entry \in HistoricalEntryKeys:
        /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
        /\ \E owner \in Server: TermOwner(owner, entry.term, entry.index)
<1> SUFFICES ASSUME InductiveInvariant, NEW entry \in HistoricalEntryKeys
             PROVE /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
                   /\ \E owner \in Server: TermOwner(owner, entry.term, entry.index)
    BY DEF HistoricalEntryKeys
<1> PICK edge \in HistoricalEntryEdges:
        entry = [index |-> edge.index, term |-> edge.term]
    BY DEF HistoricalEntryKeys
<1>positive. edge.index > 0
    BY LenProperties, MessageFieldsTypeOK, SMT
    DEF HistoricalEntryEdges, LogEntryEdge, RequestEntryEdge, AppendRequests,
        InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY <1>positive, HistoricalEntryEdgeHasTermOwner, SMT

LEMMA PositiveVoteRequestOriginInit == Init => PositiveVoteRequestOriginInv
    BY DEF Init, PositiveVoteRequestOriginInv

LEMMA PositiveVoteRequestOriginNext ==
    /\ InductiveInvariant /\ PositiveVoteRequestOriginInv /\ [Next]_vars
    => PositiveVoteRequestOriginInv'
<1> SUFFICES ASSUME InductiveInvariant, PositiveVoteRequestOriginInv, [Next]_vars,
                    NEW response \in messages',
                    response.mtype = RequestVoteResponse, response.mvoteGranted
             PROVE \E request \in messages':
                       /\ request.mtype = RequestVoteRequest
                       /\ request.msource = response.mdest
                       /\ request.mdest = response.msource
                       /\ request.mterm = response.mterm
    BY DEF PositiveVoteRequestOriginInv
<1>old. CASE response \in messages
    BY <1>old, MessagesMonotonicNext DEF PositiveVoteRequestOriginInv
<1>new. CASE response \notin messages
    <2>receive. CASE \E request \in messages: Receive(request)
        <3> PICK request \in messages: Receive(request) BY <2>receive
        <3>vote. CASE request.mtype = RequestVoteRequest
            <4>fields. /\ response.mdest = request.msource
                          /\ response.msource = request.mdest
                          /\ response.mterm = request.mterm
                BY <3>vote, <1>new, MessageFieldsTypeOK, MessageTypesDistinct
                DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                    Send, WithMessage, WithMessages, InductiveInvariant, TypeOK, MsgTypeOK
            <4>present. request \in messages' BY MessagesMonotonicNext
            <4> QED BY <4>fields, <4>present, <3>vote
        <3>voteResponse. CASE request.mtype = RequestVoteResponse
            BY <3>voteResponse, <1>new, MessageFieldsTypeOK, MessageTypesDistinct, SMT
            DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteResponse,
                Send, WithMessage, WithMessages, InductiveInvariant, TypeOK, MsgTypeOK
        <3>append. CASE request.mtype = AppendEntriesRequest
            BY <3>append, <1>new, MessageFieldsTypeOK, MessageTypesDistinct, SMT
            DEF Receive, UpdateTerm, HandleMsg, HandleAppendEntriesRequest,
                Send, WithMessage, WithMessages, InductiveInvariant, TypeOK, MsgTypeOK
        <3>appendResponse. CASE request.mtype = AppendEntriesResponse
            BY <3>appendResponse, <1>new, MessageFieldsTypeOK, MessageTypesDistinct, SMT
            DEF Receive, UpdateTerm, HandleMsg, HandleAppendEntriesResponse,
                Send, WithMessage, WithMessages, InductiveInvariant, TypeOK, MsgTypeOK
        <3> QED BY <3>vote, <3>voteResponse, <3>append, <3>appendResponse
            DEF InductiveInvariant, TypeOK, MsgTypeOK, Message,
                RequestVoteRequestMessage, RequestVoteResponseMessage,
                AppendEntriesRequestMessage, AppendEntriesResponseMessage
    <2>other. CASE ~(\E request \in messages: Receive(request))
        BY <2>other, <1>new, MessageTypesDistinct
        DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
            AdvanceCommitIndex, AppendEntries, AppendEntriesMessage, LeaderStepDown,
            Send, WithMessage, WithMessages, RequestVoteRequests
    <2> QED BY <2>receive, <2>other
<1> QED BY <1>old, <1>new

LEMMA CandidateSnapshotInit == Init => CandidateRequestSnapshotInv
    BY ServerStatesDistinct DEF Init, InitServerVars, CandidateRequestSnapshotInv

LEMMA CandidateSnapshotNext ==
    /\ InductiveInvariant /\ CandidateRequestSnapshotInv /\ [Next]_vars
    => CandidateRequestSnapshotInv'
<1> SUFFICES ASSUME InductiveInvariant, CandidateRequestSnapshotInv, [Next]_vars,
                    NEW candidate \in Server, NEW request \in messages',
                    state'[candidate] = Candidate,
                    request.mtype = RequestVoteRequest,
                    request.msource = candidate,
                    request.mterm = currentTerm'[candidate]
             PROVE /\ request.mlastLogTerm = LastTerm(log'[candidate])
                   /\ request.mlastLogIndex = Len(log'[candidate])
    BY DEF CandidateRequestSnapshotInv
<1>types. /\ currentTerm \in [Server -> Nat] /\ log \in [Server -> Seq(LogEntry)]
            /\ state \in [Server -> {Follower, Candidate, Leader}]
    BY DEF InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>timeout. CASE \E server \in Server: Timeout(server)
    <2> PICK server \in Server: Timeout(server) BY <1>timeout
    <2>same. CASE server = candidate
        <3>old. request \notin messages
            BY <2>same, <1>types, MessageFieldsTypeOK, SMT
            DEF Timeout, InductiveInvariant, TypeOK, MsgTypeOK, SendInvariant
        <3> QED BY <3>old, <2>same, MessageTypesDistinct, SMT
            DEF Timeout, RequestVoteRequests, WithMessages
    <2>other. CASE server # candidate
        BY <2>other, <1>types, MessageTypesDistinct, SMT
        DEF Timeout, CandidateRequestSnapshotInv, RequestVoteRequests, WithMessages
    <2> QED BY <2>same, <2>other
<1>client. CASE \E server \in Server, value \in Value: ClientRequest(server, value)
    BY <1>client, <1>types, ServerStatesDistinct, SMT
    DEF ClientRequest, CandidateRequestSnapshotInv
<1>append. CASE \E m \in messages:
        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    <2> PICK m \in messages:
        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        BY <1>append
    <2>same. CASE m.mdest = candidate
        BY <2>same, <1>types, ServerStatesDistinct, MessageTypesDistinct
        DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
            CandidateRequestSnapshotInv
    <2>other. CASE m.mdest # candidate
        BY <2>other, <1>types, MessageTypesDistinct
        DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
            CandidateRequestSnapshotInv
    <2> QED BY <2>same, <2>other
<1>other. CASE /\ ~(\E server \in Server: Timeout(server))
                 /\ ~(\E server \in Server, value \in Value: ClientRequest(server, value))
                 /\ ~(\E m \in messages:
                        m.mtype = AppendEntriesRequest /\
                        HandleAppendEntriesRequest(m.mdest, m.msource, m))
    BY <1>other, <1>types, MessageFieldsTypeOK, ServerStatesDistinct, MessageTypesDistinct
    DEF CandidateRequestSnapshotInv, Next, vars, Restart, BecomeLeader,
        AdvanceCommitIndex, AppendEntries, AppendEntriesMessage, LeaderStepDown,
        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages
<1> QED BY <1>timeout, <1>client, <1>append, <1>other

LEMMA VoteRequestsUniformInit == Init => VoteRequestsUniformInv
    BY DEF Init, VoteRequestsUniformInv

LEMMA VoteRequestsUniformNext ==
    /\ InductiveInvariant /\ VoteRequestsUniformInv /\ [Next]_vars
    => VoteRequestsUniformInv'
<1> SUFFICES ASSUME InductiveInvariant, VoteRequestsUniformInv, [Next]_vars
             PROVE VoteRequestsUniformInv'
    OBVIOUS
<1>timeout. CASE \E server \in Server: Timeout(server)
    <2> PICK server \in Server: Timeout(server) BY <1>timeout
    <2> QED BY MessageFieldsTypeOK, MessageTypesDistinct, SMTT(30)
        DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK, SendInvariant,
            VoteRequestsUniformInv, Timeout, RequestVoteRequests, WithMessages
<1>other. CASE ~(\E server \in Server: Timeout(server))
    <2>requestSubset.
        {request \in messages': request.mtype = RequestVoteRequest}
            \subseteq {request \in messages: request.mtype = RequestVoteRequest}
        <3>receive. CASE \E m \in messages: Receive(m)
            <4> PICK m \in messages: Receive(m) BY <3>receive
            <4> QED BY MessageTypesDistinct, SMTT(30)
                DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                    HandleRequestVoteResponse, HandleAppendEntriesRequest,
                    HandleAppendEntriesResponse, Send, WithMessage, WithMessages
        <3>other. CASE ~(\E m \in messages: Receive(m))
            <4>append. CASE \E leader, recipient \in Server: AppendEntries(leader, recipient)
                BY <4>append, MessageTypesDistinct
                DEF AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages
            <4>other. CASE ~(\E leader, recipient \in Server: AppendEntries(leader, recipient))
                <5>frame. messages' = messages
                    BY <3>other, <1>other, <4>other
                    DEF Next, vars, Timeout,
                        Restart, BecomeLeader, ClientRequest, AdvanceCommitIndex, LeaderStepDown
                <5> QED BY <5>frame
            <4> QED BY <4>append, <4>other
        <3> QED BY <3>receive, <3>other
    <2> QED BY <2>requestSubset DEF VoteRequestsUniformInv
<1> QED BY <1>timeout, <1>other

LEMMA NewSuccessfulAppendResponseSourceTerm ==
    InductiveInvariant /\ [Next]_vars =>
        \A response \in messages' \ messages:
            response.mtype = AppendEntriesResponse /\ response.msuccess =>
                currentTerm[response.msource] = response.mterm
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    NEW response \in messages' \ messages,
                    response.mtype = AppendEntriesResponse, response.msuccess
             PROVE currentTerm[response.msource] = response.mterm
    OBVIOUS
<1> PICK request \in AppendRequests:
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        /\ response.mdest = request.msource /\ response.mterm = request.mterm
    BY NewSuccessfulAppendResponseOrigin
<1> QED BY MessageFieldsTypeOK, MessageTypesDistinct, SMTT(30)
    DEF AppendRequests, InductiveInvariant, TypeOK, MsgTypeOK,
        HandleAppendEntriesRequest, Send, WithMessage, WithMessages

LEMMA NewSuccessfulAppendResponseLogAnchor ==
    InductiveInvariant /\ RequestAcknowledgmentAnchorInv /\ [Next]_vars =>
        \A response \in messages' \ messages: \A entry \in HistoricalEntryKeys:
            /\ response.mtype = AppendEntriesResponse /\ response.msuccess
            /\ response.mterm = entry.term /\ response.mmatchIndex = entry.index
            => LogHasTermAt(response.msource, entry.term, entry.index)'
<1> SUFFICES ASSUME InductiveInvariant, RequestAcknowledgmentAnchorInv, [Next]_vars,
                    NEW response \in messages' \ messages,
                    NEW entry \in HistoricalEntryKeys,
                    response.mtype = AppendEntriesResponse, response.msuccess,
                    response.mterm = entry.term, response.mmatchIndex = entry.index
             PROVE LogHasTermAt(response.msource, entry.term, entry.index)'
    OBVIOUS
<1> PICK request \in AppendRequests:
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        /\ response.mdest = request.msource /\ response.mterm = request.mterm
    BY NewSuccessfulAppendResponseOrigin
<1>types. /\ request.mdest \in Server /\ request.msource \in Server
           /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
           /\ Len(request.mentries) \in Nat /\ Len(request.mentries) <= 1
           /\ log \in [Server -> Seq(LogEntry)]
           /\ currentTerm \in [Server -> Nat]
           /\ Len(log[request.mdest]) \in Nat
           /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
    BY MessageFieldsTypeOK, LenProperties, HistoricalEntryKeyHasWinner
    DEF AppendRequests, InductiveInvariant, TypeOK, MsgTypeOK,
        LogVarsTypeOK, ServerVarsTypeOK, RequestCommitIndexBound
<1>sent. response = [mtype |-> AppendEntriesResponse,
                     mterm |-> currentTerm[request.mdest],
                     msuccess |-> TRUE,
                     mmatchIndex |-> request.mprevLogIndex + Len(request.mentries),
                     msource |-> request.mdest, mdest |-> request.msource]
    BY <1>types
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>accepted. /\ request.mterm = currentTerm[request.mdest]
              /\ state[request.mdest] # Leader
              /\ request.mprevLogIndex \in 0..Len(log[request.mdest])
              /\ (request.mprevLogIndex > 0 =>
                    log[request.mdest][request.mprevLogIndex].term = request.mprevLogTerm)
    BY <1>types, SMT
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>endpoint. /\ response.msource = request.mdest
              /\ entry.term = request.mterm
              /\ entry.index = request.mprevLogIndex + Len(request.mentries)
    BY <1>sent
<1>anchor. IF request.mentries = << >>
           THEN request.mprevLogTerm = entry.term
           ELSE request.mentries[1].term = entry.term
    BY <1>endpoint DEF RequestAcknowledgmentAnchorInv
<1>empty. CASE request.mentries = << >>
    <2>index. entry.index = request.mprevLogIndex
        BY <1>types, <1>endpoint, <1>empty, EmptySeq, SMT
    <2>positive. request.mprevLogIndex > 0
        BY <1>types, <2>index, SMT
    <2>range. entry.index \in 1..Len(log[request.mdest])
        BY <1>types, <1>accepted, <2>index, <2>positive, SMT
    <2>previous. log[request.mdest][request.mprevLogIndex].term = request.mprevLogTerm
        BY <1>accepted, <2>positive
    <2>term. log[request.mdest][entry.index].term = entry.term
        BY <1>anchor, <1>empty, <2>index, <2>previous
    <2>unchanged. log' = log BY <1>empty DEF HandleAppendEntriesRequest
    <2> QED BY <1>types, <1>endpoint, <2>range, <2>term, <2>unchanged, LenProperties
        DEF LogHasTermAt
<1>nonempty. CASE request.mentries # << >>
    <2>payload. /\ Len(request.mentries) = 1
                  /\ 1 \in DOMAIN request.mentries
                  /\ request.mentries[1] \in LogEntry
                  /\ entry.index = request.mprevLogIndex + 1
                  /\ request.mentries[1].term = entry.term
        BY <1>types, <1>endpoint, <1>anchor, <1>nonempty,
            EmptySeq, LenProperties, ElementOfSeq, SMT
    <2>replace. CASE \/ Len(log[request.mdest]) = request.mprevLogIndex
                        \/ log[request.mdest][request.mprevLogIndex + 1].term
                              # request.mentries[1].term
        <3>shape. log'[request.mdest] =
                Append(SubSeq(log[request.mdest], 1, request.mprevLogIndex),
                       request.mentries[1])
            BY <1>types, <1>accepted, <1>nonempty, <2>replace
            DEF HandleAppendEntriesRequest
        <3>cut. /\ request.mprevLogIndex \in Nat
                 /\ request.mprevLogIndex <= Len(log[request.mdest])
            BY <1>types, <1>accepted, SMT
        <3>prefixType. SubSeq(log[request.mdest], 1, request.mprevLogIndex) \in Seq(LogEntry)
            BY <1>types, <3>cut, SubSeqTypeOK
        <3>prefixLength. Len(SubSeq(log[request.mdest], 1, request.mprevLogIndex))
                = request.mprevLogIndex
            BY <1>types, <3>cut, SubSeqProperties, 1 \in Int, Nat \subseteq Int
        <3>length. Len(log'[request.mdest]) = request.mprevLogIndex + 1
            BY <2>payload, <3>shape, <3>prefixType, <3>prefixLength, AppendProperties
        <3>postType. log'[request.mdest] \in Seq(LogEntry)
            BY <2>payload, <3>shape, <3>prefixType, AppendProperties
        <3>domain. entry.index \in DOMAIN log'[request.mdest]
            BY <1>types, <2>payload, <3>length, <3>postType, LenProperties, SMT
        <3>copy. log'[request.mdest][entry.index] = request.mentries[1]
            BY <2>payload, <3>shape, <3>prefixType, <3>prefixLength, AppendProperties
        <3> QED BY <1>endpoint, <2>payload, <3>domain, <3>copy DEF LogHasTermAt
    <2>matched. CASE ~(\/ Len(log[request.mdest]) = request.mprevLogIndex
                          \/ log[request.mdest][request.mprevLogIndex + 1].term
                                # request.mentries[1].term)
        <3>strict. request.mprevLogIndex < Len(log[request.mdest])
            BY <1>types, <1>accepted, <2>matched, SMT
        <3>range. entry.index \in 1..Len(log[request.mdest])
            BY <1>types, <2>payload, <3>strict, SMT
        <3>same. log[request.mdest][request.mprevLogIndex + 1].term
                = request.mentries[1].term
            BY <2>matched
        <3>term. log[request.mdest][entry.index].term = entry.term
            BY <2>payload, <3>same
        <3>unchanged. log' = log
            BY <1>accepted, <1>nonempty, <2>matched DEF HandleAppendEntriesRequest
        <3> QED BY <1>types, <1>endpoint, <3>range, <3>term, <3>unchanged, LenProperties
            DEF LogHasTermAt
    <2> QED BY <2>replace, <2>matched
<1> QED BY <1>empty, <1>nonempty

LEMMA ExistingKeyPotentialAgreementCannotGrow ==
    InductiveInvariant /\ [Next]_vars =>
        \A entry \in HistoricalEntryKeys:
            ClusterMightAgree(entry.index, entry.term)' \subseteq
                ClusterMightAgree(entry.index, entry.term)
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    NEW entry \in HistoricalEntryKeys,
                    NEW server \in ClusterMightAgree(entry.index, entry.term)'
             PROVE server \in ClusterMightAgree(entry.index, entry.term)
    OBVIOUS
<1>types. /\ server \in Server /\ entry.term \in Nat
            /\ currentTerm[server] \in Nat /\ currentTerm'[server] \in Nat
    BY HistoricalEntryKeyHasWinner, TypeOKNext
    DEF ClusterMightAgree, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>low. CASE currentTerm'[server] <= entry.term
    BY <1>low, <1>types, CurrentTermsMonotonicNext, SMT DEF ClusterMightAgree
<1>old. CASE EntryAgreementEvidence(server, entry.index, entry.term)
    BY <1>old DEF ClusterMightAgree
<1>new. CASE /\ currentTerm'[server] > entry.term
                 /\ ~EntryAgreementEvidence(server, entry.index, entry.term)
    <2>evidence. EntryAgreementEvidence(server, entry.index, entry.term)'
        BY <1>new, <1>types, SMT DEF ClusterMightAgree
    <2>owner. CASE Won(server, entry.term)'
        <3> PICK owner \in Server: TermOwner(owner, entry.term, entry.index)
            BY HistoricalEntryKeyHasWinner
        <3>record. VoteRecordInv' BY VoteRecordInvNext
        <3>won. Won(owner, entry.term)' BY WonMonotonicNext DEF TermOwner
        <3>same. owner = server
            BY <1>types, <3>record, <3>won, WonUniqueNextState, <2>owner
        <3> QED BY <3>same, <1>new DEF TermOwner, EntryAgreementEvidence
    <2>ack. CASE ~Won(server, entry.term)'
        <3> PICK response \in messages' \ messages:
                /\ response.mtype = AppendEntriesResponse /\ response.msuccess
                /\ response.msource = server /\ response.mterm = entry.term
                /\ response.mmatchIndex = entry.index
            BY <2>ack, <2>evidence, <1>new DEF EntryAgreementEvidence
        <3>term. currentTerm[server] = entry.term
            BY NewSuccessfulAppendResponseSourceTerm
        <3> QED BY <3>term, <1>types, SMT DEF ClusterMightAgree
    <2> QED BY <2>owner, <2>ack
<1> QED BY <1>low, <1>old, <1>new, <1>types, SMT

LEMMA ExistingHistoricalKeysCannotBecomeEligible ==
    InductiveInvariant /\ [Next]_vars =>
        ClusterAgreeCandidateEntries' \cap HistoricalEntryKeys
            \subseteq ClusterAgreeCandidateEntries
    BY ExistingKeyPotentialAgreementCannotGrow, QuorumSuperset
    DEF ClusterAgreeCandidateEntries, ClusterMightAgree

LEMMA FreshCandidateEntryOriginNext ==
     ASSUME CandidateEntryBaseInv, [Next]_vars,
                    NEW entry \in ClusterAgreeCandidateEntries' \ HistoricalEntryKeys
             PROVE \E leader \in Server, value \in Value:
                       /\ ClientRequest(leader, value)
                       /\ entry.index = Len(log[leader]) + 1
                       /\ entry.term = currentTerm[leader]
                       /\ entry = [index |-> Len(log[leader]) + 1,
                                    term |-> currentTerm[leader]]
<1>client. \E leader \in Server, value \in Value: ClientRequest(leader, value)
    BY EntryEdgeAppendSendSubset, EntryEdgeAppendReceiveSubset, EntryEdgeOtherSubset
    DEF CandidateEntryBaseInv, ClusterAgreeCandidateEntries, HistoricalEntryKeys
<1> PICK leader \in Server, value \in Value: ClientRequest(leader, value)
    BY <1>client
<1> DEFINE edge == LogEntryEdge(log'[leader], Len(log[leader]) + 1)
<1>key. entry = [index |-> edge.index, term |-> edge.term]
    BY ClientHistoricalEntryEdges
    DEF CandidateEntryBaseInv, ClusterAgreeCandidateEntries, HistoricalEntryKeys, edge
<1>types. /\ log[leader] \in Seq(LogEntry) /\ Len(log[leader]) \in Nat
            /\ currentTerm[leader] \in Nat
    BY LenProperties
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
    BY <1>types DEF LogEntry
<1>clientLog. log'[leader] = Append(log[leader],
        [term |-> currentTerm[leader], value |-> value])
    BY <1>types
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK, ClientRequest
<1>shape. /\ edge.index = Len(log[leader]) + 1 /\ edge.term = currentTerm[leader]
    BY <1>types, <1>newEntry, <1>clientLog, AppendProperties
    DEF edge, LogEntryEdge
<1> QED BY <1>key, <1>shape

LEMMA AppendSenderNotCandidateInit == Init => AppendRequestSenderNotCandidateInv
    BY DEF Init, AppendRequests, AppendRequestSenderNotCandidateInv

LEMMA AppendSenderNotCandidateNext ==
    /\ InductiveInvariant /\ AppendRequestSenderNotCandidateInv /\ [Next]_vars
    => AppendRequestSenderNotCandidateInv'
<1> SUFFICES ASSUME InductiveInvariant, AppendRequestSenderNotCandidateInv, [Next]_vars,
                    NEW request \in AppendRequests',
                    request.mterm = currentTerm'[request.msource]
             PROVE state'[request.msource] # Candidate
    BY DEF AppendRequestSenderNotCandidateInv
<1>new. CASE request \notin messages
    <2> PICK leader, recipient \in Server:
        /\ AppendEntries(leader, recipient) /\ request = AppendEntriesMessage(leader, recipient)
        BY <1>new, NewAppendRequestOrigin DEF AppendRequests
    <2> QED BY ServerStatesDistinct DEF AppendEntries, AppendEntriesMessage
<1>old. CASE request \in messages
    <2>types. /\ request.msource \in Server /\ request.mterm \in Nat
                 /\ currentTerm \in [Server -> Nat]
                 /\ state \in [Server -> {Follower, Candidate, Leader}]
        BY <1>old, MessageFieldsTypeOK
        DEF AppendRequests, InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK
    <2>request. request \in AppendRequests BY <1>old DEF AppendRequests
    <2>bound. request.mterm <= currentTerm[request.msource]
        BY <1>old DEF InductiveInvariant, SendInvariant
    <2>before.
        request.mterm = currentTerm[request.msource] => state[request.msource] # Candidate
        BY <2>request DEF AppendRequestSenderNotCandidateInv
    <2>timeout. CASE \E server \in Server: Timeout(server)
        <3> PICK server \in Server: Timeout(server) BY <2>timeout
        <3>same. CASE server = request.msource
            <4>term. currentTerm'[request.msource] = currentTerm[request.msource] + 1
                BY <3>same, <2>types DEF Timeout
            <4> QED BY <4>term, <2>bound, <2>types, SMT
        <3>other. CASE server # request.msource
            BY <3>other, <2>types, <2>before DEF Timeout
        <3> QED BY <3>same, <3>other
    <2>other. CASE ~(\E server \in Server: Timeout(server))
        <3>receive. CASE \E m \in messages: Receive(m)
            <4> PICK m \in messages: Receive(m) BY <3>receive
            <4> QED BY <2>before, <2>types, MessageFieldsTypeOK, ServerStatesDistinct, SMTT(30)
                DEF InductiveInvariant, TypeOK, MsgTypeOK, Receive, UpdateTerm,
                    HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
                    HandleAppendEntriesRequest, HandleAppendEntriesResponse,
                    AppendRequestSenderNotCandidateInv, AppendRequests
        <3>other. CASE ~(\E m \in messages: Receive(m))
            BY <3>other, <2>other, <2>types, <2>before, ServerStatesDistinct, SMT
            DEF Next, vars, Timeout, Restart, BecomeLeader, ClientRequest,
                AdvanceCommitIndex, AppendEntries, LeaderStepDown
        <3> QED BY <3>receive, <3>other
    <2> QED BY <2>timeout, <2>other
<1> QED BY <1>new, <1>old

LEMMA ActiveAppendSnapshotInit == Init => ActiveAppendRequestSnapshotInv
    BY DEF Init, ActiveAppendRequestSnapshotInv, AppendRequests

LEMMA ActiveAppendSnapshotNext ==
    /\ CandidateEntryBaseInv /\ ActiveAppendRequestSnapshotInv /\ [Next]_vars
    => ActiveAppendRequestSnapshotInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, ActiveAppendRequestSnapshotInv, [Next]_vars,
                    NEW request \in AppendRequests',
                    currentTerm'[request.msource] = request.mterm,
                    state'[request.msource] = Leader
             PROVE /\ request.mprevLogIndex > 0 =>
                          log'[request.msource][request.mprevLogIndex].term = request.mprevLogTerm
                   /\ \A offset \in DOMAIN request.mentries:
                          request.mentries[offset] =
                              log'[request.msource][request.mprevLogIndex + offset]
    BY DEF ActiveAppendRequestSnapshotInv
<1>types. /\ request.msource \in Server /\ request.mterm \in Nat
            /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
            /\ currentTerm \in [Server -> Nat] /\ state \in [Server -> {Follower, Candidate, Leader}]
            /\ log \in [Server -> Seq(LogEntry)]
    BY MessageFieldsTypeOK, TypeOKNext
    DEF CandidateEntryBaseInv, AppendRequests, InductiveInvariant, TypeOK,
        MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>new. CASE request \notin messages
    <2> PICK leader, recipient \in Server:
            /\ AppendEntries(leader, recipient)
            /\ request = AppendEntriesMessage(leader, recipient)
        BY <1>new, NewAppendRequestOrigin DEF CandidateEntryBaseInv, AppendRequests
    <2>frame. log' = log BY DEF AppendEntries
    <2> QED BY <2>frame, AppendEntriesSenderSnapshot
        DEF CandidateEntryBaseInv, AppendEntriesMessage
<1>old. CASE request \in messages
    <2>before. /\ currentTerm[request.msource] = request.mterm
                 /\ state[request.msource] = Leader
        <3>term. currentTerm[request.msource] = request.mterm
            BY <1>old, <1>types, CurrentTermsMonotonicNext, SMT
            DEF CandidateEntryBaseInv, InductiveInvariant, SendInvariant
        <3>notElected. ~BecomeLeader(request.msource)
            BY <1>old, <1>types
            DEF CandidateEntryBaseInv, AppendRequestSenderNotCandidateInv,
                AppendRequests, BecomeLeader
        <3>leader. state[request.msource] = Leader
            <4>receive. CASE \E m \in messages: Receive(m)
                <5> PICK m \in messages: Receive(m) BY <4>receive
                <5> QED BY <3>term, <1>types, ServerStatesDistinct, MessageFieldsTypeOK, SMTT(30)
                    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
                        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                        HandleRequestVoteResponse, HandleAppendEntriesRequest, HandleAppendEntriesResponse
            <4>other. CASE ~(\E m \in messages: Receive(m))
                BY <4>other, <3>notElected, <3>term, <1>types, ServerStatesDistinct, SMT
                DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
                    AdvanceCommitIndex, AppendEntries, LeaderStepDown
            <4> QED BY <4>receive, <4>other
        <3> QED BY <3>term, <3>leader
    <2>snapshot.
        /\ request.mprevLogIndex > 0 =>
               log[request.msource][request.mprevLogIndex].term = request.mprevLogTerm
        /\ \A offset \in DOMAIN request.mentries:
               request.mentries[offset] = log[request.msource][request.mprevLogIndex + offset]
        BY <1>old, <2>before DEF ActiveAppendRequestSnapshotInv, AppendRequests
    <2>client. CASE \E leader \in Server, value \in Value: ClientRequest(leader, value)
        <3> PICK leader \in Server, value \in Value: ClientRequest(leader, value)
            BY <2>client
        <3>same. CASE leader = request.msource
            <4>term. request.mterm = currentTerm[request.msource] BY <2>before
            <4>bound.
                request.mprevLogIndex + Len(request.mentries) <= Len(log[leader])
                BY <1>old, <4>term, <3>same, <2>before
                DEF AppendRequests, CandidateEntryBaseInv, InductiveInvariant, RequestIndexBound
            <4>lengths. /\ Len(request.mentries) \in Nat /\ Len(log[leader]) \in Nat
                BY <1>types, LenProperties
            <4>previousBound. request.mprevLogIndex <= Len(log[leader])
                BY <1>types, <4>lengths, <4>bound, SMT
            <4>offsetBound. \A offset \in DOMAIN request.mentries:
                request.mprevLogIndex + offset <= Len(log[leader])
                BY <1>types, <4>lengths, <4>bound, LenProperties, SMT
            <4>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
                BY <1>types DEF LogEntry
            <4>retained. \A index \in DOMAIN log[leader]:
                log'[leader][index] = log[leader][index]
                BY <1>types, <4>newEntry, AppendProperties
                DEF ClientRequest, CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
            <4> QED BY <3>same, <1>types, <2>snapshot, <4>previousBound,
                <4>offsetBound, <4>retained, LenProperties, SMT
        <3>other. CASE leader # request.msource
            BY <3>other, <1>types, <2>snapshot DEF ClientRequest
        <3> QED BY <3>same, <3>other
    <2>other. CASE ~(\E leader \in Server, value \in Value: ClientRequest(leader, value))
        <3>frame. log'[request.msource] = log[request.msource]
            <4>receive. CASE \E m \in messages: Receive(m)
                <5> PICK m \in messages: Receive(m) BY <4>receive
                <5> QED BY <2>before, <1>types, ServerStatesDistinct, MessageFieldsTypeOK, SMTT(30)
                    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
                        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                        HandleRequestVoteResponse, HandleAppendEntriesRequest, HandleAppendEntriesResponse
            <4>other. CASE ~(\E m \in messages: Receive(m))
                BY <4>other, <2>other, <1>types
                DEF Next, vars, Timeout, ClientRequest, Restart, BecomeLeader,
                    AdvanceCommitIndex, AppendEntries, LeaderStepDown
            <4> QED BY <4>receive, <4>other
        <3> QED BY <3>frame, <2>snapshot
    <2> QED BY <2>client, <2>other
<1> QED BY <1>new, <1>old

LEMMA FreshClientKeyHasNoLaterHistoricalEntry ==
    \A leader \in Server: \A value \in Value:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ ClientRequest(leader, value)
        /\ ClusterMightAgree(Len(log[leader]) + 1, currentTerm[leader]) \in Quorum
        => \A edge \in HistoricalEntryEdges: edge.term <= currentTerm[leader]
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    InductiveInvariant, SuccessfulResponseRecipientWonInv,
                    ClientRequest(leader, value),
                    ClusterMightAgree(Len(log[leader]) + 1, currentTerm[leader]) \in Quorum,
                    NEW edge \in HistoricalEntryEdges,
                    edge.term > currentTerm[leader]
             PROVE FALSE
    BY HistoricalEntryEdgeHasTermOwner
    DEF InductiveInvariant, TypeOK, ServerVarsTypeOK
<1> PICK owner \in Server: TermOwner(owner, edge.term, edge.index)
    BY HistoricalEntryEdgeHasTermOwner
<1>types. /\ edge.term \in Nat /\ Len(log[leader]) + 1 \in Nat
            /\ Len(log[leader]) < Len(log[leader]) + 1
    BY HistoricalEntryEdgeHasTermOwner, LenProperties, SMT
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1> QED BY <1>types, HistoricalHigherElectionExcludesUncreatedEntry
    DEF ClientRequest, TermOwner

LEMMA FreshClientKeyHasNoLaterHistoricalRequest ==
    \A leader \in Server: \A value \in Value:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ AppendRequestSenderWonInv
        /\ ClientRequest(leader, value)
        /\ ClusterMightAgree(Len(log[leader]) + 1, currentTerm[leader]) \in Quorum
        => \A request \in AppendRequests: request.mterm <= currentTerm[leader]
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    InductiveInvariant, SuccessfulResponseRecipientWonInv,
                    AppendRequestSenderWonInv, ClientRequest(leader, value),
                    ClusterMightAgree(Len(log[leader]) + 1, currentTerm[leader]) \in Quorum,
                    NEW request \in AppendRequests,
                    request.mterm > currentTerm[leader]
             PROVE FALSE
    BY MessageFieldsTypeOK
    DEF AppendRequests, InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>types. /\ request.msource \in Server /\ request.mterm \in Nat
            /\ Len(log[leader]) + 1 \in Nat
            /\ Len(log[leader]) < Len(log[leader]) + 1
    BY MessageFieldsTypeOK, LenProperties, SMT
    DEF AppendRequests, InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY <1>types, HistoricalHigherElectionExcludesUncreatedEntry
    DEF AppendRequests, ClientRequest, AppendRequestSenderWonInv,
        InductiveInvariant, SendInvariant

LEMMA FreshClientKeyHasNoHigherTermVoteEvidence ==
    \A leader \in Server: \A value \in Value:
        /\ InductiveInvariant /\ SuccessfulResponseRecipientWonInv
        /\ ClientRequest(leader, value)
        => \A request \in messages:
               /\ request.mtype = RequestVoteRequest
               /\ currentTerm[leader] < request.mterm
               /\ Grant(request.mdest, request.msource, request.mterm)
               => ~EntryAgreementEvidence(request.mdest,
                       Len(log[leader]) + 1, currentTerm[leader])
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    InductiveInvariant, SuccessfulResponseRecipientWonInv,
                    ClientRequest(leader, value), NEW request \in messages,
                    request.mtype = RequestVoteRequest,
                    currentTerm[leader] < request.mterm,
                    Grant(request.mdest, request.msource, request.mterm)
             PROVE ~EntryAgreementEvidence(request.mdest,
                       Len(log[leader]) + 1, currentTerm[leader])
    OBVIOUS
<1>types. /\ request.mdest \in Server /\ request.msource \in Server
            /\ request.mterm \in Nat /\ currentTerm[leader] \in Nat
            /\ currentTerm[request.mdest] \in Nat /\ Len(log[leader]) \in Nat
            /\ Len(log[leader]) + 1 \in Nat
    BY MessageFieldsTypeOK, LenProperties, SMT
    DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>bound. request.mterm <= currentTerm[request.mdest]
    BY <1>types, GrantTermBoundFromSendInvariant DEF GrantTermBoundInv
<1>higher. currentTerm[leader] < currentTerm[request.mdest]
    BY <1>types, <1>bound, SMT
<1> QED BY <1>types, <1>higher, UncreatedEntryHasNoHigherTermEvidence, SMT
    DEF ClientRequest

LEMMA ActiveLeaderHistoricalSameTermSnapshot ==
    \A leader \in Server: \A edge \in HistoricalEntryEdges:
        /\ InductiveInvariant /\ EntryEdgeConsistency
        /\ state[leader] = Leader /\ edge.term = currentTerm[leader]
        => /\ edge.index \in DOMAIN log[leader]
           /\ edge.previous = LogEntryEdge(log[leader], edge.index).previous
           /\ edge.entry = log[leader][edge.index]
<1> SUFFICES ASSUME NEW leader \in Server, NEW edge \in HistoricalEntryEdges,
                    InductiveInvariant, EntryEdgeConsistency,
                    state[leader] = Leader, edge.term = currentTerm[leader]
             PROVE /\ edge.index \in DOMAIN log[leader]
                   /\ edge.previous = LogEntryEdge(log[leader], edge.index).previous
                   /\ edge.entry = log[leader][edge.index]
    OBVIOUS
<1> PICK owner \in Server: TermOwner(owner, edge.term, edge.index)
    BY HistoricalEntryEdgeHasTermOwner
<1>won. Won(leader, currentTerm[leader]) BY ActiveLeaderWon
<1>same. owner = leader
    BY <1>won, WonUnique DEF TermOwner, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>entry. /\ edge.index \in DOMAIN log[leader]
             /\ log[leader][edge.index].term = edge.term
    BY <1>same DEF TermOwner, OwnerActive, LogHasTermAt
<1>copy. LogEntryEdge(log[leader], edge.index) \in HistoricalEntryEdges
    BY <1>entry DEF HistoricalEntryEdges
<1>types. /\ edge.index \in Nat /\ edge.term \in Nat
    BY HistoricalEntryEdgeHasTermOwner
<1>consistent.
    /\ edge.previous = LogEntryEdge(log[leader], edge.index).previous
    /\ edge.entry = log[leader][edge.index]
    BY <1>types, <1>entry, <1>copy
    DEF EntryEdgeConsistency, LogEntryEdge
<1> QED BY <1>entry, <1>consistent

LEMMA HistoricalSameTermBoundaryInit == Init => HistoricalSameTermBoundaryInv
    BY DEF Init, InitLogVars, HistoricalSameTermBoundaryInv, HistoricalEntryEdges, AppendRequests

LEMMA HistoricalSameTermBoundaryClient ==
    \A leader \in Server: \A value \in Value:
        /\ InductiveInvariant /\ EntryEdgeConsistency /\ TermOrderingInv
        /\ HistoricalSameTermBoundaryInv /\ ClientRequest(leader, value)
        => HistoricalSameTermBoundaryInv'
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    InductiveInvariant, EntryEdgeConsistency, TermOrderingInv,
                    HistoricalSameTermBoundaryInv, ClientRequest(leader, value),
                    NEW left \in HistoricalEntryEdges', NEW right \in HistoricalEntryEdges',
                    left.term = right.term, left.index < right.index
             PROVE right.previous = right.term
    BY DEF HistoricalSameTermBoundaryInv
<1> DEFINE fresh == LogEntryEdge(log'[leader], Len(log[leader]) + 1)
<1>origin. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh}
    BY ClientHistoricalEntryEdges DEF fresh
<1>types. /\ log[leader] \in Seq(LogEntry) /\ Len(log[leader]) \in Nat
            /\ currentTerm[leader] \in Nat
    BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
    BY <1>types DEF LogEntry
<1>newTerm. /\ fresh.index = Len(log[leader]) + 1
              /\ fresh.term = currentTerm[leader]
    BY <1>types, <1>newEntry, AppendProperties
    DEF fresh, ClientRequest, LogEntryEdge, InductiveInvariant, TypeOK, LogVarsTypeOK
<1>old. CASE left \in HistoricalEntryEdges /\ right \in HistoricalEntryEdges
    BY <1>old DEF HistoricalSameTermBoundaryInv
<1>rightNew. CASE left \in HistoricalEntryEdges /\ right = fresh
    <2>leftTerm. left.term = currentTerm[leader]
        BY <1>rightNew, <1>newTerm
    <2>copy.
        /\ left.index \in DOMAIN log[leader]
        /\ left.entry = log[leader][left.index]
        BY <1>rightNew, <2>leftTerm, ActiveLeaderHistoricalSameTermSnapshot
        DEF ClientRequest
    <2>snapshot. /\ left.index \in DOMAIN log[leader]
                   /\ log[leader][left.index].term = currentTerm[leader]
        BY <2>copy, <2>leftTerm
        DEF HistoricalEntryEdges, LogEntryEdge, RequestEntryEdge
    <2>bound. /\ left.index <= Len(log[leader]) /\ Len(log[leader]) > 0
                /\ Len(log[leader]) \in DOMAIN log[leader]
        BY <2>snapshot, <1>types, LenProperties, SMT
    <2>lower. currentTerm[leader] <= log[leader][Len(log[leader])].term
        BY <1>types, <2>snapshot, <2>bound
        DEF TermOrderingInv, LogTermsMonotonic
    <2>upper. log[leader][Len(log[leader])].term <= currentTerm[leader]
        BY <2>bound DEF InductiveInvariant, LogTermBoundInv
    <2>lastType. log[leader][Len(log[leader])].term \in Nat
        BY <1>types, <2>bound, ElementOfSeq DEF LogEntry
    <2>term. log[leader][Len(log[leader])].term = currentTerm[leader]
        BY <2>lower, <2>upper, <2>lastType, <1>types, SMT
    <2>retained.
        log'[leader][Len(log[leader])] = log[leader][Len(log[leader])]
        BY <1>types, <1>newEntry, <2>bound, AppendProperties
        DEF ClientRequest, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2> QED BY <1>rightNew, <1>newTerm, <1>types, <2>bound, <2>term, <2>retained, SMT
        DEF fresh, LogEntryEdge
<1>leftNew. CASE left = fresh /\ right \in HistoricalEntryEdges
    <2>snapshot. right.index \in DOMAIN log[leader]
        BY <1>leftNew, <1>newTerm, ActiveLeaderHistoricalSameTermSnapshot DEF ClientRequest
    <2> QED BY <2>snapshot, <1>leftNew, <1>newTerm, <1>types, LenProperties, SMT
<1>both. CASE left = fresh /\ right = fresh
    BY <1>both, <1>newTerm, <1>types, SMT
<1> QED BY <1>origin, <1>old, <1>rightNew, <1>leftNew, <1>both

LEMMA HistoricalSameTermBoundaryNext ==
    /\ InductiveInvariant /\ EntryEdgeConsistency /\ TermOrderingInv
    /\ AppendRequestRootTerm /\ HistoricalSameTermBoundaryInv /\ [Next]_vars
    => HistoricalSameTermBoundaryInv'
<1>client. CASE \E leader \in Server, value \in Value: ClientRequest(leader, value)
    BY <1>client, HistoricalSameTermBoundaryClient
<1>send. CASE \E leader, recipient \in Server: AppendEntries(leader, recipient)
    BY <1>send, EntryEdgeAppendSendSubset DEF HistoricalSameTermBoundaryInv
<1>receive. CASE \E recipient, sender \in Server, request \in messages:
        request.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(recipient, sender, request)
    BY <1>receive, EntryEdgeAppendReceiveSubset DEF HistoricalSameTermBoundaryInv
<1>other. CASE
    /\ ~(\E leader \in Server, value \in Value: ClientRequest(leader, value))
    /\ ~(\E leader, recipient \in Server: AppendEntries(leader, recipient))
    /\ ~(\E recipient, sender \in Server, request \in messages:
        request.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(recipient, sender, request))
    BY <1>other, EntryEdgeOtherSubset DEF HistoricalSameTermBoundaryInv
<1> QED BY <1>client, <1>send, <1>receive, <1>other

LEMMA LogContainingEntryHasFreshLastTerm ==
    \A server \in Server: \A entry \in HistoricalEntryKeys:
        /\ InductiveInvariant /\ TermOrderingInv
        /\ LogHasTermAt(server, entry.term, entry.index)
        => /\ entry.term <= LastTerm(log[server])
           /\ (entry.term = LastTerm(log[server]) => entry.index <= Len(log[server]))
<1> SUFFICES ASSUME NEW server \in Server, NEW entry \in HistoricalEntryKeys,
                    InductiveInvariant, TermOrderingInv,
                    LogHasTermAt(server, entry.term, entry.index)
             PROVE /\ entry.term <= LastTerm(log[server])
                   /\ (entry.term = LastTerm(log[server]) => entry.index <= Len(log[server]))
    OBVIOUS
<1>types. /\ log[server] \in Seq(LogEntry) /\ entry.index \in Nat \ {0}
            /\ entry.term \in Nat /\ Len(log[server]) \in Nat
    BY HistoricalEntryKeyHasWinner, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>bound. /\ entry.index <= Len(log[server]) /\ Len(log[server]) > 0
            /\ Len(log[server]) \in DOMAIN log[server]
    BY <1>types, LenProperties, SMT DEF LogHasTermAt
<1>term. entry.term <= log[server][Len(log[server])].term
    BY <1>bound DEF TermOrderingInv, LogTermsMonotonic, LogHasTermAt
<1> QED BY <1>types, <1>bound, <1>term DEF LastTerm

LEMMA GrantingVoterForcesCoveringRequest ==
    \A request \in messages: \A entry \in ClusterAgreeCandidateEntries:
        /\ ClusterAgreeProofInv /\ CandidateEntryEvidenceRetainedInv
        /\ request.mtype = RequestVoteRequest /\ entry.term < request.mterm
        /\ EntryAgreementEvidence(request.mdest, entry.index, entry.term)
        /\ HandleRequestVoteRequest(request.mdest, request.msource, request)
        /\ Grant(request.mdest, request.msource, request.mterm)'
        /\ ~Grant(request.mdest, request.msource, request.mterm)
        => VoteRequestCoversEntry(request, entry)
<1> SUFFICES ASSUME NEW request \in messages,
                    NEW entry \in ClusterAgreeCandidateEntries,
                    ClusterAgreeProofInv, CandidateEntryEvidenceRetainedInv,
                    request.mtype = RequestVoteRequest, entry.term < request.mterm,
                    EntryAgreementEvidence(request.mdest, entry.index, entry.term),
                    HandleRequestVoteRequest(request.mdest, request.msource, request),
                    Grant(request.mdest, request.msource, request.mterm)',
                    ~Grant(request.mdest, request.msource, request.mterm)
             PROVE VoteRequestCoversEntry(request, entry)
    OBVIOUS
<1>types. /\ request.mdest \in Server /\ request.mlastLogTerm \in Nat
            /\ request.mlastLogIndex \in Nat /\ entry.index \in Nat
            /\ entry.term \in Nat /\ LastTerm(log[request.mdest]) \in Nat
            /\ Len(log[request.mdest]) \in Nat
    BY MessageFieldsTypeOK, HistoricalEntryKeyHasWinner, LastTermTypeOK, LenProperties
    DEF ClusterAgreeCandidateEntries, ClusterAgreeProofInv,
        InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1>entry. LogHasTermAt(request.mdest, entry.term, entry.index)
    BY <1>types DEF CandidateEntryEvidenceRetainedInv
<1>fresh. /\ entry.term <= LastTerm(log[request.mdest])
            /\ (entry.term = LastTerm(log[request.mdest]) =>
                    entry.index <= Len(log[request.mdest]))
    BY <1>types, <1>entry, LogContainingEntryHasFreshLastTerm
    DEF ClusterAgreeCandidateEntries, ClusterAgreeProofInv
<1>requestFresh.
    \/ request.mlastLogTerm > LastTerm(log[request.mdest])
    \/ /\ request.mlastLogTerm = LastTerm(log[request.mdest])
       /\ request.mlastLogIndex >= Len(log[request.mdest])
    BY MessageTypesDistinct, SMTT(30)
    DEF HandleRequestVoteRequest, Grant, Send, WithMessage, WithMessages
<1> QED BY <1>types, <1>fresh, <1>requestFresh, SMT DEF VoteRequestCoversEntry

LEMMA FreshClientEdgeProtectsExistingCandidateEntries ==
    \A leader \in Server: \A value \in Value:
        /\ CandidateEntryBaseInv /\ LeaderCandidateEntryInv
        /\ ClientRequest(leader, value)
        => \A entry \in ClusterAgreeCandidateEntries:
               entry.term < currentTerm[leader] =>
                   /\ entry.index < Len(log[leader]) + 1
                   /\ entry.term <=
                       LogEntryEdge(log'[leader], Len(log[leader]) + 1).previous
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    CandidateEntryBaseInv, LeaderCandidateEntryInv,
                    ClientRequest(leader, value),
                    NEW entry \in ClusterAgreeCandidateEntries,
                    entry.term < currentTerm[leader]
             PROVE /\ entry.index < Len(log[leader]) + 1
                   /\ entry.term <=
                       LogEntryEdge(log'[leader], Len(log[leader]) + 1).previous
    OBVIOUS
<1>types. /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
            /\ currentTerm[leader] \in Nat /\ Len(log[leader]) \in Nat
            /\ log[leader] \in Seq(LogEntry)
    BY HistoricalEntryKeyHasWinner, LenProperties
    DEF CandidateEntryBaseInv, ClusterAgreeCandidateEntries,
        InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>entry. LogHasTermAt(leader, entry.term, entry.index)
    BY <1>types, SMT DEF LeaderCandidateEntryInv, ClientRequest
<1>fresh. /\ entry.index <= Len(log[leader])
            /\ entry.term <= LastTerm(log[leader])
    BY <1>types, <1>entry, LogContainingEntryHasFreshLastTerm, LenProperties
    DEF CandidateEntryBaseInv, ClusterAgreeCandidateEntries, LogHasTermAt
<1>nonempty. Len(log[leader]) > 0 BY <1>types, <1>fresh, SMT
<1>last. Len(log[leader]) \in DOMAIN log[leader]
    BY <1>types, <1>nonempty, LenProperties
<1>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
    BY <1>types DEF LogEntry
<1>retained.
    log'[leader][Len(log[leader])] = log[leader][Len(log[leader])]
    BY <1>types, <1>last, <1>newEntry, AppendProperties
    DEF ClientRequest, CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
<1>previous.
    LogEntryEdge(log'[leader], Len(log[leader]) + 1).previous = LastTerm(log[leader])
    BY <1>types, <1>nonempty, <1>retained, SMT DEF LogEntryEdge, LastTerm
<1> QED BY <1>types, <1>fresh, <1>previous, SMT

LEMMA HistoricalNewerBoundaryInit == Init => HistoricalNewerEntryBoundaryInv
    BY DEF Init, InitLogVars, HistoricalNewerEntryBoundaryInv,
        HistoricalEntryEdges, HistoricalEntryKeys, ClusterAgreeCandidateEntries, AppendRequests

LEMMA HistoricalNewerBoundaryClient ==
    \A leader \in Server: \A value \in Value:
        /\ CandidateEntryBaseInv /\ HistoricalNewerEntryBoundaryInv
        /\ LeaderCandidateEntryInv /\ ClientRequest(leader, value)
        => HistoricalNewerEntryBoundaryInv'
<1> SUFFICES ASSUME NEW leader \in Server, NEW value \in Value,
                    CandidateEntryBaseInv, HistoricalNewerEntryBoundaryInv,
                    LeaderCandidateEntryInv, ClientRequest(leader, value),
                    NEW edge \in HistoricalEntryEdges',
                    NEW entry \in ClusterAgreeCandidateEntries', entry.term < edge.term
             PROVE /\ entry.index < edge.index /\ entry.term <= edge.previous
    BY DEF HistoricalNewerEntryBoundaryInv
<1> DEFINE fresh == LogEntryEdge(log'[leader], Len(log[leader]) + 1)
<1>origin. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh}
    BY ClientHistoricalEntryEdges DEF CandidateEntryBaseInv, fresh
<1>types. /\ log[leader] \in Seq(LogEntry) /\ Len(log[leader]) \in Nat
            /\ currentTerm[leader] \in Nat
    BY LenProperties DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
        LogVarsTypeOK, ServerVarsTypeOK
<1>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
    BY <1>types DEF LogEntry
<1>freshKey. /\ fresh.index = Len(log[leader]) + 1 /\ fresh.term = currentTerm[leader]
    BY <1>types, <1>newEntry, AppendProperties
    DEF fresh, ClientRequest, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK, LogEntryEdge
<1>oldKey. CASE entry \in HistoricalEntryKeys
    <2>eligible. entry \in ClusterAgreeCandidateEntries
        BY <1>oldKey, ExistingHistoricalKeysCannotBecomeEligible
        DEF CandidateEntryBaseInv, Next, vars
    <2>oldEdge. CASE edge \in HistoricalEntryEdges
        BY <2>oldEdge, <2>eligible DEF HistoricalNewerEntryBoundaryInv
    <2>freshEdge. CASE edge = fresh
        BY <2>freshEdge, <2>eligible, <1>freshKey, FreshClientEdgeProtectsExistingCandidateEntries
    <2> QED BY <1>origin, <2>oldEdge, <2>freshEdge
<1>freshEntry. CASE entry \notin HistoricalEntryKeys
    <2>key. entry = [index |-> fresh.index, term |-> fresh.term]
        BY <1>freshEntry, <1>origin
        DEF ClusterAgreeCandidateEntries, HistoricalEntryKeys
    <2>potentialUnchanged.
        \A index, term \in Nat:
            ClusterMightAgree(index, term)' = ClusterMightAgree(index, term)
        BY DEF ClientRequest, ClusterMightAgree, EntryAgreementEvidence,
            Won, Started, VoteFor, Grant
    <2>quorum. ClusterMightAgree(Len(log[leader]) + 1, currentTerm[leader]) \in Quorum
        BY <2>key, <1>freshKey, <1>types, <2>potentialUnchanged
        DEF ClusterAgreeCandidateEntries
    <2>noLater. \A old \in HistoricalEntryEdges: old.term <= currentTerm[leader]
        BY <2>quorum, FreshClientKeyHasNoLaterHistoricalEntry DEF CandidateEntryBaseInv
    <2>edgeOld. CASE edge \in HistoricalEntryEdges
        <3>edgeType. edge.term \in Nat
            BY <2>edgeOld, HistoricalEntryEdgeHasTermOwner DEF CandidateEntryBaseInv
        <3>upper. edge.term <= currentTerm[leader] BY <2>edgeOld, <2>noLater
        <3> QED BY <3>upper, <2>key, <1>freshKey, <1>types, <3>edgeType, SMT
    <2>edgeNew. CASE edge = fresh
        BY <2>edgeNew, <2>key, <1>freshKey, <1>types, SMT
    <2> QED BY <1>origin, <2>edgeOld, <2>edgeNew
<1> QED BY <1>oldKey, <1>freshEntry

LEMMA HistoricalNewerBoundaryCopiedEdges ==
    /\ CandidateEntryBaseInv /\ HistoricalNewerEntryBoundaryInv /\ [Next]_vars
    /\ HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    => HistoricalNewerEntryBoundaryInv'
    BY ExistingHistoricalKeysCannotBecomeEligible
    DEF CandidateEntryBaseInv, HistoricalNewerEntryBoundaryInv,
        ClusterAgreeCandidateEntries, HistoricalEntryKeys

LEMMA HistoricalNewerBoundaryNext ==
    /\ CandidateEntryBaseInv /\ HistoricalNewerEntryBoundaryInv
    /\ LeaderCandidateEntryInv /\ [Next]_vars
    => HistoricalNewerEntryBoundaryInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, HistoricalNewerEntryBoundaryInv,
                    LeaderCandidateEntryInv, [Next]_vars
             PROVE HistoricalNewerEntryBoundaryInv'
    OBVIOUS
<1>client. CASE \E leader \in Server, value \in Value: ClientRequest(leader, value)
    BY <1>client, HistoricalNewerBoundaryClient
<1>send. CASE \E leader, recipient \in Server: AppendEntries(leader, recipient)
    BY <1>send, EntryEdgeAppendSendSubset, HistoricalNewerBoundaryCopiedEdges
    DEF CandidateEntryBaseInv
<1>receive. CASE \E request \in messages:
        request.mtype = AppendEntriesRequest /\
        HandleAppendEntriesRequest(request.mdest, request.msource, request)
    <2>types. \A request \in messages:
            request.mdest \in Server /\ request.msource \in Server
        BY StoredMessageFieldsTypeOK DEF CandidateEntryBaseInv, InductiveInvariant
    <2>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges
        BY <1>receive, <2>types, EntryEdgeAppendReceiveSubset DEF CandidateEntryBaseInv
    <2> QED BY <2>edges, HistoricalNewerBoundaryCopiedEdges
<1>unchanged. CASE log' = log /\
        ~(\E leader, recipient \in Server: AppendEntries(leader, recipient))
    <2>requests. AppendRequests' \subseteq AppendRequests
        BY <1>unchanged, NewAppendRequestOrigin DEF CandidateEntryBaseInv, AppendRequests
    <2>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges
        BY <1>unchanged, <2>requests DEF HistoricalEntryEdges
    <2> QED BY <2>edges, HistoricalNewerBoundaryCopiedEdges
<1> QED BY <1>client, <1>send, <1>receive, <1>unchanged, LogChangingActionNext
    DEF CandidateEntryBaseInv

LEMMA CandidateAppendPreservesProtectedReplica ==
    \A request \in messages:
        /\ CandidateEntryBaseInv /\ CandidateAppendPrefixInv
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        => \A entry \in ClusterAgreeCandidateEntries:
               \A server \in ClusterReplicated(entry.index, entry.term):
                   server \in ClusterReplicated(entry.index, entry.term)'
<1> SUFFICES ASSUME NEW request \in messages, CandidateEntryBaseInv,
                    CandidateAppendPrefixInv, request.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(request.mdest, request.msource, request),
                    NEW entry \in ClusterAgreeCandidateEntries,
                    NEW server \in ClusterReplicated(entry.index, entry.term)
             PROVE server \in ClusterReplicated(entry.index, entry.term)'
    OBVIOUS
<1>types. /\ log \in [Server -> Seq(LogEntry)] /\ entry.index \in Nat \ {0}
            /\ entry.term \in Nat /\ request.mterm \in Nat
            /\ request.mprevLogIndex \in Nat /\ request.mdest \in Server
            /\ currentTerm[request.mdest] \in Nat
    BY HistoricalEntryKeyHasWinner, MessageFieldsTypeOK
    DEF ClusterAgreeCandidateEntries, ClusterReplicated, CandidateEntryBaseInv,
        InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>other. CASE server # request.mdest
    <2>frame. log'[server] = log[server]
        BY <1>types, <1>other DEF HandleAppendEntriesRequest, ClusterReplicated
    <2> QED BY <2>frame DEF ClusterReplicated
<1>same. CASE server = request.mdest
    <2>unchanged. CASE log' = log BY <2>unchanged DEF ClusterReplicated
    <2>changed. CASE log' # log
        <3>shape.
            /\ request.mprevLogIndex \in 0..Len(log[server])
            /\ request.mentries # << >>
            /\ request.mterm = currentTerm[server]
            /\ log'[server] = Append(SubSeq(log[server], 1, request.mprevLogIndex), request.mentries[1])
        BY <1>same, <2>changed, AppendRequestChangedLogShape, <1>types
        DEF CandidateEntryBaseInv, HandleAppendEntriesRequest
        <3>term. entry.term <= request.mterm
            BY <3>shape, <1>same
            DEF ClusterReplicated, CandidateEntryBaseInv, InductiveInvariant, LogTermBoundInv
        <3>prefix. CASE entry.index <= request.mprevLogIndex
            <4>endpoint. entry.index \in 1..request.mprevLogIndex
                BY <1>types, <3>prefix, SMT
            <4>retained. log'[server][entry.index] = log[server][entry.index]
                BY <1>same, <3>shape, <4>endpoint, AppendRequestRetainsMatchedPrefix
                DEF CandidateEntryBaseInv, ClusterReplicated
            <4>inductive. InductiveInvariant BY DEF CandidateEntryBaseInv
            <4>requestTypes. /\ request.mdest \in Server /\ request.msource \in Server
                BY MessageFieldsTypeOK
                DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK
            <4>postType. log'[server] \in Seq(LogEntry)
                BY <1>same, <4>inductive, <4>requestTypes, HandleAppendEntriesRequestLogVarsTypeOK
                DEF InductiveInvariant, LogVarsTypeOK, ClusterReplicated
            <4>length. Len(log'[server]) = request.mprevLogIndex + 1
                BY <1>same, <2>changed, <4>inductive, <4>requestTypes, AppendRequestChangedLogShape
            <4>domain. entry.index \in DOMAIN log'[server]
                BY <1>types, <4>endpoint, <4>postType, <4>length, LenProperties, SMT
            <4> QED BY <4>retained, <4>domain DEF ClusterReplicated
        <3>conflict. CASE request.mprevLogIndex < entry.index
            <4>compatible.
                request.mentries[1].term = log[server][request.mprevLogIndex + 1].term
                BY <1>same, <3>shape, <3>term, <3>conflict
                DEF CandidateAppendPrefixInv, AppendRequests
            <4> QED BY <4>compatible, <1>same, <1>types, <3>shape, <3>conflict,
                LenProperties, SMT DEF HandleAppendEntriesRequest, ClusterReplicated
        <3> QED BY <1>types, <3>prefix, <3>conflict, SMT
    <2> QED BY <2>unchanged, <2>changed
<1> QED BY <1>other, <1>same

LEMMA HistoricalSameTermBoundaryImpliesIntervals ==
    /\ InductiveInvariant /\ EntryEdgeConsistency /\ HistoricalSameTermBoundaryInv
    => SameTermEntryIntervalsInv
<1> SUFFICES ASSUME InductiveInvariant, EntryEdgeConsistency, HistoricalSameTermBoundaryInv,
                    NEW left \in Server, NEW right \in Server,
                    NEW high \in DOMAIN log[left], NEW low \in DOMAIN log[right],
                    low <= high, log[left][high].term = log[right][low].term
             PROVE /\ low \in DOMAIN log[left]
                   /\ log[left][low].term = log[right][low].term
    BY DEF SameTermEntryIntervalsInv
<1>types. /\ log[left] \in Seq(LogEntry) /\ log[right] \in Seq(LogEntry)
            /\ high \in Nat /\ low \in Nat /\ low > 0 /\ high <= Len(log[left])
    BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>domain. low \in DOMAIN log[left] BY <1>types, LenProperties, SMT
<1>rightEdge. LogEntryEdge(log[right], low) \in HistoricalEntryEdges
    BY DEF HistoricalEntryEdges
<1> DEFINE P(distance) == distance <= high - low =>
        log[left][high - distance].term = log[right][low].term
<1>base. P(0) BY <1>types, SMT DEF P
<1>step. \A distance \in Nat: P(distance) => P(distance + 1)
    <2> SUFFICES ASSUME NEW distance \in Nat, P(distance), distance + 1 <= high - low
                 PROVE log[left][high - (distance + 1)].term = log[right][low].term
        BY DEF P
    <2>domain. /\ high - distance \in DOMAIN log[left] /\ low < high - distance
                 /\ high - distance > 1 /\ high - (distance + 1) = high - distance - 1
        BY <1>types, LenProperties, SMT
    <2>term. log[left][high - distance].term = log[right][low].term
        BY <1>types, SMT DEF P
    <2>edge. LogEntryEdge(log[left], high - distance) \in HistoricalEntryEdges
        BY <2>domain DEF HistoricalEntryEdges
    <2>previous.
        LogEntryEdge(log[left], high - distance).previous = log[right][low].term
        BY <1>rightEdge, <2>edge, <2>term, <2>domain
        DEF HistoricalSameTermBoundaryInv, LogEntryEdge
    <2> QED BY <1>types, <2>domain, <2>previous, SMT DEF LogEntryEdge
<1>all. \A distance \in Nat: P(distance) BY <1>base, <1>step, NatInduction
<1>end. log[left][low].term = log[right][low].term
    BY <1>all, <1>types, SMT DEF P
<1> QED BY <1>domain, <1>end

LEMMA HistoricalBoundaryImpliesCandidateNewerPrefixes ==
    /\ InductiveInvariant /\ HistoricalNewerEntryBoundaryInv
    /\ HistoricalSameTermBoundaryInv
    => CandidateNewerLogPrefixesInv
<1> SUFFICES ASSUME InductiveInvariant, HistoricalNewerEntryBoundaryInv,
                    HistoricalSameTermBoundaryInv,
                    NEW server \in Server, NEW index \in DOMAIN log[server],
                    NEW entry \in ClusterAgreeCandidateEntries,
                    entry.term < log[server][index].term
             PROVE /\ entry.index <= index
                   /\ LogHasTermAt(server, entry.term, entry.index)
    BY DEF CandidateNewerLogPrefixesInv
<1>types. /\ log[server] \in Seq(LogEntry)
            /\ index \in Nat /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
            /\ index <= Len(log[server])
    BY HistoricalEntryKeyHasWinner, LenProperties
    DEF ClusterAgreeCandidateEntries, InductiveInvariant, TypeOK, LogVarsTypeOK
<1> DEFINE P(distance) ==
    distance \in Nat /\ distance <= index - entry.index =>
        entry.term <= log[server][index - distance].term
<1>base. P(0) BY <1>types, SMT DEF P
<1>step. \A distance \in Nat: P(distance) => P(distance + 1)
    <2> SUFFICES ASSUME NEW distance \in Nat, P(distance),
                        distance + 1 <= index - entry.index
                 PROVE entry.term <= log[server][index - (distance + 1)].term
        BY DEF P
    <2>domain. /\ index - distance \in DOMAIN log[server]
                 /\ entry.index < index - distance
                 /\ index - distance > 1
                 /\ index - (distance + 1) = index - distance - 1
        BY <1>types, LenProperties, SMT
    <2>term. entry.term <= log[server][index - distance].term
        BY <1>types, SMT DEF P
    <2>equal. CASE entry.term = log[server][index - distance].term
        <3>edge. LogEntryEdge(log[server], index - distance) \in HistoricalEntryEdges
            BY <2>domain DEF HistoricalEntryEdges
        <3> PICK old \in HistoricalEntryEdges:
                entry = [index |-> old.index, term |-> old.term]
            BY DEF ClusterAgreeCandidateEntries, HistoricalEntryKeys
        <3>boundary. LogEntryEdge(log[server], index - distance).previous = entry.term
            BY <2>domain, <2>equal, <3>edge, SMT
            DEF HistoricalSameTermBoundaryInv, LogEntryEdge
        <3> QED BY <1>types, <3>boundary, <2>domain, SMT DEF LogEntryEdge
    <2>greater. CASE entry.term < log[server][index - distance].term
        <3>edge. LogEntryEdge(log[server], index - distance) \in HistoricalEntryEdges
            BY <2>domain DEF HistoricalEntryEdges
        <3> QED BY <2>domain, <2>greater, <3>edge
            DEF HistoricalNewerEntryBoundaryInv, LogEntryEdge
    <2> QED BY <2>term, <2>equal, <2>greater, SMT
<1>all. \A distance \in Nat: P(distance)
    BY <1>base, <1>step, NatInduction
<1>bound. entry.index < index
    BY DEF HistoricalNewerEntryBoundaryInv, HistoricalEntryEdges, LogEntryEdge
<1>end. entry.term <= log[server][entry.index].term
    BY <1>all, <1>bound, <1>types, SMT DEF P
<1>domain. entry.index \in DOMAIN log[server]
    BY <1>bound, <1>types, LenProperties, SMT
<1>edge. LogEntryEdge(log[server], entry.index) \in HistoricalEntryEdges
    BY <1>domain DEF HistoricalEntryEdges
<1>notGreater. ~(entry.term < log[server][entry.index].term)
    BY <1>edge DEF HistoricalNewerEntryBoundaryInv, LogEntryEdge
<1> QED BY <1>bound, <1>domain, <1>end, <1>notGreater, SMT DEF LogHasTermAt

LEMMA CandidateQuorumCandidateEntriesAreOlder ==
    \A candidate \in Server:
        /\ ClusterAgreeCandidateProofInv
        /\ state[candidate] = Candidate
        /\ votesGranted[candidate] \in Quorum
        => \A entry \in ClusterAgreeCandidateEntries:
               entry.term <= currentTerm[candidate] =>
                   entry.term < currentTerm[candidate]
<1> SUFFICES ASSUME NEW candidate \in Server, ClusterAgreeCandidateProofInv,
                    state[candidate] = Candidate,
                    votesGranted[candidate] \in Quorum,
                    NEW entry \in ClusterAgreeCandidateEntries,
                    entry.term = currentTerm[candidate]
             PROVE FALSE
    BY HistoricalEntryKeyHasWinner
    DEF ClusterAgreeCandidateEntries, ClusterAgreeCandidateProofInv,
        ClusterAgreeProofInv, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1> PICK owner \in Server: TermOwner(owner, entry.term, entry.index)
    BY HistoricalEntryKeyHasWinner
    DEF ClusterAgreeCandidateEntries, ClusterAgreeCandidateProofInv,
        ClusterAgreeProofInv
<1>won. Won(candidate, currentTerm[candidate])
    BY CandidateWithQuorumWon DEF ClusterAgreeCandidateProofInv, ClusterAgreeProofInv
<1>owner. owner = candidate
    BY <1>won, WonUnique
    DEF TermOwner, ClusterAgreeCandidateProofInv, ClusterAgreeProofInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>entry. /\ entry.index \in DOMAIN log[candidate]
             /\ log[candidate][entry.index].term = currentTerm[candidate]
    BY <1>owner
    DEF TermOwner, OwnerActive, LogHasTermAt,
        ClusterAgreeCandidateProofInv, ClusterAgreeProofInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK
<1> QED BY <1>entry
    DEF ClusterAgreeCandidateProofInv, ClusterAgreeProofInv, CandidateCurrentTermFree

LEMMA ElectionQuorumContainsClusterAgreeCandidateEntries ==
    \A candidate \in Server:
        /\ ClusterAgreeCandidateProofInv
        /\ state[candidate] = Candidate
        /\ votesGranted[candidate] \in Quorum
        => \A entry \in ClusterAgreeCandidateEntries:
               entry.term <= currentTerm[candidate] =>
                   /\ entry.index \in DOMAIN log[candidate]
                   /\ log[candidate][entry.index].term = entry.term
<1> SUFFICES ASSUME NEW candidate \in Server, ClusterAgreeCandidateProofInv,
                    state[candidate] = Candidate,
                    votesGranted[candidate] \in Quorum,
                    NEW entry \in ClusterAgreeCandidateEntries,
                    entry.term <= currentTerm[candidate]
             PROVE /\ entry.index \in DOMAIN log[candidate]
                   /\ log[candidate][entry.index].term = entry.term
    OBVIOUS
<1>older. entry.term < currentTerm[candidate]
    BY CandidateQuorumCandidateEntriesAreOlder
<1>intersection.
        votesGranted[candidate] \cap
            ClusterMightAgree(entry.index, entry.term) # {}
    BY QuorumsIntersect DEF ClusterAgreeCandidateEntries
<1> PICK voter \in votesGranted[candidate] \cap
        ClusterMightAgree(entry.index, entry.term): TRUE
    BY <1>intersection
<1>types. /\ voter \in Server
            /\ currentTerm[candidate] \in Nat
            /\ currentTerm[voter] \in Nat
            /\ entry.term \in Nat
            /\ entry.index \in Nat \ {0}
            /\ log[candidate] \in Seq(LogEntry)
            /\ log[voter] \in Seq(LogEntry)
    BY HistoricalEntryKeyHasWinner, LenProperties
    DEF ClusterMightAgree, ClusterAgreeCandidateEntries, HistoricalEntryKeys,
        ClusterAgreeCandidateProofInv, ClusterAgreeProofInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LogEntry
<1>vote. VoteFor(voter, candidate, currentTerm[candidate])
    BY DEF ClusterAgreeCandidateProofInv, ClusterAgreeProofInv,
        InductiveInvariant, ActiveVotesInv
<1>self. CASE voter = candidate
    <2>evidence. EntryAgreementEvidence(candidate, entry.index, entry.term)
        BY <1>self, <1>older, <1>types, SMT DEF ClusterMightAgree
    <2> QED BY <2>evidence
        DEF ClusterAgreeCandidateProofInv, CandidateEntryEvidenceRetainedInv,
            LogHasTermAt
<1>other. CASE voter # candidate
    <2>grant. Grant(voter, candidate, currentTerm[candidate])
        BY <1>other, <1>vote DEF VoteFor
    <2>voterTerm. currentTerm[candidate] <= currentTerm[voter]
        BY <2>grant, <1>types, SMT
        DEF ClusterAgreeCandidateProofInv, GrantTermBoundInv
    <2>evidence. EntryAgreementEvidence(voter, entry.index, entry.term)
        BY <1>older, <1>types, <2>voterTerm, SMT DEF ClusterMightAgree
    <2>voterEntry. LogHasTermAt(voter, entry.term, entry.index)
        BY <2>evidence, <1>types
        DEF ClusterAgreeCandidateProofInv, CandidateEntryEvidenceRetainedInv
    <2> PICK response \in messages:
            /\ response.mtype = RequestVoteResponse
            /\ response.mterm = currentTerm[candidate]
            /\ response.mvoteGranted
            /\ response.msource = voter
            /\ response.mdest = candidate
        BY <2>grant DEF Grant
    <2> PICK request \in messages:
            /\ request.mtype = RequestVoteRequest
            /\ request.msource = candidate
            /\ request.mdest = voter
            /\ request.mterm = currentTerm[candidate]
        BY DEF ClusterAgreeCandidateProofInv, PositiveVoteRequestOriginInv
    <2>covers. VoteRequestCoversEntry(request, entry)
        BY <1>older, <2>grant, <2>evidence
        DEF ClusterAgreeCandidateProofInv, HistoricalVoteProtectionInv
    <2>snapshot. /\ request.mlastLogTerm = LastTerm(log[candidate])
                   /\ request.mlastLogIndex = Len(log[candidate])
        BY DEF ClusterAgreeCandidateProofInv, CandidateRequestSnapshotInv
    <2>newer. CASE request.mlastLogTerm > entry.term
        <3>nonempty. Len(log[candidate]) > 0
            BY <1>types, <2>snapshot, <2>newer, SMT DEF LastTerm
        <3>last. Len(log[candidate]) \in DOMAIN log[candidate]
            BY <1>types, <3>nonempty, LenProperties
        <3>term. entry.term < log[candidate][Len(log[candidate])].term
            BY <2>snapshot, <2>newer, <3>nonempty DEF LastTerm
        <3> QED BY <3>last, <3>term
            DEF ClusterAgreeCandidateProofInv, CandidateNewerLogPrefixesInv,
                LogHasTermAt
    <2>same. CASE /\ request.mlastLogTerm = entry.term
                    /\ request.mlastLogIndex >= entry.index
        <3>nonempty. Len(log[candidate]) > 0
            BY <1>types, <2>snapshot, <2>same, SMT DEF LastTerm
        <3>last. Len(log[candidate]) \in DOMAIN log[candidate]
            BY <1>types, <3>nonempty, LenProperties
        <3>voterIndex. entry.index \in DOMAIN log[voter]
            BY <2>voterEntry DEF LogHasTermAt
        <3>length. entry.index <= Len(log[candidate])
            BY <2>snapshot, <2>same
        <3>lastTerm.
            log[candidate][Len(log[candidate])].term =
                log[voter][entry.index].term
            BY <2>snapshot, <2>same, <2>voterEntry, <3>nonempty
            DEF LastTerm, LogHasTermAt
        <3>candidateEntry.
            /\ entry.index \in DOMAIN log[candidate]
            /\ log[candidate][entry.index].term = log[voter][entry.index].term
            BY <1>types, <3>last, <3>voterIndex, <3>length, <3>lastTerm, SMT
            DEF ClusterAgreeCandidateProofInv, SameTermEntryIntervalsInv
        <3> QED BY <3>candidateEntry, <2>voterEntry DEF LogHasTermAt
    <2> QED BY <2>covers, <2>newer, <2>same DEF VoteRequestCoversEntry
<1> QED BY <1>self, <1>other

LEMMA ElectedLeaderContainsClusterAgreeCandidateEntries ==
    \A leader \in Server:
        ClusterAgreeCandidateProofInv /\ BecomeLeader(leader) =>
            \A entry \in ClusterAgreeCandidateEntries':
                entry.term <= currentTerm'[leader] =>
                    /\ entry.index \in DOMAIN log'[leader]
                    /\ log'[leader][entry.index].term = entry.term
<1> SUFFICES ASSUME NEW leader \in Server,
                    ClusterAgreeCandidateProofInv, BecomeLeader(leader),
                    NEW entry \in ClusterAgreeCandidateEntries',
                    entry.term <= currentTerm'[leader]
             PROVE /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index].term = entry.term
    OBVIOUS
<1>unchanged. /\ ClusterAgreeCandidateEntries' = ClusterAgreeCandidateEntries
                /\ log' = log /\ currentTerm' = currentTerm
    BY DEF BecomeLeader, ClusterAgreeCandidateEntries, HistoricalEntryKeys,
        HistoricalEntryEdges, AppendRequests, ClusterMightAgree,
        EntryAgreementEvidence, Won, Started, VoteFor, Grant
<1> QED BY <1>unchanged, ElectionQuorumContainsClusterAgreeCandidateEntries
    DEF BecomeLeader

LEMMA ElectionQuorumContainsClusterAgreeEntries ==
    \A candidate \in Server:
        /\ ClusterAgreeCandidateProofInv
        /\ state[candidate] = Candidate
        /\ votesGranted[candidate] \in Quorum
        => \A entry \in ClusterAgreeEntries:
               entry.term <= currentTerm[candidate] =>
                   /\ entry.index \in DOMAIN log[candidate]
                   /\ log[candidate][entry.index].term = entry.term
    BY ClusterAgreeEntriesAreCandidateEntries,
        ElectionQuorumContainsClusterAgreeCandidateEntries

LEMMA ElectedLeaderContainsClusterAgreeEntries ==
    \A leader \in Server:
        ClusterAgreeCandidateProofInv /\ BecomeLeader(leader) =>
            \A entry \in ClusterAgreeEntries':
                entry.term <= currentTerm'[leader] =>
                    /\ entry.index \in DOMAIN log'[leader]
                    /\ log'[leader][entry.index].term = entry.term
<1> SUFFICES ASSUME NEW leader \in Server,
                    ClusterAgreeCandidateProofInv, BecomeLeader(leader),
                    NEW entry \in ClusterAgreeEntries',
                    entry.term <= currentTerm'[leader]
             PROVE /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index].term = entry.term
    OBVIOUS
<1>unchanged. /\ ClusterAgreeEntries' = ClusterAgreeEntries
                /\ log' = log /\ currentTerm' = currentTerm
    BY DEF BecomeLeader, ClusterAgreeEntries, ClusterEntries,
        ClusterAgree, ClusterReplicated, Won, Started, VoteFor, Grant
<1> QED BY <1>unchanged, ElectionQuorumContainsClusterAgreeEntries DEF BecomeLeader

LEMMA ExistingLeaderRetainsClusterAgreeEntries ==
    ClusterAgreeProofInv /\ [Next]_vars =>
        \A leader \in Server: \A entry \in ClusterAgreeEntries:
            /\ state[leader] = Leader /\ state'[leader] = Leader
            /\ entry.term <= currentTerm'[leader]
            => /\ entry.index \in DOMAIN log'[leader]
               /\ log'[leader][entry.index].term = entry.term
<1> SUFFICES ASSUME ClusterAgreeProofInv, [Next]_vars,
                    NEW leader \in Server, NEW entry \in ClusterAgreeEntries,
                    state[leader] = Leader, state'[leader] = Leader,
                    entry.term <= currentTerm'[leader]
             PROVE /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index].term = entry.term
    OBVIOUS
<1>term. currentTerm'[leader] = currentTerm[leader]
    BY ContinuingLeaderKeepsTerm DEF ClusterAgreeProofInv
<1>before. leader \in ClusterReplicated(entry.index, entry.term)
    BY <1>term DEF ClusterAgreeProofInv, ClusterAgreeSupportInv,
        LeaderClusterAgreeInv, ClusterReplicated
<1>client. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    <2> PICK i \in Server, v \in Value: ClientRequest(i, v)
        BY <1>client
    <2>types. /\ log \in [Server -> Seq(LogEntry)]
                /\ [term |-> currentTerm[i], value |-> v] \in LogEntry
                /\ entry.index \in DOMAIN log[leader]
                /\ log[leader][entry.index].term = entry.term
        BY <1>before DEF ClusterAgreeProofInv, InductiveInvariant,
            TypeOK, LogVarsTypeOK, ServerVarsTypeOK, LogEntry, ClusterReplicated
    <2>other. CASE leader # i
        BY <2>other, <2>types DEF ClientRequest
    <2>same. CASE leader = i
        BY <2>same, <2>types, AppendProperties, LenProperties DEF ClientRequest
    <2> QED BY <2>other, <2>same
<1>append. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>append, <1>before, CompatibleAppendPreservesClusterReplicas
    DEF ClusterAgreeProofInv, ClusterAgreeSupportInv, ClusterReplicated
<1>unchanged. CASE UNCHANGED log
    BY <1>unchanged, <1>before DEF ClusterReplicated
<1> QED BY <1>client, <1>append, <1>unchanged
    DEF Next, vars, Restart, Timeout, BecomeLeader, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse, HandleAppendEntriesResponse

LEMMA ProtectedReplicaPrefixNext ==
    InductiveInvariant /\ [Next]_vars =>
        \A anchor \in Server: \A endpoint \in DOMAIN log[anchor]:
            (\A m \in AppendRequests:
                log[anchor][endpoint].term <= m.mterm =>
                    AppendRequestPrefixCompatible(m, log[anchor], endpoint))
            => /\ endpoint \in DOMAIN log'[anchor]
               /\ SubSeq(log'[anchor], 1, endpoint) = SubSeq(log[anchor], 1, endpoint)
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    NEW anchor \in Server, NEW endpoint \in DOMAIN log[anchor],
                    \A m \in AppendRequests:
                        log[anchor][endpoint].term <= m.mterm =>
                            AppendRequestPrefixCompatible(m, log[anchor], endpoint)
             PROVE /\ endpoint \in DOMAIN log'[anchor]
                   /\ SubSeq(log'[anchor], 1, endpoint) = SubSeq(log[anchor], 1, endpoint)
    OBVIOUS
<1>types. /\ log \in [Server -> Seq(LogEntry)]
           /\ endpoint \in 1..Len(log[anchor])
    BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>client. CASE \E leader \in Server, value \in Value: ClientRequest(leader, value)
    <2> PICK leader \in Server, value \in Value: ClientRequest(leader, value)
        BY <1>client
    <2>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
        BY DEF InductiveInvariant, TypeOK, ServerVarsTypeOK, LogEntry
    <2>same. CASE anchor = leader
        <3>shape. log'[anchor] =
                Append(log[anchor], [term |-> currentTerm[leader], value |-> value])
            BY <2>same, <1>types DEF ClientRequest
        <3>domain. endpoint \in DOMAIN log'[anchor]
            BY <1>types, <2>newEntry, <3>shape, AppendProperties, LenProperties
        <3>prefix. SubSeq(log'[anchor], 1, endpoint) = SubSeq(log[anchor], 1, endpoint)
            BY <1>types, <2>newEntry, <3>shape, AppendRetainsLogPrefix
        <3> QED BY <3>domain, <3>prefix
    <2>other. CASE anchor # leader
        BY <2>other, <1>types DEF ClientRequest
    <2> QED BY <2>same, <2>other
<1>append. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    <2> PICK m \in messages:
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        BY <1>append
    <2>messageTypes. /\ m.mdest \in Server /\ m.msource \in Server
        BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>other. CASE anchor # m.mdest
        BY <2>other, <1>types, <2>messageTypes DEF HandleAppendEntriesRequest
    <2>unchanged. CASE log' = log
        BY <2>unchanged
    <2>changed. CASE anchor = m.mdest /\ log' # log
        <3>term. /\ m.mterm = currentTerm[anchor]
                  /\ log[anchor][endpoint].term <= m.mterm
            BY <2>changed, <1>types, <2>messageTypes, SMT
            DEF HandleAppendEntriesRequest, InductiveInvariant, LogTermBoundInv
        <3>compatible. AppendRequestPrefixCompatible(m, log[anchor], endpoint)
            BY <3>term DEF AppendRequests
        <3> QED BY <2>changed, <3>compatible, AppendRequestPreservesCompatiblePrefix
    <2> QED BY <2>other, <2>unchanged, <2>changed
<1>unchanged. CASE log' = log
    BY <1>unchanged
<1> QED BY <1>client, <1>append, <1>unchanged, LogChangingActionNext

LEMMA HistoricalRequestsRetainClusterAgreeCompatibility ==
    ClusterAgreeProofInv /\ [Next]_vars =>
        \A request \in AppendRequests: \A entry \in ClusterAgreeEntries:
            entry.term <= request.mterm =>
                \A server \in ClusterReplicated(entry.index, entry.term)':
                    AppendRequestPrefixCompatible(request, log'[server], entry.index)
<1> SUFFICES ASSUME ClusterAgreeProofInv, [Next]_vars,
                    NEW request \in AppendRequests, NEW entry \in ClusterAgreeEntries,
                    entry.term <= request.mterm,
                    NEW server \in ClusterReplicated(entry.index, entry.term)'
             PROVE AppendRequestPrefixCompatible(request, log'[server], entry.index)
    OBVIOUS
<1> PICK anchor \in Server:
        /\ entry.index \in DOMAIN log[anchor]
        /\ log[anchor][entry.index].term = entry.term
    BY DEF ClusterAgreeEntries, ClusterEntries
<1>replica. anchor \in ClusterReplicated(entry.index, entry.term)
    BY DEF ClusterReplicated
<1>protected. \A m \in AppendRequests:
        log[anchor][entry.index].term <= m.mterm =>
            AppendRequestPrefixCompatible(m, log[anchor], entry.index)
    BY <1>replica
    DEF ClusterAgreeProofInv, ClusterAgreeSupportInv, ClusterAgreeAppendInv
<1>retained. /\ entry.index \in DOMAIN log'[anchor]
              /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    BY <1>protected, ProtectedReplicaPrefixNext DEF ClusterAgreeProofInv
<1>types. /\ log \in [Server -> Seq(LogEntry)]
           /\ log' \in [Server -> Seq(LogEntry)]
           /\ entry.index \in Nat \ {0}
           /\ request.mprevLogIndex \in Nat
           /\ request.mentries \in Seq(LogEntry)
    BY TypeOKNext, MessageFieldsTypeOK, LenProperties
    DEF ClusterAgreeProofInv, InductiveInvariant, TypeOK, LogVarsTypeOK,
        MsgTypeOK, AppendRequests, ClusterReplicated
<1>bounds. /\ entry.index \in 1..Len(log[anchor])
            /\ entry.index \in 1..Len(log'[anchor])
            /\ entry.index \in 1..Len(log'[server])
    BY <1>types, <1>retained, LenProperties DEF ClusterReplicated
<1>endpoint. log'[anchor][entry.index] = log[anchor][entry.index]
    BY <1>types, <1>retained, <1>bounds, EqualLogPrefixesEntryEqual
<1>matching. LogMatchingInv'
    BY LogMatchingInvNext DEF ClusterAgreeProofInv
<1>shared. SubSeq(log'[anchor], 1, entry.index) = SubSeq(log'[server], 1, entry.index)
    BY <1>matching, <1>endpoint, <1>bounds DEF LogMatchingInv, ClusterReplicated
<1>overlap. CASE request.mprevLogIndex < entry.index /\ request.mentries # << >>
    <2>index. request.mprevLogIndex + 1 \in 1..entry.index
        BY <1>types, <1>overlap, SMT
    <2>payload. request.mentries[1].term = log[anchor][request.mprevLogIndex + 1].term
        BY <1>protected, <1>overlap DEF AppendRequestPrefixCompatible
    <2>retained. log'[anchor][request.mprevLogIndex + 1] =
            log[anchor][request.mprevLogIndex + 1]
        BY <1>types, <1>retained, <1>bounds, <2>index, EqualLogPrefixesEntryEqual
    <2>matched. log'[anchor][request.mprevLogIndex + 1] =
            log'[server][request.mprevLogIndex + 1]
        BY <1>types, <1>shared, <1>bounds, <2>index, EqualLogPrefixesEntryEqual
    <2> QED BY <2>payload, <2>retained, <2>matched DEF AppendRequestPrefixCompatible
<1> QED BY <1>overlap DEF AppendRequestPrefixCompatible

LEMMA NewRequestsRespectClusterAgreePrefixes ==
    ClusterAgreeProofInv /\ [Next]_vars =>
        \A request \in AppendRequests' \ AppendRequests:
            \A entry \in ClusterAgreeEntries:
                entry.term <= request.mterm =>
                    \A server \in ClusterReplicated(entry.index, entry.term)':
                        AppendRequestPrefixCompatible(request, log'[server], entry.index)
<1> SUFFICES ASSUME ClusterAgreeProofInv, [Next]_vars,
                    NEW request \in AppendRequests' \ AppendRequests,
                    NEW entry \in ClusterAgreeEntries,
                    entry.term <= request.mterm,
                    NEW server \in ClusterReplicated(entry.index, entry.term)'
             PROVE AppendRequestPrefixCompatible(request, log'[server], entry.index)
    OBVIOUS
<1> PICK leader, recipient \in Server:
        /\ AppendEntries(leader, recipient)
        /\ request = AppendEntriesMessage(leader, recipient)
    BY NewAppendRequestOrigin, SMT
    DEF ClusterAgreeProofInv, AppendRequests
<1>unchanged. log' = log
    BY DEF AppendEntries
<1>serverEntry. /\ entry.index \in DOMAIN log[server]
                 /\ log[server][entry.index].term = entry.term
    BY <1>unchanged DEF ClusterReplicated
<1>types. /\ log[leader] \in Seq(LogEntry)
          /\ log[server] \in Seq(LogEntry)
          /\ request.mentries \in Seq(LogEntry)
          /\ request.mprevLogIndex \in Nat
          /\ entry.index \in Nat \ {0}
    BY AppendEntriesEntriesTypeOK
    DEF ClusterAgreeProofInv, InductiveInvariant, TypeOK, LogVarsTypeOK,
        LeaderVarsTypeOK, AppendEntriesMessage, 
        ClusterReplicated, ClusterEntries, ClusterAgreeEntries, ClusterAgree
<1>term. entry.term <= currentTerm[leader]
    BY DEF AppendEntriesMessage
<1>leaderEntry. /\ entry.index \in DOMAIN log[leader]
                 /\ log[leader][entry.index].term = entry.term
    BY <1>term
    DEF AppendEntries, ClusterAgreeProofInv, ClusterAgreeSupportInv,
        LeaderClusterAgreeInv
<1>matching. /\ LogMatchingInv /\ leader \in Server /\ server \in Server
    BY DEF ClusterAgreeProofInv, ClusterReplicated
<1>prefix. /\ entry.index \in 1..Len(log[leader])
           /\ entry.index \in 1..Len(log[server])
           /\ log[leader][entry.index].term = log[server][entry.index].term
           /\ SubSeq(log[leader], 1, entry.index) = SubSeq(log[server], 1, entry.index)
    BY ONLY <1>leaderEntry, <1>serverEntry, <1>types, <1>matching, LenProperties
    DEF LogMatchingInv
<1>compatible. CASE /\ request.mprevLogIndex < entry.index
                    /\ request.mentries # << >>
    <2>first. 1 \in DOMAIN request.mentries
        BY <1>compatible, <1>types, EmptySeq, ElementOfSeq, LenProperties, SMT
    <2>payload. request.mentries[1] = log[leader][request.mprevLogIndex + 1]
        BY <2>first, AppendEntriesSenderSnapshot
        DEF ClusterAgreeProofInv
    <2>matched. log[leader][request.mprevLogIndex + 1]
                = log[server][request.mprevLogIndex + 1]
        BY <1>prefix, <1>leaderEntry, <1>serverEntry, <1>types, <1>compatible,
            EqualLogPrefixesEntryEqual, ElementOfSeq, SMT
    <2> QED BY <2>payload, <2>matched, <1>unchanged, SMT
        DEF AppendRequestPrefixCompatible
<1> QED BY <1>compatible DEF AppendRequestPrefixCompatible

LEMMA LeaderCompletenessInductionImpliesElectionSupport ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv =>
        ClusterAgreeCandidateProofInv
    BY GrantTermBoundFromSendInvariant,
        HistoricalSameTermBoundaryImpliesIntervals,
        HistoricalBoundaryImpliesCandidateNewerPrefixes
    DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv,
        CandidateEntryAuxiliaryInv, CandidateEntryJointInv,
        ClusterAgreeCandidateProofInv

LEMMA LeaderCompletenessInductionImpliesNewLeaderCompleteness ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv =>
        NewLeaderCandidateEntryCompleteness
    BY LeaderCompletenessInductionImpliesElectionSupport,
        ElectedLeaderContainsClusterAgreeCandidateEntries
    DEF NewLeaderCandidateEntryCompleteness, LogHasTermAt

LEMMA RequestAcknowledgmentAnchorInit == Init => RequestAcknowledgmentAnchorInv
    BY DEF Init, AppendRequests, RequestAcknowledgmentAnchorInv

LEMMA RequestAcknowledgmentAnchorNext ==
    /\ CandidateEntryBaseInv /\ ActiveAppendRequestSnapshotInv
    /\ RequestAcknowledgmentAnchorInv /\ [Next]_vars
    => RequestAcknowledgmentAnchorInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, ActiveAppendRequestSnapshotInv,
                    RequestAcknowledgmentAnchorInv, [Next]_vars,
                    NEW request \in AppendRequests', NEW entry \in HistoricalEntryKeys',
                    entry.term = request.mterm,
                    entry.index = request.mprevLogIndex + Len(request.mentries)
             PROVE IF request.mentries = << >>
                   THEN request.mprevLogTerm = entry.term
                   ELSE request.mentries[1].term = entry.term
    BY DEF RequestAcknowledgmentAnchorInv
<1>types. /\ request.msource \in Server /\ request.mterm \in Nat
            /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
            /\ log \in [Server -> Seq(LogEntry)] /\ currentTerm \in [Server -> Nat]
    BY MessageFieldsTypeOK, TypeOKNext
    DEF CandidateEntryBaseInv, AppendRequests, InductiveInvariant, TypeOK,
        MsgTypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>new. CASE request \notin messages
    <2> PICK leader, recipient \in Server:
            /\ AppendEntries(leader, recipient)
            /\ request = AppendEntriesMessage(leader, recipient)
        BY <1>new, NewAppendRequestOrigin DEF CandidateEntryBaseInv, AppendRequests
    <2>keyOld. entry \in HistoricalEntryKeys
        BY EntryEdgeAppendSendSubset
        DEF CandidateEntryBaseInv, HistoricalEntryKeys
    <2> PICK edge \in HistoricalEntryEdges:
            entry = [index |-> edge.index, term |-> edge.term]
        BY <2>keyOld DEF HistoricalEntryKeys
    <2>term. edge.term = currentTerm[leader]
        BY DEF AppendEntriesMessage
    <2> PICK owner \in Server: TermOwner(owner, edge.term, edge.index)
        BY HistoricalEntryEdgeHasTermOwner DEF CandidateEntryBaseInv
    <2>leaderWon. Won(leader, currentTerm[leader])
        BY ActiveLeaderWon DEF CandidateEntryBaseInv, AppendEntries
    <2>ownerWon. Won(owner, currentTerm[leader]) BY <2>term DEF TermOwner
    <2>termType. currentTerm[leader] \in Nat BY <1>types
    <2>ownerSame. owner = leader
        BY <2>termType, <2>ownerWon, <2>leaderWon, WonUnique
        DEF CandidateEntryBaseInv, InductiveInvariant
    <2>owner.
        /\ edge.index \in DOMAIN log[leader]
        /\ log[leader][edge.index].term = currentTerm[leader]
        BY <2>ownerSame, <2>term
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, ServerVarsTypeOK,
            AppendEntries, TermOwner, OwnerActive, LogHasTermAt
    <2>snapshot.
        LET r == AppendEntriesMessage(leader, recipient) IN
        /\ r.mprevLogIndex > 0 => log[leader][r.mprevLogIndex].term = r.mprevLogTerm
        /\ \A offset \in DOMAIN r.mentries:
               r.mentries[offset] = log[leader][r.mprevLogIndex + offset]
        BY AppendEntriesSenderSnapshot DEF CandidateEntryBaseInv
    <2>empty. CASE request.mentries = << >>
        BY <2>empty, <2>owner, <2>snapshot, <1>types, LenProperties, SMT
        DEF AppendEntriesMessage
    <2>nonempty. CASE request.mentries # << >>
        <3>nextType. nextIndex[leader][recipient] \in Nat
            BY DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LeaderVarsTypeOK
        <3>start. /\ nextIndex[leader][recipient] >= 1
                   /\ nextIndex[leader][recipient] <= Len(log[leader]) + 1
            BY DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
                LeaderVarsTypeOK, MatchIndexBelowNextIndex, NextIndexBound, AppendEntries
        <3>lengthType. Len(log[leader]) \in Nat BY <1>types, LenProperties
        <3>endpoint.
            AppendEntriesLastEntry(leader, recipient) \in Nat
            /\ AppendEntriesLastEntry(leader, recipient) <= nextIndex[leader][recipient]
            /\ AppendEntriesLastEntry(leader, recipient) <= Len(log[leader])
            BY <3>nextType, <3>lengthType, SMT DEF AppendEntriesLastEntry, Min
        <3>length.
            Len(request.mentries) =
                IF nextIndex[leader][recipient] <= AppendEntriesLastEntry(leader, recipient)
                THEN AppendEntriesLastEntry(leader, recipient) - nextIndex[leader][recipient] + 1
                ELSE 0
            BY <1>types, <3>start, <3>nextType, <3>endpoint, SubSeqProperties
            DEF AppendEntriesMessage, AppendEntriesEntries
        <3>nonzero. Len(request.mentries) > 0
            BY <1>types, <2>nonempty, EmptySeq, LenProperties, SMT
        <3>single. Len(request.mentries) = 1
            BY <3>length, <3>endpoint, <3>nextType, <3>nonzero, SMT
        <3>first. 1 \in DOMAIN request.mentries BY <1>types, <3>single, LenProperties
        <3>index. edge.index = request.mprevLogIndex + 1 BY <3>single
        <3>payload. request.mentries[1] = log[leader][edge.index]
            BY <3>first, <3>index, <2>snapshot
        <3>term. entry.term = currentTerm[leader]
            BY <2>term
        <3> QED BY <3>payload, <2>owner, <3>term, <2>nonempty
    <2> QED BY <2>empty, <2>nonempty
<1>old. CASE request \in messages
    <2>oldKey. CASE entry \in HistoricalEntryKeys
        BY <2>oldKey, <1>old DEF RequestAcknowledgmentAnchorInv, AppendRequests
    <2>fresh. CASE entry \notin HistoricalEntryKeys
        <3>client. \E leader \in Server, value \in Value: ClientRequest(leader, value)
            BY <2>fresh, EntryEdgeAppendSendSubset, EntryEdgeAppendReceiveSubset, EntryEdgeOtherSubset
            DEF CandidateEntryBaseInv, HistoricalEntryKeys
        <3> PICK leader \in Server, value \in Value: ClientRequest(leader, value) BY <3>client
        <3> DEFINE edge == LogEntryEdge(log'[leader], Len(log[leader]) + 1)
        <3>key. entry = [index |-> edge.index, term |-> edge.term]
            BY <2>fresh, ClientHistoricalEntryEdges
            DEF CandidateEntryBaseInv, HistoricalEntryKeys, edge
        <3>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
            BY <1>types DEF LogEntry
        <3>freshKey. /\ edge.index = Len(log[leader]) + 1 /\ edge.term = currentTerm[leader]
            BY <1>types, <3>newEntry, AppendProperties
            DEF edge, ClientRequest, LogEntryEdge
        <3>won. Won(leader, currentTerm[leader]) BY ActiveLeaderWon DEF CandidateEntryBaseInv, ClientRequest
        <3>preRequest. request \in AppendRequests BY <1>old DEF AppendRequests
        <3>requestWon. Won(request.msource, request.mterm)
            BY <3>preRequest DEF CandidateEntryBaseInv, AppendRequestSenderWonInv
        <3>term. request.mterm = currentTerm[leader] BY <3>key, <3>freshKey
        <3>sender. request.msource = leader
            BY <1>types, <3>term, <3>requestWon, <3>won, WonUnique
            DEF CandidateEntryBaseInv, InductiveInvariant
        <3>bound. request.mprevLogIndex + Len(request.mentries) <= Len(log[leader])
            BY <3>preRequest, <3>sender, <3>term
            DEF AppendRequests, CandidateEntryBaseInv, InductiveInvariant, RequestIndexBound, ClientRequest
        <3>length. Len(log[leader]) \in Nat BY <1>types, LenProperties
        <3> QED BY <3>bound, <3>key, <3>freshKey, <3>length, SMT
    <2> QED BY <2>oldKey, <2>fresh
<1> QED BY <1>new, <1>old

LEMMA CandidateEntryAuxiliaryInit == Init => CandidateEntryAuxiliaryInv
    BY PositiveVoteRequestOriginInit, CandidateSnapshotInit, ActiveAppendSnapshotInit,
        VoteRequestsUniformInit, RequestAcknowledgmentAnchorInit
    DEF CandidateEntryAuxiliaryInv

LEMMA CandidateEntryAuxiliaryNext ==
    CandidateEntryBaseInv /\ CandidateEntryAuxiliaryInv /\ [Next]_vars =>
        CandidateEntryAuxiliaryInv'
    BY PositiveVoteRequestOriginNext, CandidateSnapshotNext, ActiveAppendSnapshotNext,
        VoteRequestsUniformNext, RequestAcknowledgmentAnchorNext
    DEF CandidateEntryBaseInv, CandidateEntryAuxiliaryInv

LEMMA CandidateEntryEvidenceRetainedNext ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        CandidateEntryEvidenceRetainedInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                    [Next]_vars, NEW entry \in ClusterAgreeCandidateEntries',
                    NEW server \in Server,
                    EntryAgreementEvidence(server, entry.index, entry.term)'
             PROVE LogHasTermAt(server, entry.term, entry.index)'
    BY DEF CandidateEntryEvidenceRetainedInv
<1>oldKey. CASE entry \in HistoricalEntryKeys
    <2>eligible. entry \in ClusterAgreeCandidateEntries
        BY <1>oldKey, ExistingHistoricalKeysCannotBecomeEligible
        DEF CandidateEntryBaseInv
    <2>types. /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
               /\ log \in [Server -> Seq(LogEntry)]
               /\ log' \in [Server -> Seq(LogEntry)]
        BY <1>oldKey, HistoricalEntryKeyHasWinner, TypeOKNext
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>retain. EntryAgreementEvidence(server, entry.index, entry.term) =>
            LogHasTermAt(server, entry.term, entry.index)'
        <3> SUFFICES ASSUME EntryAgreementEvidence(server, entry.index, entry.term)
                     PROVE LogHasTermAt(server, entry.term, entry.index)'
            OBVIOUS
        <3>replica. /\ entry.index \in DOMAIN log[server]
                     /\ log[server][entry.index].term = entry.term
            BY <2>eligible
            DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
                CandidateEntryEvidenceRetainedInv, LogHasTermAt
        <3>compatible. \A request \in AppendRequests:
                log[server][entry.index].term <= request.mterm =>
                    AppendRequestPrefixCompatible(request, log[server], entry.index)
            BY <2>eligible, <3>replica
            DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
                CandidateAppendPrefixInv, ClusterReplicated, AppendRequestPrefixCompatible
        <3>prefix. /\ entry.index \in DOMAIN log'[server]
                    /\ SubSeq(log'[server], 1, entry.index)
                          = SubSeq(log[server], 1, entry.index)
            BY <3>replica, <3>compatible, ProtectedReplicaPrefixNext
            DEF CandidateEntryBaseInv
        <3>bounds. /\ entry.index <= Len(log[server])
                    /\ entry.index <= Len(log'[server])
                    /\ entry.index \in 1..entry.index
            BY <2>types, <3>replica, <3>prefix, LenProperties, SMT
        <3>same. log'[server][entry.index] = log[server][entry.index]
            BY <2>types, <3>prefix, <3>bounds, EqualLogPrefixesEntryEqual
        <3> QED BY <3>replica, <3>prefix, <3>same DEF LogHasTermAt
    <2>oldEvidence. CASE EntryAgreementEvidence(server, entry.index, entry.term)
        BY <2>oldEvidence, <2>retain
    <2>winner. CASE Won(server, entry.term)'
        <3> PICK owner \in Server: TermOwner(owner, entry.term, entry.index)
            BY <1>oldKey, HistoricalEntryKeyHasWinner DEF CandidateEntryBaseInv
        <3>record. VoteRecordInv'
            BY VoteRecordInvNext DEF CandidateEntryBaseInv
        <3>won. Won(owner, entry.term)'
            BY WonMonotonicNext DEF CandidateEntryBaseInv, TermOwner
        <3>same. owner = server
            BY <2>types, <2>winner, <3>record, <3>won, WonUniqueNextState
        <3>evidence. EntryAgreementEvidence(server, entry.index, entry.term)
            BY <3>same DEF TermOwner, EntryAgreementEvidence
        <3> QED BY <2>retain, <3>evidence
    <2>newAck. CASE /\ ~EntryAgreementEvidence(server, entry.index, entry.term)
                      /\ ~Won(server, entry.term)'
        <3> PICK response \in messages' \ messages:
                /\ response.mtype = AppendEntriesResponse /\ response.msuccess
                /\ response.msource = server /\ response.mterm = entry.term
                /\ response.mmatchIndex = entry.index
            BY <2>newAck DEF EntryAgreementEvidence
        <3> QED BY <1>oldKey, NewSuccessfulAppendResponseLogAnchor
            DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                CandidateEntryAuxiliaryInv
    <2> QED BY <2>oldEvidence, <2>winner, <2>newAck
<1>fresh. CASE entry \notin HistoricalEntryKeys
    <2> PICK leader \in Server, value \in Value:
            /\ ClientRequest(leader, value)
            /\ entry.index = Len(log[leader]) + 1
            /\ entry.term = currentTerm[leader]
            /\ entry = [index |-> Len(log[leader]) + 1,
                         term |-> currentTerm[leader]]
        BY <1>fresh, FreshCandidateEntryOriginNext
    <2>types. /\ currentTerm[leader] \in Nat
               /\ log[leader] \in Seq(LogEntry)
               /\ Len(log[leader]) \in Nat
               /\ log \in [Server -> Seq(LogEntry)]
        BY LenProperties
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
            ServerVarsTypeOK, LogVarsTypeOK
    <2>client. /\ state[leader] = Leader /\ messages' = messages
                /\ entry.index = Len(log[leader]) + 1
                /\ entry.term = currentTerm[leader]
        BY DEF ClientRequest
    <2>votes. \A candidate \in Server: Won(candidate, entry.term)' = Won(candidate, entry.term)
        BY <2>client DEF Won, Started, VoteFor, Grant
    <2>leaderWon. Won(leader, entry.term)
        BY <2>client, ActiveLeaderWon DEF CandidateEntryBaseInv
    <2>winner. CASE Won(server, entry.term)'
        <3>won. Won(server, entry.term) BY <2>votes, <2>winner
        <3>same. server = leader
            BY <2>types, <2>client, <2>leaderWon, <3>won, WonUnique
            DEF CandidateEntryBaseInv, InductiveInvariant
        <3>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
            BY <2>types DEF LogEntry
        <3>clientLog. log'[leader] =
                Append(log[leader], [term |-> currentTerm[leader], value |-> value])
            BY <2>types DEF ClientRequest
        <3>entry. /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index] =
                         [term |-> currentTerm[leader], value |-> value]
            BY <2>types, <2>client, <3>newEntry, <3>clientLog,
                AppendProperties, LenProperties
        <3> QED BY <2>client, <3>same, <3>entry DEF LogHasTermAt
    <2>ack. CASE ~Won(server, entry.term)'
        <3> PICK response \in messages:
                /\ response.mtype = AppendEntriesResponse /\ response.msuccess
                /\ response.msource = server /\ response.mterm = entry.term
                /\ response.mmatchIndex = entry.index
            BY <2>client, <2>ack DEF EntryAgreementEvidence
        <3>recipientType. response.mdest \in Server
            BY MessageFieldsTypeOK
            DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK
        <3>recipientWon. Won(response.mdest, entry.term)
            BY DEF CandidateEntryBaseInv, SuccessfulResponseRecipientWonInv
        <3>recipient. response.mdest = leader
            BY <2>types, <2>client, <2>leaderWon, <3>recipientType,
                <3>recipientWon, WonUnique
            DEF CandidateEntryBaseInv, InductiveInvariant
        <3>bound. entry.index <= Len(log[leader])
            BY <2>client, <3>recipient
            DEF CandidateEntryBaseInv, InductiveInvariant, ResponseIndexBound
        <3> QED BY <2>types, <2>client, <3>bound, SMT
    <2> QED BY <2>winner, <2>ack
<1> QED BY <1>oldKey, <1>fresh

LEMMA CandidateAppendPrefixNext ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        CandidateAppendPrefixInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                    [Next]_vars, NEW request \in AppendRequests',
                    NEW entry \in ClusterAgreeCandidateEntries',
                    entry.term <= request.mterm,
                    NEW server \in ClusterReplicated(entry.index, entry.term)',
                    request.mprevLogIndex < entry.index,
                    request.mentries # << >>
             PROVE request.mentries[1].term =
                    log'[server][request.mprevLogIndex + 1].term
    BY DEF CandidateAppendPrefixInv, AppendRequestPrefixCompatible
<1>types. /\ request.msource \in Server /\ request.mterm \in Nat
           /\ request.mprevLogIndex \in Nat
           /\ request.mentries \in Seq(LogEntry)
           /\ server \in Server /\ log' \in [Server -> Seq(LogEntry)]
    BY MessageFieldsTypeOK, TypeOKNext
    DEF CandidateEntryBaseInv, AppendRequests, ClusterReplicated,
        InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
<1>newRequest. CASE request \notin messages
    <2> PICK leader, recipient \in Server:
            /\ AppendEntries(leader, recipient)
            /\ request = AppendEntriesMessage(leader, recipient)
        BY <1>newRequest, NewAppendRequestOrigin
        DEF CandidateEntryBaseInv, AppendRequests
    <2>oldKey. entry \in HistoricalEntryKeys
        BY EntryEdgeAppendSendSubset
        DEF CandidateEntryBaseInv, ClusterAgreeCandidateEntries, HistoricalEntryKeys
    <2>eligible. entry \in ClusterAgreeCandidateEntries
        BY <2>oldKey, ExistingHistoricalKeysCannotBecomeEligible
        DEF CandidateEntryBaseInv
    <2>entryType. /\ entry.index \in Nat /\ entry.term \in Nat
        BY <2>oldKey, HistoricalEntryKeyHasWinner
        DEF CandidateEntryBaseInv
    <2>preTypes. /\ log[leader] \in Seq(LogEntry)
                  /\ log[server] \in Seq(LogEntry)
        BY <1>types DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>unchanged. log' = log BY DEF AppendEntries
    <2>serverEntry. /\ entry.index \in DOMAIN log[server]
                     /\ log[server][entry.index].term = entry.term
        BY <2>unchanged DEF ClusterReplicated
    <2>term. entry.term <= currentTerm[leader]
        BY DEF AppendEntriesMessage
    <2>leaderEntry. LogHasTermAt(leader, entry.term, entry.index)
        BY <2>eligible, <2>term
        DEF LeaderCompletenessInductionInv, LeaderCandidateEntryInv, AppendEntries
    <2>leaderDomain. entry.index \in DOMAIN log[leader]
        BY <2>leaderEntry DEF LogHasTermAt
    <2>serverDomain. entry.index \in DOMAIN log[server]
        BY <2>serverEntry
    <2>endpoints.
        entry.index \in (1..Len(log[leader])) \cap (1..Len(log[server]))
        BY <2>entryType, <2>preTypes, <2>leaderDomain, <2>serverDomain,
            LenProperties
    <2>sameAtEnd. log[leader][entry.index].term =
            log[server][entry.index].term
        BY <2>leaderEntry, <2>serverEntry DEF LogHasTermAt
    <2>shared. SubSeq(log[leader], 1, entry.index) =
            SubSeq(log[server], 1, entry.index)
        BY <1>types, <2>endpoints, <2>sameAtEnd
        DEF CandidateEntryBaseInv, LogMatchingInv
    <2>point. /\ request.mprevLogIndex + 1 \in Nat
                /\ request.mprevLogIndex + 1 \in 1..entry.index
        BY <1>types, <2>entryType, SMT
    <2>points. /\ request.mprevLogIndex + 1 \in DOMAIN log[leader]
                 /\ request.mprevLogIndex + 1 \in DOMAIN log[server]
        BY <2>preTypes, <2>endpoints, <2>point, LenProperties
    <2>first. 1 \in DOMAIN request.mentries
        BY <1>types, EmptySeq, LenProperties, SMT
    <2>payload. request.mentries[1] =
            log[leader][request.mprevLogIndex + 1]
        BY <2>first, AppendEntriesSenderSnapshot
        DEF CandidateEntryBaseInv
    <2>matched. log[leader][request.mprevLogIndex + 1] =
            log[server][request.mprevLogIndex + 1]
        BY <2>entryType, <2>preTypes, <2>endpoints, <2>point, <2>shared,
            EqualLogPrefixesEntryEqual
    <2> QED BY <2>unchanged, <2>payload, <2>matched
<1>fresh. CASE request \in messages /\ entry \notin HistoricalEntryKeys
    <2>client. \E leader \in Server, value \in Value:
                   /\ ClientRequest(leader, value)
                   /\ entry.index = Len(log[leader]) + 1
                   /\ entry.term = currentTerm[leader]
                   /\ entry = [index |-> Len(log[leader]) + 1,
                                term |-> currentTerm[leader]]
        BY <1>fresh, FreshCandidateEntryOriginNext
    <2> PICK leader \in Server, value \in Value:
            /\ ClientRequest(leader, value)
            /\ entry.index = Len(log[leader]) + 1
            /\ entry.term = currentTerm[leader]
            /\ entry = [index |-> Len(log[leader]) + 1,
                         term |-> currentTerm[leader]]
        BY <2>client
    <2>newEntry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
        BY DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
            ServerVarsTypeOK, LogEntry
    <2>stateTypes. /\ currentTerm[leader] \in Nat
                    /\ log[leader] \in Seq(LogEntry)
                    /\ Len(log[leader]) \in Nat
        BY LenProperties
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
            ServerVarsTypeOK, LogVarsTypeOK
    <2>clientLog. log'[leader] = Append(log[leader],
            [term |-> currentTerm[leader], value |-> value])
        BY <2>client, <2>stateTypes
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
            LogVarsTypeOK, ClientRequest
    <2>shape. /\ entry.index = Len(log[leader]) + 1
               /\ entry.term = currentTerm[leader]
        BY <2>client
    <2>quorum. ClusterMightAgree(Len(log[leader]) + 1,
                    currentTerm[leader]) \in Quorum
        BY <2>shape, <2>client, Isa
        DEF ClusterAgreeCandidateEntries, ClientRequest, ClusterMightAgree,
            EntryAgreementEvidence, Won, Started, VoteFor, Grant
    <2>requestBound. request.mterm <= currentTerm[leader]
        BY <1>fresh, <2>client, <2>quorum,
            FreshClientKeyHasNoLaterHistoricalRequest
        DEF CandidateEntryBaseInv, AppendRequests
    <2>sameTerm. request.mterm = currentTerm[leader]
        BY <1>types, <2>stateTypes, <2>shape, <2>requestBound, SMT
    <2>requestWon. Won(request.msource, request.mterm)
        BY <1>fresh DEF CandidateEntryBaseInv, AppendRequestSenderWonInv, AppendRequests
    <2>leaderWon. Won(leader, currentTerm[leader])
        BY ActiveLeaderWon DEF CandidateEntryBaseInv, ClientRequest
    <2>source. request.msource = leader
        BY <1>types, <2>sameTerm, <2>requestWon, <2>leaderWon, WonUnique
        DEF CandidateEntryBaseInv, InductiveInvariant
    <2>snapshot.
        \A offset \in DOMAIN request.mentries:
            request.mentries[offset] =
                log[leader][request.mprevLogIndex + offset]
        BY <2>source, <2>sameTerm
        DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv,
            CandidateEntryAuxiliaryInv, ActiveAppendRequestSnapshotInv,
            ClientRequest, AppendRequests
    <2>oldRequest. request \in AppendRequests
        BY <1>fresh DEF ClientRequest, AppendRequests
    <2>sameServer. server = leader
        <3>other. CASE server # leader
            <4>oldLog. log'[server] = log[server]
                BY <1>types, <2>client, <3>other DEF ClientRequest
            <4>oldKey. entry \in HistoricalEntryKeys
                BY <2>client, <2>shape, <4>oldLog
                DEF ClusterReplicated, HistoricalEntryKeys,
                    HistoricalEntryEdges, LogEntryEdge
            <4> QED BY <1>fresh, <4>oldKey
        <3>same. CASE server = leader BY <3>same
        <3> QED BY <3>other, <3>same
    <2>first. 1 \in DOMAIN request.mentries
        BY <1>types, EmptySeq, LenProperties, SMT
    <2>nonempty. Len(request.mentries) > 0
        BY <1>types, EmptySeq, LenProperties, SMT
    <2>requestIndex.
        request.mprevLogIndex + Len(request.mentries) <= Len(log[request.msource])
        BY <1>types, <2>oldRequest, <2>source, <2>sameTerm,
            <2>client
        DEF CandidateEntryBaseInv, InductiveInvariant, RequestIndexBound,
            AppendRequests, ClientRequest
    <2>lengthType. Len(request.mentries) \in Nat
        BY <1>types, LenProperties
    <2>requestIndexLeader.
        request.mprevLogIndex + Len(request.mentries) <= Len(log[leader])
        BY <2>requestIndex, <2>source
    <2>one. 1 <= Len(request.mentries)
        BY <2>nonempty, <2>lengthType, SMT
    <2>payloadBound.
        request.mprevLogIndex + 1 <=
            request.mprevLogIndex + Len(request.mentries)
        BY <1>types, <2>one, <2>lengthType, SMT
    <2>bound. request.mprevLogIndex + 1 <= Len(log[leader])
        BY <1>types, <2>lengthType, <2>stateTypes,
            <2>payloadBound, <2>requestIndexLeader, NatLeqTransitive
    <2>domain. request.mprevLogIndex + 1 \in DOMAIN log[leader]
        BY <1>types, <2>stateTypes, <2>bound, LenProperties
    <2>postLog. log'[leader] = Append(log[leader],
            [term |-> currentTerm[leader], value |-> value])
        BY <2>clientLog
    <2>retained. log'[leader][request.mprevLogIndex + 1] =
            log[leader][request.mprevLogIndex + 1]
        BY <2>stateTypes, <2>domain, <2>newEntry, <2>postLog,
            AppendProperties
    <2> QED BY <2>snapshot, <2>sameServer, <2>first, <2>retained
<1>old. CASE request \in messages /\ entry \in HistoricalEntryKeys
    <2>eligible. entry \in ClusterAgreeCandidateEntries
        BY <1>old, ExistingHistoricalKeysCannotBecomeEligible
        DEF CandidateEntryBaseInv
    <2>oldRequest. request \in AppendRequests
        BY <1>old DEF AppendRequests
    <2> PICK owner \in Server: TermOwner(owner, entry.term, entry.index)
        BY <1>old, HistoricalEntryKeyHasWinner DEF CandidateEntryBaseInv
    <2>ownerEntry. LogHasTermAt(owner, entry.term, entry.index)
        BY <2>eligible
        DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
            CandidateEntryEvidenceRetainedInv, EntryAgreementEvidence, TermOwner
    <2>ownerReplica. owner \in ClusterReplicated(entry.index, entry.term)
        BY <2>ownerEntry DEF ClusterReplicated, LogHasTermAt
    <2>preTypes. /\ log \in [Server -> Seq(LogEntry)]
                   /\ entry.index \in Nat \ {0} /\ entry.term \in Nat
        BY <1>old, HistoricalEntryKeyHasWinner
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>point. /\ request.mprevLogIndex + 1 \in Nat
                /\ request.mprevLogIndex + 1 \in 1..entry.index
        BY <1>types, <2>preTypes, SMT
    <2>ownerBounds. /\ entry.index \in 1..Len(log[owner])
                      /\ request.mprevLogIndex + 1 \in DOMAIN log[owner]
        BY <2>preTypes, <2>ownerEntry, <2>point, LenProperties
        DEF LogHasTermAt
    <2>payload. request.mentries[1].term =
            log[owner][request.mprevLogIndex + 1].term
        BY <2>oldRequest, <2>eligible, <2>ownerReplica
        DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
            CandidateAppendPrefixInv
    <2>retained. /\ owner \in ClusterReplicated(entry.index, entry.term)'
                   /\ log'[owner][request.mprevLogIndex + 1] =
                          log[owner][request.mprevLogIndex + 1]
        <3>compatible. \A m \in AppendRequests:
                log[owner][entry.index].term <= m.mterm =>
                    AppendRequestPrefixCompatible(m, log[owner], entry.index)
            BY <2>eligible, <2>ownerReplica, <2>ownerEntry
            DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
                CandidateAppendPrefixInv, AppendRequestPrefixCompatible, LogHasTermAt
        <3>prefix. /\ entry.index \in DOMAIN log'[owner]
                    /\ SubSeq(log'[owner], 1, entry.index) =
                           SubSeq(log[owner], 1, entry.index)
            BY <3>compatible, <2>ownerEntry, ProtectedReplicaPrefixNext
            DEF CandidateEntryBaseInv, LogHasTermAt
        <3>bounds. entry.index \in 1..Len(log'[owner])
            BY <1>types, <2>preTypes, <3>prefix, LenProperties
        <3>entries. /\ log'[owner][entry.index] = log[owner][entry.index]
                     /\ log'[owner][request.mprevLogIndex + 1] =
                            log[owner][request.mprevLogIndex + 1]
            BY <1>types, <2>preTypes, <2>point, <2>ownerBounds,
                <3>bounds, <3>prefix, EqualLogPrefixesEntryEqual
        <3> QED BY <2>ownerReplica, <3>prefix, <3>entries DEF ClusterReplicated
    <2>matching. LogMatchingInv'
        BY LogMatchingInvNext DEF CandidateEntryBaseInv
    <2>endpoints. entry.index \in
            (1..Len(log'[owner])) \cap (1..Len(log'[server]))
        BY <1>types, <2>retained, LenProperties DEF ClusterReplicated
    <2>shared. SubSeq(log'[owner], 1, entry.index) =
            SubSeq(log'[server], 1, entry.index)
        BY <2>matching, <2>retained, <2>endpoints DEF LogMatchingInv, ClusterReplicated
    <2>matched. log'[owner][request.mprevLogIndex + 1] =
            log'[server][request.mprevLogIndex + 1]
        BY <1>types, <2>preTypes, <2>point, <2>endpoints, <2>shared,
            EqualLogPrefixesEntryEqual
    <2> QED BY <2>payload, <2>retained, <2>matched
<1> QED BY <1>newRequest, <1>fresh, <1>old

LEMMA HistoricalVoteProtectionNext ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        HistoricalVoteProtectionInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                    [Next]_vars, NEW request \in messages',
                    NEW entry \in ClusterAgreeCandidateEntries',
                    request.mtype = RequestVoteRequest,
                    entry.term < request.mterm,
                    Grant(request.mdest, request.msource, request.mterm)',
                    EntryAgreementEvidence(request.mdest, entry.index, entry.term)'
             PROVE VoteRequestCoversEntry(request, entry)
    BY DEF HistoricalVoteProtectionInv
<1>support. ClusterAgreeProofInv
    BY ClusterAgreeEntriesAreCandidateEntries
    DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv,
        CandidateEntryJointInv, ClusterAgreeProofInv, ClusterAgreeSupportInv,
        LeaderClusterAgreeInv, ClusterAgreeAppendInv, LeaderCandidateEntryInv,
        CandidateAppendPrefixInv, LogHasTermAt, ClusterReplicated,
        AppendRequestPrefixCompatible
<1>auxiliary. CandidateEntryAuxiliaryInv'
    BY CandidateEntryAuxiliaryNext
    DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv
<1>types. /\ request.msource \in Server /\ request.mdest \in Server
           /\ request.mterm \in Nat
    BY MessageFieldsTypeOK, TypeOKNext
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK
<1>currentType. currentTerm[request.mdest] \in Nat
    BY <1>types
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>oldKey. CASE entry \in HistoricalEntryKeys
    <2>eligible. entry \in ClusterAgreeCandidateEntries
        BY <1>oldKey, ExistingHistoricalKeysCannotBecomeEligible
        DEF CandidateEntryBaseInv
    <2>entryType. entry.term \in Nat
        BY <1>oldKey, HistoricalEntryKeyHasWinner
        DEF CandidateEntryBaseInv
    <2>grantBound. GrantTermBoundInv
        BY GrantTermBoundFromSendInvariant DEF CandidateEntryBaseInv
    <2>oldGrant. CASE Grant(request.mdest, request.msource, request.mterm)
        <3>bound. request.mterm <= currentTerm[request.mdest]
            BY <1>types, <2>grantBound, <2>oldGrant
            DEF GrantTermBoundInv
        <3>potential. request.mdest \in ClusterMightAgree(entry.index, entry.term)
            BY <1>types, <1>oldKey, ExistingKeyPotentialAgreementCannotGrow
            DEF CandidateEntryBaseInv, ClusterMightAgree,
                EntryAgreementEvidence
        <3>lowOrEvidence.
            \/ currentTerm[request.mdest] <= entry.term
            \/ EntryAgreementEvidence(request.mdest, entry.index, entry.term)
            BY <3>potential DEF ClusterMightAgree
        <3>notLow. ~(currentTerm[request.mdest] <= entry.term)
            BY <1>types, <1>currentType, <2>entryType, <3>bound, SMT
        <3>evidence. EntryAgreementEvidence(request.mdest, entry.index, entry.term)
            BY <3>lowOrEvidence, <3>notLow
        <3> PICK anchor \in messages:
                /\ anchor.mtype = RequestVoteRequest
                /\ anchor.msource = request.msource
                /\ anchor.mdest = request.mdest
                /\ anchor.mterm = request.mterm
            BY <2>oldGrant
            DEF LeaderCompletenessInductionInv, CandidateEntryAuxiliaryInv,
                PositiveVoteRequestOriginInv, Grant
        <3>covered. VoteRequestCoversEntry(anchor, entry)
            BY <1>types, <2>entryType, <2>eligible, <2>oldGrant,
                <3>evidence, SMT
            DEF LeaderCompletenessInductionInv, CandidateEntryJointInv,
                HistoricalVoteProtectionInv
        <3>same. /\ anchor.mlastLogTerm = request.mlastLogTerm
                  /\ anchor.mlastLogIndex = request.mlastLogIndex
            BY <1>auxiliary, MessagesMonotonicNext
            DEF CandidateEntryAuxiliaryInv, VoteRequestsUniformInv
        <3> QED BY <3>covered, <3>same DEF VoteRequestCoversEntry
    <2>newGrant. CASE ~Grant(request.mdest, request.msource, request.mterm)
        <3> PICK response \in messages' \ messages:
                /\ response.mtype = RequestVoteResponse
                /\ response.mterm = request.mterm
                /\ response.mvoteGranted
                /\ response.msource = request.mdest
                /\ response.mdest = request.msource
            BY <2>newGrant DEF Grant
        <3>receive. \E inbound \in messages: Receive(inbound)
            <4>frame. CASE UNCHANGED messages
                BY <4>frame
            <4>timeout. CASE \E server \in Server: Timeout(server)
                <5> PICK server \in Server: Timeout(server) BY <4>timeout
                <5>new. response \in RequestVoteRequests(server,
                        currentTerm[server] + 1)
                    BY DEF Timeout, WithMessages
                <5>requestType. response.mtype = RequestVoteRequest
                    BY <5>new DEF RequestVoteRequests
                <5> QED BY <5>requestType, MessageTypesDistinct
            <4>append. CASE \E leader, recipient \in Server:
                    AppendEntries(leader, recipient)
                <5> PICK leader, recipient \in Server:
                        AppendEntries(leader, recipient)
                    BY <4>append
                <5>new. response = AppendEntriesMessage(leader, recipient)
                    BY DEF AppendEntries, Send, WithMessage, WithMessages
                <5>requestType. response.mtype = AppendEntriesRequest
                    BY <5>new DEF AppendEntriesMessage
                <5> QED BY <5>requestType, MessageTypesDistinct
            <4>receive. CASE \E inbound \in messages: Receive(inbound)
                BY <4>receive
            <4> QED BY <4>frame, <4>timeout, <4>append, <4>receive
                DEF Next, vars, Restart, BecomeLeader, ClientRequest,
                    AdvanceCommitIndex, LeaderStepDown
        <3> PICK inbound \in messages: Receive(inbound) BY <3>receive
        <3>handled. /\ inbound.mtype = RequestVoteRequest
                       /\ HandleRequestVoteRequest(inbound.mdest,
                              inbound.msource, inbound)
            BY <2>newGrant, MessageFieldsTypeOK, MessageTypesDistinct, SMTT(60)
            DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
                Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest,
                HandleAppendEntriesResponse, Grant, Send, WithMessage, WithMessages
        <3>sameGrant. /\ inbound.msource = request.msource
                       /\ inbound.mdest = request.mdest
                       /\ inbound.mterm = request.mterm
            BY <2>newGrant, <3>handled, MessageFieldsTypeOK,
                MessageTypesDistinct, SMTT(60)
            DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
                HandleRequestVoteRequest, Grant, Send, WithMessage, WithMessages
        <3>evidence. EntryAgreementEvidence(inbound.mdest, entry.index, entry.term)
            BY <1>types, <2>entryType, <3>handled, <3>sameGrant,
                MessageFieldsTypeOK, MessageTypesDistinct, SMTT(60)
            DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
                EntryAgreementEvidence, Won, Started, VoteFor, Grant,
                HandleRequestVoteRequest, Send, WithMessage, WithMessages
        <3>covered. VoteRequestCoversEntry(inbound, entry)
            BY <1>support, <1>types, <2>entryType, <2>eligible,
                <2>newGrant, <3>handled, <3>sameGrant, <3>evidence,
                GrantingVoterForcesCoveringRequest, SMT
            DEF LeaderCompletenessInductionInv, CandidateEntryJointInv
        <3>same. /\ inbound.mlastLogTerm = request.mlastLogTerm
                  /\ inbound.mlastLogIndex = request.mlastLogIndex
            BY <1>auxiliary, <3>handled, <3>sameGrant,
                MessagesMonotonicNext
            DEF CandidateEntryAuxiliaryInv, VoteRequestsUniformInv
        <3> QED BY <3>covered, <3>same DEF VoteRequestCoversEntry
    <2> QED BY <2>oldGrant, <2>newGrant
<1>fresh. CASE entry \notin HistoricalEntryKeys
    <2>client. \E leader \in Server, value \in Value:
                   /\ ClientRequest(leader, value)
                   /\ entry.index = Len(log[leader]) + 1
                   /\ entry.term = currentTerm[leader]
        BY <1>fresh, FreshCandidateEntryOriginNext
    <2> PICK leader \in Server, value \in Value:
            /\ ClientRequest(leader, value)
            /\ entry.index = Len(log[leader]) + 1
            /\ entry.term = currentTerm[leader]
        BY <2>client
    <2>shape. /\ entry.index = Len(log[leader]) + 1
               /\ entry.term = currentTerm[leader]
        BY <2>client
    <2>oldFacts. /\ request \in messages
                  /\ Grant(request.mdest, request.msource, request.mterm)
                  /\ EntryAgreementEvidence(request.mdest, entry.index, entry.term)
        BY MessageFieldsTypeOK, MessageTypesDistinct, SMTT(60)
        DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
            ClientRequest, EntryAgreementEvidence, Won, Started, VoteFor, Grant
    <2> QED BY <2>shape, <2>oldFacts,
        FreshClientKeyHasNoHigherTermVoteEvidence
        DEF CandidateEntryBaseInv
<1> QED BY <1>oldKey, <1>fresh

LEMMA LeaderCandidateEntryNext ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        LeaderCandidateEntryInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv, [Next]_vars,
                    NEW leader \in Server, state'[leader] = Leader,
                    NEW entry \in ClusterAgreeCandidateEntries',
                    entry.term <= currentTerm'[leader]
             PROVE LogHasTermAt(leader, entry.term, entry.index)'
    BY DEF LeaderCandidateEntryInv
<1>elected. CASE BecomeLeader(leader)
    BY <1>elected, LeaderCompletenessInductionImpliesNewLeaderCompleteness
    DEF NewLeaderCandidateEntryCompleteness
<1>persistent. CASE ~BecomeLeader(leader)
    <2>types. /\ log \in [Server -> Seq(LogEntry)]
                 /\ currentTerm \in [Server -> Nat]
                 /\ state \in [Server -> {Follower, Candidate, Leader}]
        BY DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
    <2>before. state[leader] = Leader
        BY <1>persistent, NextCreatesLeaderOnlyByElection DEF CandidateEntryBaseInv
    <2>retained.
        /\ currentTerm'[leader] = currentTerm[leader]
        /\ \A index \in DOMAIN log[leader]:
               /\ index \in DOMAIN log'[leader] /\ log'[leader][index] = log[leader][index]
        BY <2>before, PersistentLeaderRetainsLogEntries
        DEF CandidateEntryBaseInv
    <2>old. CASE entry \in HistoricalEntryKeys
        <3>eligible. entry \in ClusterAgreeCandidateEntries
            BY <2>old, ExistingHistoricalKeysCannotBecomeEligible DEF CandidateEntryBaseInv
        <3>before. LogHasTermAt(leader, entry.term, entry.index)
            BY <3>eligible, <2>before, <2>retained
            DEF LeaderCompletenessInductionInv, LeaderCandidateEntryInv
        <3> QED BY <3>before, <2>retained DEF LogHasTermAt
    <2>fresh. CASE entry \notin HistoricalEntryKeys
        <3> PICK server \in Server, value \in Value:
                /\ ClientRequest(server, value)
                /\ entry.index = Len(log[server]) + 1
                /\ entry.term = currentTerm[server]
                /\ entry = [index |-> Len(log[server]) + 1, term |-> currentTerm[server]]
            BY <2>fresh, FreshCandidateEntryOriginNext
        <3>key. entry = [index |-> Len(log[server]) + 1, term |-> currentTerm[server]]
            OBVIOUS
        <3>newEntry. [term |-> currentTerm[server], value |-> value] \in LogEntry
            BY <2>types DEF LogEntry
        <3>freshTerm. /\ entry.index = Len(log[server]) + 1 /\ entry.term = currentTerm[server]
            OBVIOUS
        <3>same. CASE server = leader
            BY <3>same, <3>key, <3>freshTerm, <2>types, <3>newEntry,
                AppendProperties, LenProperties, SMT
            DEF ClientRequest, LogHasTermAt
        <3>other. CASE server # leader
            <4>newer. currentTerm[server] < currentTerm[leader]
                <5>serverWon. Won(server, currentTerm[server])
                    BY ActiveLeaderWon DEF CandidateEntryBaseInv, ClientRequest
                <5>leaderWon. Won(leader, currentTerm[leader])
                    BY <2>before, ActiveLeaderWon DEF CandidateEntryBaseInv
                <5>sameTermImpossible. currentTerm[server] # currentTerm[leader]
                    BY <3>other, <5>serverWon, <5>leaderWon, <2>types, WonUnique
                    DEF CandidateEntryBaseInv, InductiveInvariant
                <5>termTypes. currentTerm[server] \in Nat /\ currentTerm[leader] \in Nat
                    BY <2>types
                <5> QED BY <5>sameTermImpossible, <5>termTypes,
                    <3>key, <3>freshTerm, <2>retained, SMT
            <4>quorum. ClusterMightAgree(Len(log[server]) + 1, currentTerm[server]) \in Quorum
                BY <3>key, <3>freshTerm
                DEF ClusterAgreeCandidateEntries, ClientRequest, ClusterMightAgree,
                    EntryAgreementEvidence, Won, Started, VoteFor, Grant
            <4>won. Won(leader, currentTerm[leader]) BY <2>before, ActiveLeaderWon DEF CandidateEntryBaseInv
            <4>types. /\ Len(log[server]) \in Nat /\ currentTerm[leader] \in Nat
                       /\ Len(log[server]) + 1 \in Nat
                       /\ Len(log[server]) < Len(log[server]) + 1
                BY <2>types, LenProperties, SMT
            <4>excluded.
                ClusterMightAgree(Len(log[server]) + 1, currentTerm[server]) \notin Quorum
                BY <4>types, <4>newer, <4>won, HistoricalHigherElectionExcludesUncreatedEntry
                DEF CandidateEntryBaseInv, ClientRequest
            <4> QED BY <4>excluded, <4>quorum
        <3> QED BY <3>same, <3>other
    <2> QED BY <2>old, <2>fresh
<1> QED BY <1>elected, <1>persistent

LEMMA LeaderCompletenessInductionInit == Init => LeaderCompletenessInductionInv
    BY CandidateEntryAuxiliaryInit, HistoricalNewerBoundaryInit, ServerStatesDistinct
    DEF LeaderCompletenessInductionInv, LeaderCandidateEntryInv, CandidateEntryJointInv,
        CandidateEntryEvidenceRetainedInv, CandidateAppendPrefixInv,
        HistoricalVoteProtectionInv, ClusterAgreeCandidateEntries, HistoricalEntryKeys,
        HistoricalEntryEdges, AppendRequests, Init, InitServerVars, InitLogVars

LEMMA LeaderCompletenessInductionNext ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        LeaderCompletenessInductionInv'
    BY CandidateEntryAuxiliaryNext, CandidateEntryEvidenceRetainedNext,
        CandidateAppendPrefixNext, HistoricalNewerBoundaryNext,
        HistoricalVoteProtectionNext, LeaderCandidateEntryNext
    DEF LeaderCompletenessInductionInv, CandidateEntryJointInv

LEMMA NewlyAgreedEntriesInExistingLeaders ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        \A leader \in Server:
            \A entry \in ClusterAgreeEntries' \ ClusterAgreeEntries:
                /\ state[leader] = Leader /\ state'[leader] = Leader
                /\ entry.term <= currentTerm'[leader]
                => /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index].term = entry.term
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv, [Next]_vars
             PROVE \A leader \in Server:
                \A entry \in ClusterAgreeEntries' \ ClusterAgreeEntries:
                    /\ state[leader] = Leader /\ state'[leader] = Leader
                    /\ entry.term <= currentTerm'[leader]
                    => /\ entry.index \in DOMAIN log'[leader]
                       /\ log'[leader][entry.index].term = entry.term
    OBVIOUS
<1>leader. LeaderCandidateEntryInv' BY LeaderCandidateEntryNext
<1>subset. ClusterAgreeEntries' \subseteq ClusterAgreeCandidateEntries'
    BY ClusterAgreeEntriesAreCandidateEntriesNext
<1> QED BY <1>leader, <1>subset DEF LeaderCandidateEntryInv, LogHasTermAt

LEMMA LeaderClusterAgreeInvNext ==
    ClusterAgreeProofInv /\ CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars
        => LeaderClusterAgreeInv'
<1> SUFFICES ASSUME ClusterAgreeProofInv, CandidateEntryBaseInv,
                    LeaderCompletenessInductionInv, [Next]_vars,
                    NEW leader \in Server, NEW entry \in ClusterAgreeEntries',
                    state'[leader] = Leader, entry.term <= currentTerm'[leader]
             PROVE /\ entry.index \in DOMAIN log'[leader]
                   /\ log'[leader][entry.index].term = entry.term
    BY DEF LeaderClusterAgreeInv
<1>candidate. ClusterAgreeCandidateProofInv
    BY LeaderCompletenessInductionImpliesElectionSupport
<1>election. CASE state[leader] # Leader
    BY <1>election, <1>candidate, NextCreatesLeaderOnlyByElection,
        ElectedLeaderContainsClusterAgreeEntries DEF ClusterAgreeProofInv
<1>old. CASE state[leader] = Leader /\ entry \in ClusterAgreeEntries
    BY <1>old, ExistingLeaderRetainsClusterAgreeEntries
<1>new. CASE state[leader] = Leader /\ entry \notin ClusterAgreeEntries
    BY <1>new, NewlyAgreedEntriesInExistingLeaders
<1> QED BY <1>election, <1>old, <1>new

LEMMA NewlyAgreedEntriesRespectHistoricalRequests ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
        \A request \in AppendRequests':
            \A entry \in ClusterAgreeEntries' \ ClusterAgreeEntries:
                entry.term <= request.mterm =>
                    \A server \in ClusterReplicated(entry.index, entry.term)':
                        AppendRequestPrefixCompatible(request, log'[server], entry.index)
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv, [Next]_vars
             PROVE \A request \in AppendRequests':
                \A entry \in ClusterAgreeEntries' \ ClusterAgreeEntries:
                    entry.term <= request.mterm =>
                        \A server \in ClusterReplicated(entry.index, entry.term)':
                            AppendRequestPrefixCompatible(request, log'[server], entry.index)
    OBVIOUS
<1>prefix. CandidateAppendPrefixInv' BY CandidateAppendPrefixNext
<1>subset. ClusterAgreeEntries' \subseteq ClusterAgreeCandidateEntries'
    BY ClusterAgreeEntriesAreCandidateEntriesNext
<1> QED BY <1>prefix, <1>subset
    DEF CandidateAppendPrefixInv, AppendRequestPrefixCompatible

LEMMA ClusterAgreeAppendInvNext ==
    ClusterAgreeProofInv /\ CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars
        => ClusterAgreeAppendInv'
<1> SUFFICES ASSUME ClusterAgreeProofInv, CandidateEntryBaseInv,
                    LeaderCompletenessInductionInv, [Next]_vars,
                    NEW request \in AppendRequests', NEW entry \in ClusterAgreeEntries',
                    entry.term <= request.mterm,
                    NEW server \in ClusterReplicated(entry.index, entry.term)'
             PROVE AppendRequestPrefixCompatible(request, log'[server], entry.index)
    BY DEF ClusterAgreeAppendInv
<1>newEntry. CASE entry \notin ClusterAgreeEntries
    BY <1>newEntry, NewlyAgreedEntriesRespectHistoricalRequests
<1>oldRequest. CASE entry \in ClusterAgreeEntries /\ request \in AppendRequests
    BY <1>oldRequest, HistoricalRequestsRetainClusterAgreeCompatibility
<1>newRequest. CASE entry \in ClusterAgreeEntries /\ request \notin AppendRequests
    BY <1>newRequest, NewRequestsRespectClusterAgreePrefixes
<1> QED BY <1>newEntry, <1>oldRequest, <1>newRequest

LEMMA ClusterAgreeSupportInvNext ==
    ClusterAgreeProofInv /\ CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars
        => ClusterAgreeSupportInv'
    BY LeaderClusterAgreeInvNext, ClusterAgreeAppendInvNext
    DEF ClusterAgreeSupportInv

---------------------------------------------------------------

THEOREM AppendRequestSenderWonInvariant == Spec => []AppendRequestSenderWonInv
<1>inductive. Spec => []InductiveInvariant BY InductiveInvariantInvariant
<1>init. Init => AppendRequestSenderWonInv BY AppendRequestSenderWonInit
<1>next. InductiveInvariant /\ AppendRequestSenderWonInv /\ [Next]_vars
         => AppendRequestSenderWonInv'
    BY AppendRequestSenderWonNext
<1> QED BY <1>inductive, <1>init, <1>next, PTL DEF Spec

THEOREM SuccessfulResponseRecipientWonInvariant ==
    Spec => []SuccessfulResponseRecipientWonInv
<1>independent. Spec => []InductiveInvariant /\ []AppendRequestSenderWonInv
    BY InductiveInvariantInvariant, AppendRequestSenderWonInvariant
<1>init. Init => SuccessfulResponseRecipientWonInv
    BY SuccessfulResponseRecipientWonInit
<1>next. InductiveInvariant /\ AppendRequestSenderWonInv
         /\ SuccessfulResponseRecipientWonInv /\ [Next]_vars
         => SuccessfulResponseRecipientWonInv'
    BY SuccessfulResponseRecipientWonNext
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM HigherElectionExcludesUncreatedEntryInvariant ==
    Spec => [](\A leader, candidate \in Server: \A index \in Nat:
        /\ state[leader] = Leader
        /\ Won(candidate, currentTerm[candidate])
        /\ currentTerm[leader] < currentTerm[candidate]
        /\ Len(log[leader]) < index
        => ClusterMightAgree(index, currentTerm[leader]) \notin Quorum)
<1>independent. Spec => []InductiveInvariant /\ []SuccessfulResponseRecipientWonInv
    BY InductiveInvariantInvariant, SuccessfulResponseRecipientWonInvariant
<1>state. InductiveInvariant /\ SuccessfulResponseRecipientWonInv =>
    \A leader, candidate \in Server: \A index \in Nat:
        /\ state[leader] = Leader
        /\ Won(candidate, currentTerm[candidate])
        /\ currentTerm[leader] < currentTerm[candidate]
        /\ Len(log[leader]) < index
        => ClusterMightAgree(index, currentTerm[leader]) \notin Quorum
    BY HigherElectionExcludesUncreatedEntry
<1> QED BY <1>independent, <1>state, PTL

THEOREM HistoricalSameTermBoundaryInvariant == Spec => []HistoricalSameTermBoundaryInv
<1>independent. Spec => /\ []InductiveInvariant /\ []EntryEdgeConsistency
                           /\ []TermOrderingInv /\ []AppendRequestRootTerm
    BY InductiveInvariantInvariant, EntryEdgeConsistencyInvariant,
        TermOrderingInvariant, AppendRequestRootTermInvariant
<1>init. Init => HistoricalSameTermBoundaryInv BY HistoricalSameTermBoundaryInit
<1>next. InductiveInvariant /\ EntryEdgeConsistency /\ TermOrderingInv
         /\ AppendRequestRootTerm /\ HistoricalSameTermBoundaryInv /\ [Next]_vars
         => HistoricalSameTermBoundaryInv'
    BY HistoricalSameTermBoundaryNext
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM AppendRequestSenderNotCandidateInvariant == Spec => []AppendRequestSenderNotCandidateInv
<1>independent. Spec => []InductiveInvariant BY InductiveInvariantInvariant
<1>init. Init => AppendRequestSenderNotCandidateInv BY AppendSenderNotCandidateInit
<1>next. InductiveInvariant /\ AppendRequestSenderNotCandidateInv /\ [Next]_vars =>
    AppendRequestSenderNotCandidateInv'
    BY AppendSenderNotCandidateNext
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM CandidateEntryBaseInvariant == Spec => []CandidateEntryBaseInv
<1>independent. Spec =>
    /\ []InductiveInvariant /\ []LogMatchingInv /\ []EntryEdgeConsistency
    /\ []TermOrderingInv /\ []CandidateCurrentTermFree /\ []AppendRequestRootTerm
    /\ []AppendRequestSenderWonInv /\ []SuccessfulResponseRecipientWonInv
    /\ []HistoricalSameTermBoundaryInv /\ []AppendRequestSenderNotCandidateInv
    BY InductiveInvariantInvariant, ClusterLogMatchingInvariant,
        EntryEdgeConsistencyInvariant, TermOrderingInvariant,
        CandidateCurrentTermFreeInvariant, AppendRequestRootTermInvariant,
        AppendRequestSenderWonInvariant, SuccessfulResponseRecipientWonInvariant,
        HistoricalSameTermBoundaryInvariant, AppendRequestSenderNotCandidateInvariant
<1> QED BY <1>independent, PTL DEF CandidateEntryBaseInv

THEOREM LeaderCompletenessInductionInvariant == Spec => []LeaderCompletenessInductionInv
<1>independent. Spec => []CandidateEntryBaseInv BY CandidateEntryBaseInvariant
<1>init. Init => LeaderCompletenessInductionInv BY LeaderCompletenessInductionInit
<1>next. CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ [Next]_vars =>
    LeaderCompletenessInductionInv'
    BY LeaderCompletenessInductionNext
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM NewLeaderCandidateEntryCompletenessInvariant ==
    Spec => [][NewLeaderCandidateEntryCompleteness]_vars
<1>inductive. Spec => []CandidateEntryBaseInv /\ []LeaderCompletenessInductionInv
    BY CandidateEntryBaseInvariant, LeaderCompletenessInductionInvariant
<1>step. CandidateEntryBaseInv /\ LeaderCompletenessInductionInv =>
    NewLeaderCandidateEntryCompleteness
    BY LeaderCompletenessInductionImpliesNewLeaderCompleteness
<1> QED BY <1>inductive, <1>step, PTL

THEOREM ClusterAgreeSupportInvariant == Spec => []ClusterAgreeSupportInv
<1>independent. Spec =>
        /\ []CandidateEntryBaseInv /\ []LeaderCompletenessInductionInv
    BY CandidateEntryBaseInvariant, LeaderCompletenessInductionInvariant
<1>init. Init => ClusterAgreeSupportInv
    BY ClusterAgreeSupportInvInit
<1>next. CandidateEntryBaseInv /\ LeaderCompletenessInductionInv
         /\ ClusterAgreeSupportInv /\ [Next]_vars => ClusterAgreeSupportInv'
    BY ClusterAgreeSupportInvNext DEF ClusterAgreeProofInv, CandidateEntryBaseInv
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM GrowOnlyClusterAgreeEntries == Spec => [][StableClusterAgreeEntriesInv]_vars
<1>1. Spec => [][Next]_vars /\ []InductiveInvariant /\ []ClusterAgreeSupportInv
    BY InductiveInvariantInvariant, ClusterAgreeSupportInvariant DEF Spec
<1>2. InductiveInvariant /\ ClusterAgreeSupportInv /\ [Next]_vars
       => [StableClusterAgreeEntriesInv]_vars
    BY NextGrowsClusterAgree
<1> QED BY <1>1, <1>2, PTL

===============================================================
