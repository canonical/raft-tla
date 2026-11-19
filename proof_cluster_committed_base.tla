------------ MODULE proof_cluster_committed_base ------------
\* proof_cluster_committed_base.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_log_matching_inv, proof_log_term_monotonic, proof_commitindex

GrantTermBoundInv ==
    \A voter, candidate \in Server: \A term \in Nat:
        Grant(voter, candidate, term) => term <= currentTerm[voter]

-------------------------------------------------------------

LEMMA GrantTermBoundFromSendInvariant ==
    InductiveInvariant => GrantTermBoundInv
    BY MessageFieldsTypeOK
    DEF InductiveInvariant, TypeOK, MsgTypeOK, SendInvariant, GrantTermBoundInv, Grant

LEMMA WonUniqueNextState ==
    VoteRecordInv' =>
        \A left, right \in Server: \A term \in Nat:
            Won(left, term)' /\ Won(right, term)' => left = right
<1> SUFFICES ASSUME VoteRecordInv', NEW left \in Server, NEW right \in Server,
                    NEW term \in Nat, Won(left, term)', Won(right, term)'
             PROVE left = right
    OBVIOUS
<1> PICK leftQuorum \in Quorum:
        \A voter \in leftQuorum: VoteFor(voter, left, term)'
    BY DEF Won
<1> PICK rightQuorum \in Quorum:
        \A voter \in rightQuorum: VoteFor(voter, right, term)'
    BY DEF Won
<1>intersection. leftQuorum \cap rightQuorum # {} BY QuorumsIntersect
<1> PICK voter \in leftQuorum \cap rightQuorum: TRUE BY <1>intersection
<1>votes. /\ voter \in Server
            /\ VoteFor(voter, left, term)' /\ VoteFor(voter, right, term)'
    BY DEF Quorum
<1>started. Started(left, term)' /\ Started(right, term)' BY DEF Won
<1> QED BY <1>votes, <1>started
    DEF VoteFor, VoteRecordInv, VoteUniqueInv, StartedGrantInv

LEMMA CurrentTermsMonotonicNext ==
    InductiveInvariant /\ [Next]_vars =>
        \A server \in Server: currentTerm[server] <= currentTerm'[server]
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, NEW server \in Server
             PROVE currentTerm[server] <= currentTerm'[server]
    OBVIOUS
<1>types. /\ currentTerm \in [Server -> Nat]
            /\ messages \subseteq Message
    BY DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>fields. \A m \in messages:
        /\ m.mdest \in Server
        /\ m.mterm \in Nat
    BY <1>types, MessageFieldsTypeOK
<1>handlers. \A i, j, m:
        HandleMsg(i, j, m) => UNCHANGED currentTerm
    BY DEF HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1>timeout. CASE \E i \in Server: Timeout(i)
    BY <1>timeout, TimeoutDoesNotDecreaseTerms
    DEF InductiveInvariant, TypeOK
<1>update. CASE \E m \in messages: UpdateTerm(m.mdest, m.msource, m)
    BY <1>update, <1>types, <1>fields, SMT DEF UpdateTerm
<1>unchanged. CASE UNCHANGED currentTerm
    BY <1>unchanged, <1>types
<1> QED BY <1>timeout, <1>update, <1>unchanged, <1>handlers
    DEF Next, vars, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive

LEMMA HigherElectionVotersHaveHigherTerms ==
    \A candidate \in Server: \A quorum \in Quorum:
        /\ InductiveInvariant
        /\ \A voter \in quorum: VoteFor(voter, candidate, currentTerm[candidate])
        => \A voter \in quorum: currentTerm[candidate] <= currentTerm[voter]
    BY GrantTermBoundFromSendInvariant, SMT
    DEF Quorum, VoteFor, GrantTermBoundInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK

LEMMA CandidateWithQuorumWon ==
    \A candidate \in Server:
        /\ InductiveInvariant
        /\ state[candidate] = Candidate
        /\ votesGranted[candidate] \in Quorum
        => Won(candidate, currentTerm[candidate])
    BY DEF InductiveInvariant, ActiveVotesInv, Won

LEMMA CandidateQuorumExcludesCurrentTermEntries ==
    \A candidate \in Server:
        /\ InductiveInvariant
        /\ CandidateCurrentTermFree
        /\ state[candidate] = Candidate
        /\ votesGranted[candidate] \in Quorum
        => \A server \in Server: \A index \in DOMAIN log[server]:
               log[server][index].term # currentTerm[candidate]
<1> SUFFICES ASSUME NEW candidate \in Server, InductiveInvariant,
                    CandidateCurrentTermFree, state[candidate] = Candidate,
                    votesGranted[candidate] \in Quorum,
                    NEW server \in Server, NEW index \in DOMAIN log[server],
                    log[server][index].term = currentTerm[candidate]
             PROVE FALSE
    OBVIOUS
<1>won. Won(candidate, currentTerm[candidate])
    BY CandidateWithQuorumWon
<1> PICK owner \in Server: TermOwner(owner, currentTerm[candidate], index)
    BY DEF InductiveInvariant, LogElectionInv
<1>owner. owner = candidate
    BY <1>won, WonUnique
    DEF TermOwner, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>entry. /\ index \in DOMAIN log[candidate]
             /\ log[candidate][index].term = currentTerm[candidate]
    BY <1>owner DEF TermOwner, OwnerActive, LogHasTermAt
<1> QED BY <1>entry DEF CandidateCurrentTermFree

LEMMA AppendEntriesSenderSnapshot ==
    \A leader, recipient \in Server:
        InductiveInvariant /\ AppendEntries(leader, recipient) =>
            LET request == AppendEntriesMessage(leader, recipient) IN
            /\ request.mprevLogIndex > 0 =>
                   log[leader][request.mprevLogIndex].term = request.mprevLogTerm
            /\ \A offset \in DOMAIN request.mentries:
                   request.mentries[offset] = log[leader][request.mprevLogIndex + offset]
<1> SUFFICES ASSUME NEW leader \in Server, NEW recipient \in Server,
                    InductiveInvariant, AppendEntries(leader, recipient)
             PROVE LET request == AppendEntriesMessage(leader, recipient) IN
            /\ request.mprevLogIndex > 0 =>
                   log[leader][request.mprevLogIndex].term = request.mprevLogTerm
            /\ \A offset \in DOMAIN request.mentries:
                   request.mentries[offset] = log[leader][request.mprevLogIndex + offset]
    OBVIOUS
<1>types. /\ log[leader] \in Seq(LogEntry) /\ nextIndex[leader][recipient] \in Nat
            /\ 1 <= nextIndex[leader][recipient]
            /\ nextIndex[leader][recipient] <= Len(log[leader]) + 1
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LeaderVarsTypeOK,
        NextIndexBound, AppendEntries
<1>previous.
    nextIndex[leader][recipient] - 1 > 0 =>
        log[leader][nextIndex[leader][recipient] - 1].term = AppendEntriesPrevLogTerm(leader, recipient)
    BY DEF AppendEntriesPrevLogTerm
<1>last. /\ AppendEntriesLastEntry(leader, recipient) \in Nat
           /\ AppendEntriesLastEntry(leader, recipient) <= Len(log[leader])
    BY AppendEntriesLastEntryTypeOK DEF InductiveInvariant
<1>elements. \A position \in
                 nextIndex[leader][recipient]..AppendEntriesLastEntry(leader, recipient):
                 log[leader][position] \in LogEntry
    BY <1>types, <1>last, ElementOfSeq
<1>length. Len(AppendEntriesEntries(leader, recipient)) =
               IF nextIndex[leader][recipient] <= AppendEntriesLastEntry(leader, recipient)
               THEN AppendEntriesLastEntry(leader, recipient) - nextIndex[leader][recipient] + 1
               ELSE 0
    BY <1>types, <1>last, <1>elements, SubSeqProperties DEF AppendEntriesEntries
<1>domain. DOMAIN AppendEntriesEntries(leader, recipient) =
               1..Len(AppendEntriesEntries(leader, recipient))
    BY AppendEntriesEntriesTypeOK, LenProperties DEF InductiveInvariant
<1>payload.
    \A offset \in DOMAIN AppendEntriesEntries(leader, recipient):
        AppendEntriesEntries(leader, recipient)[offset] =
            log[leader][nextIndex[leader][recipient] - 1 + offset]
    <2> SUFFICES ASSUME NEW offset \in DOMAIN AppendEntriesEntries(leader, recipient)
                 PROVE AppendEntriesEntries(leader, recipient)[offset] =
                           log[leader][nextIndex[leader][recipient] - 1 + offset]
        OBVIOUS
    <2>bounds. offset \in 1..(AppendEntriesLastEntry(leader, recipient) - nextIndex[leader][recipient] + 1)
        BY <1>types, <1>last, <1>length, <1>domain, SMT
    <2>entry. AppendEntriesEntries(leader, recipient)[offset] =
                  log[leader][offset + nextIndex[leader][recipient] - 1]
        BY <1>types, <1>last, <1>elements, <2>bounds, SubSeqProperties
        DEF AppendEntriesEntries
    <2> QED BY <1>types, <1>domain, <2>entry, SMT
<1> QED BY <1>previous, <1>payload DEF AppendEntriesMessage

LEMMA ContinuingLeaderKeepsTerm ==
    InductiveInvariant /\ [Next]_vars =>
        \A leader \in Server:
            state[leader] = Leader /\ state'[leader] = Leader
            => currentTerm'[leader] = currentTerm[leader]
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, NEW leader \in Server,
                    state[leader] = Leader, state'[leader] = Leader
             PROVE currentTerm'[leader] = currentTerm[leader]
    OBVIOUS
<1>types. /\ currentTerm \in [Server -> Nat]
            /\ state \in [Server -> {Follower, Candidate, Leader}]
            /\ messages \subseteq Message
    BY DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>fields. \A m \in messages: m.mdest \in Server
    BY <1>types, MessageFieldsTypeOK
<1>handlers. \A i, j, m:
        HandleMsg(i, j, m) => UNCHANGED currentTerm
    BY DEF HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1>timeout. CASE \E i \in Server: Timeout(i)
    BY <1>timeout, <1>types, ServerStatesDistinct, SMT DEF Timeout
<1>update. CASE \E m \in messages: UpdateTerm(m.mdest, m.msource, m)
    BY <1>update, <1>types, <1>fields, ServerStatesDistinct, SMT
    DEF UpdateTerm
<1>unchanged. CASE UNCHANGED currentTerm
    BY <1>unchanged
<1> QED BY <1>timeout, <1>update, <1>unchanged, <1>handlers
    DEF Next, vars, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive

LEMMA NextCreatesLeaderOnlyByElection ==
    InductiveInvariant /\ [Next]_vars =>
        \A leader \in Server:
            state[leader] # Leader /\ state'[leader] = Leader
            => BecomeLeader(leader)
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, NEW leader \in Server,
                    state[leader] # Leader, state'[leader] = Leader
             PROVE BecomeLeader(leader)
    OBVIOUS
<1>types. /\ state \in [Server -> {Follower, Candidate, Leader}]
            /\ messages \subseteq Message
    BY DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>fields. \A m \in messages: m.mdest \in Server
    BY <1>types, MessageFieldsTypeOK
<1>append. \A i, j, m:
        HandleAppendEntriesRequest(i, j, m) =>
            \/ UNCHANGED state
            \/ state' = [state EXCEPT ![i] = Follower]
    BY DEF HandleAppendEntriesRequest
<1>handlers. \A i, j, m:
        HandleMsg(i, j, m) =>
            \/ UNCHANGED state
            \/ state' = [state EXCEPT ![i] = Follower]
    BY <1>append
    DEF HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesResponse
<1>unchanged. CASE UNCHANGED state
    BY <1>unchanged
<1>follower. CASE \E i \in Server: state' = [state EXCEPT ![i] = Follower]
    BY <1>follower, <1>types, ServerStatesDistinct, SMT
<1>candidate. CASE \E i \in Server: state' = [state EXCEPT ![i] = Candidate]
    BY <1>candidate, <1>types, ServerStatesDistinct, SMT
<1>election. CASE \E i \in Server: BecomeLeader(i)
    <2> PICK i \in Server: BecomeLeader(i) BY <1>election
    <2>actor. i = leader BY <1>types, SMT DEF BecomeLeader
    <2> QED BY <2>actor
<1> QED BY <1>unchanged, <1>follower, <1>candidate, <1>election,
           <1>handlers, <1>fields
    DEF Next, vars, Restart, Timeout, ClientRequest, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm

LEMMA PersistentLeaderRetainsLogEntries ==
    InductiveInvariant /\ [Next]_vars =>
        \A leader \in Server:
            state[leader] = Leader /\ state'[leader] = Leader =>
                /\ currentTerm'[leader] = currentTerm[leader]
                /\ \A index \in DOMAIN log[leader]:
                       /\ index \in DOMAIN log'[leader]
                       /\ log'[leader][index] = log[leader][index]
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, NEW leader \in Server,
                    state[leader] = Leader, state'[leader] = Leader
             PROVE /\ currentTerm'[leader] = currentTerm[leader]
                   /\ \A index \in DOMAIN log[leader]:
                          /\ index \in DOMAIN log'[leader]
                          /\ log'[leader][index] = log[leader][index]
    OBVIOUS
<1>types. /\ log \in [Server -> Seq(LogEntry)]
            /\ currentTerm \in [Server -> Nat]
            /\ state \in [Server -> {Follower, Candidate, Leader}]
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>client. CASE \E server \in Server, value \in Value: ClientRequest(server, value)
    <2> PICK server \in Server, value \in Value: ClientRequest(server, value) BY <1>client
    <2>term. currentTerm' = currentTerm BY DEF ClientRequest
    <2>same. CASE server = leader
        <3>entry. [term |-> currentTerm[leader], value |-> value] \in LogEntry
            BY <1>types DEF LogEntry
        <3> QED BY <2>same, <2>term, <1>types, <3>entry, AppendProperties, LenProperties
            DEF ClientRequest
    <2>other. CASE server # leader
        BY <2>other, <2>term, <1>types DEF ClientRequest
    <2> QED BY <2>same, <2>other
<1>other. CASE ~(\E server \in Server, value \in Value: ClientRequest(server, value))
    <2>receive. CASE \E request \in messages: Receive(request)
        <3> PICK request \in messages: Receive(request) BY <2>receive
        <3>frame. /\ log'[leader] = log[leader]
                    /\ currentTerm'[leader] = currentTerm[leader]
            BY <1>types, MessageFieldsTypeOK, ServerStatesDistinct, SMTT(30)
            DEF InductiveInvariant, TypeOK, MsgTypeOK,
                Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest, HandleAppendEntriesResponse
        <3> QED BY <3>frame
    <2>other. CASE ~(\E request \in messages: Receive(request))
        BY <2>other, <1>other, <1>types, ServerStatesDistinct, SMT
        DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
            AdvanceCommitIndex, AppendEntries, LeaderStepDown
    <2> QED BY <2>receive, <2>other
<1> QED BY <1>client, <1>other

=============================================================
