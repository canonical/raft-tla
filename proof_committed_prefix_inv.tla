---------------- MODULE proof_committed_prefix_inv ----------------
\* proof_committed_prefix_inv.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_cluster_committed

AgreedPrefix(prefix) ==
    \/ prefix = << >>
    \/ \E entry \in ClusterAgreeEntries: \E anchor \in ClusterReplicated(entry.index, entry.term):
           IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))

CommittedPrefixInv == \A server \in Server: AgreedPrefix(Committed(server))

CommitCertificate(server, entry, anchor) ==
    /\ entry \in ClusterAgreeEntries
    /\ anchor \in ClusterReplicated(entry.index, entry.term)
    /\ entry.term <= currentTerm[server]
    /\ commitIndex[server] <= entry.index
    /\ commitIndex[server] <= Len(log[server])
    /\ SubSeq(log[server], 1, commitIndex[server])
           = SubSeq(log[anchor], 1, commitIndex[server])

CommittedCertificateInv ==
    \A server \in Server:
        \/ commitIndex[server] = 0
        \/ \E entry \in ClusterAgreeEntries: \E anchor \in Server:
               CommitCertificate(server, entry, anchor)

RequestCertificate(request, entry, anchor) ==
    /\ entry \in ClusterAgreeEntries
    /\ anchor \in ClusterReplicated(entry.index, entry.term)
    /\ entry.term <= request.mterm
    /\ request.mcommitIndex <= entry.index
    /\ IF request.mprevLogIndex < entry.index
       THEN /\ request.mprevLogIndex > 0 =>
                   request.mprevLogTerm = log[anchor][request.mprevLogIndex].term
            /\ request.mentries # << >>
            /\ request.mentries[1] = log[anchor][request.mprevLogIndex + 1]
       ELSE request.mprevLogTerm >= entry.term

RequestCertificateInv ==
    \A request \in AppendRequests:
        \/ request.mcommitIndex = 0
        \/ \E entry \in ClusterAgreeEntries: \E anchor \in Server:
               RequestCertificate(request, entry, anchor)

CommitCertificatesInv == CommittedCertificateInv /\ RequestCertificateInv

CurrentTermReplicaEvidenceInv ==
    \A server \in Server: \A index \in DOMAIN log[server]:
        log[server][index].term = currentTerm[server] =>
            EntryAgreementEvidence(server, index, currentTerm[server])

SuccessfulResponseLowerEvidenceInv ==
    \A leader \in Server: \A response \in messages: \A index \in DOMAIN log[leader]:
        /\ state[leader] = Leader
        /\ response.mtype = AppendEntriesResponse /\ response.msuccess
        /\ response.mdest = leader /\ response.mterm = currentTerm[leader]
        /\ log[leader][index].term = currentTerm[leader]
        /\ index <= response.mmatchIndex
        => EntryAgreementEvidence(response.msource, index, currentTerm[leader])

LeaderMatchResponseInv ==
    \A leader, server \in Server:
        state[leader] = Leader /\ matchIndex[leader][server] > 0 =>
            \E response \in messages:
                /\ response.mtype = AppendEntriesResponse /\ response.msuccess
                /\ response.msource = server /\ response.mdest = leader
                /\ response.mterm = currentTerm[leader]
                /\ response.mmatchIndex = matchIndex[leader][server]

LeaderAgreementBridgeInv ==
    /\ CurrentTermReplicaEvidenceInv
    /\ SuccessfulResponseLowerEvidenceInv
    /\ LeaderMatchResponseInv

CommitCertificateBaseInv ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ ClusterAgreeSupportInv

AcceptedCertifiedRequest(recipient, sender, request) ==
    /\ HandleAppendEntriesRequest(recipient, sender, request)
    /\ request.mterm = currentTerm[recipient]
    /\ state[recipient] # Leader
    /\ \/ request.mprevLogIndex = 0
       \/ /\ request.mprevLogIndex > 0
          /\ request.mprevLogIndex <= Len(log[recipient])
          /\ request.mprevLogTerm = log[recipient][request.mprevLogIndex].term

CommittedProofInv == CommitCertificateBaseInv /\ LeaderAgreementBridgeInv /\ CommitCertificatesInv

------------------------------------------------------------------------

LEMMA SequencePrefixEmpty ==
    \A entries \in Seq(LogEntry): IsPrefix(<< >>, entries)
    BY EmptySeq, LenProperties, SubSeqEmpty, SMT DEF IsPrefix

LEMMA SequencePrefixTake ==
    \A entries \in Seq(LogEntry): \A cut \in 0..Len(entries):
        /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, 1, cut)) = cut
        /\ IsPrefix(SubSeq(entries, 1, cut), entries)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW cut \in 0..Len(entries)
             PROVE /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
                   /\ Len(SubSeq(entries, 1, cut)) = cut
                   /\ IsPrefix(SubSeq(entries, 1, cut), entries)
    BY SMT
<1>types. /\ cut \in Nat /\ Len(entries) \in Nat
    BY LenProperties, SMT
<1>elements. \A index \in 1..cut: entries[index] \in LogEntry
    BY <1>types, ElementOfSeq, SMT
<1>take. /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
         /\ Len(SubSeq(entries, 1, cut)) = cut
    BY <1>types, <1>elements, SubSeqProperties, SMT
<1> QED BY <1>take DEF IsPrefix

LEMMA SequencePrefixShorten ==
    \A prefix, entries \in Seq(LogEntry): \A cut \in 0..Len(prefix):
        IsPrefix(prefix, entries) =>
            SubSeq(prefix, 1, cut) = SubSeq(entries, 1, cut)
<1> SUFFICES ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry),
                    NEW cut \in 0..Len(prefix), IsPrefix(prefix, entries)
             PROVE SubSeq(prefix, 1, cut) = SubSeq(entries, 1, cut)
    BY SMT
<1>types. /\ Len(prefix) \in Nat /\ Len(entries) \in Nat /\ cut \in Nat
          /\ Len(prefix) <= Len(entries)
          /\ prefix = SubSeq(entries, 1, Len(prefix))
    BY LenProperties, SMT DEF IsPrefix
<1>empty. CASE cut = 0
    BY <1>empty, SubSeqEmpty, SMT
<1>positive. CASE cut > 0
    <2>bounds. /\ 1 \in 1..Len(entries) /\ Len(prefix) \in 1..Len(entries)
               /\ 1 \in 1..Len(prefix) /\ cut \in 1..Len(prefix)
        BY <1>types, <1>positive, SMT
    <2> QED BY <1>types, <2>bounds, SubSeqOfSubSeq, SMT
<1> QED BY <1>empty, <1>positive, <1>types, SMT

LEMMA SequencePrefixTransitive ==
    \A shorter, longer, entries \in Seq(LogEntry):
        IsPrefix(shorter, longer) /\ IsPrefix(longer, entries) =>
            IsPrefix(shorter, entries)
<1> SUFFICES ASSUME NEW shorter \in Seq(LogEntry), NEW longer \in Seq(LogEntry),
                    NEW entries \in Seq(LogEntry), IsPrefix(shorter, longer),
                    IsPrefix(longer, entries)
             PROVE IsPrefix(shorter, entries)
    BY SMT
<1>bounds. /\ Len(shorter) \in 0..Len(longer)
           /\ Len(shorter) <= Len(entries)
    BY LenProperties, SMT DEF IsPrefix
<1>prefix. SubSeq(longer, 1, Len(shorter)) = SubSeq(entries, 1, Len(shorter))
    BY <1>bounds, SequencePrefixShorten
<1> QED BY <1>bounds, <1>prefix DEF IsPrefix

LEMMA SequencePrefixesComparable ==
    \A left, right, entries \in Seq(LogEntry):
        IsPrefix(left, entries) /\ IsPrefix(right, entries) =>
            IsPrefix(left, right) \/ IsPrefix(right, left)
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    NEW entries \in Seq(LogEntry), IsPrefix(left, entries),
                    IsPrefix(right, entries)
             PROVE IsPrefix(left, right) \/ IsPrefix(right, left)
    BY SMT
<1>types. /\ Len(left) \in Nat /\ Len(right) \in Nat
    BY LenProperties
<1>left. CASE Len(left) <= Len(right)
    <2>bound. Len(left) \in 0..Len(right) BY <1>types, <1>left, SMT
    <2>prefix. SubSeq(right, 1, Len(left)) = SubSeq(entries, 1, Len(left))
        BY <2>bound, SequencePrefixShorten
    <2> QED BY <1>left, <2>prefix DEF IsPrefix
<1>right. CASE Len(right) <= Len(left)
    <2>bound. Len(right) \in 0..Len(left) BY <1>types, <1>right, SMT
    <2>prefix. SubSeq(left, 1, Len(right)) = SubSeq(entries, 1, Len(right))
        BY <2>bound, SequencePrefixShorten
    <2> QED BY <1>right, <2>prefix DEF IsPrefix
<1> QED BY <1>left, <1>right, <1>types, SMT

LEMMA AgreedPrefixEmpty == AgreedPrefix(<< >>)
    BY DEF AgreedPrefix

LEMMA AgreedPrefixDownwardClosure ==
    InductiveInvariant => \A shorter, longer \in Seq(LogEntry):
        IsPrefix(shorter, longer) /\ AgreedPrefix(longer) => AgreedPrefix(shorter)
<1> SUFFICES ASSUME InductiveInvariant, NEW shorter \in Seq(LogEntry),
                    NEW longer \in Seq(LogEntry), IsPrefix(shorter, longer),
                    AgreedPrefix(longer)
             PROVE AgreedPrefix(shorter)
    BY SMT
<1>empty. CASE longer = << >>
    <2>shorterEmpty. shorter = << >>
        BY <1>empty, EmptySeq, LenProperties, SubSeqEmpty, SMT DEF IsPrefix
    <2> QED BY <2>shorterEmpty, AgreedPrefixEmpty
<1>certificate. CASE longer # << >>
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in ClusterReplicated(entry.index, entry.term):
                IsPrefix(longer, SubSeq(log[anchor], 1, entry.index))
        BY <1>certificate DEF AgreedPrefix
    <2> PICK anchor \in ClusterReplicated(entry.index, entry.term):
            IsPrefix(longer, SubSeq(log[anchor], 1, entry.index))
        BY SMT
    <2>types. /\ log[anchor] \in Seq(LogEntry)
              /\ entry.index \in 0..Len(log[anchor])
        BY LenProperties, SMT
        DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ClusterReplicated
    <2>segment. SubSeq(log[anchor], 1, entry.index) \in Seq(LogEntry)
        BY <2>types, SequencePrefixTake
    <2>prefix. IsPrefix(shorter, SubSeq(log[anchor], 1, entry.index))
        BY <2>segment, SequencePrefixTransitive
    <2> QED BY <2>prefix DEF AgreedPrefix
<1> QED BY <1>empty, <1>certificate

LEMMA AgreedPrefixPersistence ==
    InductiveInvariant /\ ClusterAgreeSupportInv /\ [Next]_vars =>
        \A prefix \in Seq(LogEntry): AgreedPrefix(prefix) => AgreedPrefix(prefix)'
<1> SUFFICES ASSUME InductiveInvariant, ClusterAgreeSupportInv, [Next]_vars,
                    NEW prefix \in Seq(LogEntry), AgreedPrefix(prefix)
             PROVE AgreedPrefix(prefix)'
    BY SMT
<1>empty. CASE prefix = << >>
    BY <1>empty DEF AgreedPrefix
<1>certificate. CASE prefix # << >>
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in ClusterReplicated(entry.index, entry.term):
                IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))
        BY <1>certificate DEF AgreedPrefix
    <2> PICK anchor \in ClusterReplicated(entry.index, entry.term):
            IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))
        BY SMT
    <2>before. /\ anchor \in Server /\ entry.index \in DOMAIN log[anchor]
               /\ log[anchor][entry.index].term = entry.term
        BY DEF ClusterReplicated
    <2>protected. \A request \in AppendRequests:
            log[anchor][entry.index].term <= request.mterm =>
                AppendRequestPrefixCompatible(request, log[anchor], entry.index)
        BY <2>before DEF ClusterAgreeSupportInv, ClusterAgreeAppendInv
    <2>retained. /\ entry.index \in DOMAIN log'[anchor]
                 /\ SubSeq(log'[anchor], 1, entry.index)
                        = SubSeq(log[anchor], 1, entry.index)
        BY <2>before, <2>protected, ProtectedReplicaPrefixNext
    <2>types. /\ log[anchor] \in Seq(LogEntry) /\ log'[anchor] \in Seq(LogEntry)
              /\ entry.index \in Nat
              /\ entry.index \in 1..entry.index
              /\ entry.index <= Len(log[anchor])
              /\ entry.index <= Len(log'[anchor])
        BY <2>before, <2>retained, TypeOKNext, LenProperties, SMT
        DEF InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>endpoint. log'[anchor][entry.index] = log[anchor][entry.index]
        BY <2>types, <2>retained, EqualLogPrefixesEntryEqual
    <2>replica. anchor \in ClusterReplicated(entry.index, entry.term)'
        BY <2>before, <2>retained, <2>endpoint DEF ClusterReplicated
    <2>stable. entry \in ClusterAgreeEntries'
        BY ClusterAgreeSupportInvSufficesForNext DEF StableClusterAgreeEntriesInv
    <2> QED BY <2>stable, <2>replica, <2>retained DEF AgreedPrefix
<1> QED BY <1>empty, <1>certificate

LEMMA AgreedPrefixAtReplica ==
    InductiveInvariant /\ LogMatchingInv =>
        \A prefix \in Seq(LogEntry): \A entry \in ClusterAgreeEntries:
            \A anchor, replica \in ClusterReplicated(entry.index, entry.term):
                IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index)) =>
                    IsPrefix(prefix, log[replica])
<1> SUFFICES ASSUME InductiveInvariant, LogMatchingInv,
                    NEW prefix \in Seq(LogEntry), NEW entry \in ClusterAgreeEntries,
                    NEW anchor \in ClusterReplicated(entry.index, entry.term),
                    NEW replica \in ClusterReplicated(entry.index, entry.term),
                    IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))
             PROVE IsPrefix(prefix, log[replica])
    BY SMT
<1>types. /\ anchor \in Server /\ replica \in Server
          /\ log[anchor] \in Seq(LogEntry) /\ log[replica] \in Seq(LogEntry)
          /\ entry.index \in 1..Len(log[anchor])
          /\ entry.index \in 1..Len(log[replica])
          /\ log[anchor][entry.index].term = log[replica][entry.index].term
    BY LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ClusterReplicated
<1>matching. SubSeq(log[anchor], 1, entry.index)
                 = SubSeq(log[replica], 1, entry.index)
    BY <1>types DEF LogMatchingInv
<1>take. /\ SubSeq(log[replica], 1, entry.index) \in Seq(LogEntry)
         /\ IsPrefix(SubSeq(log[replica], 1, entry.index), log[replica])
    BY <1>types, SequencePrefixTake, SMT
<1> QED BY <1>matching, <1>take, <1>types, SequencePrefixTransitive

LEMMA AgreedPrefixInQuorum ==
    InductiveInvariant /\ LogMatchingInv =>
        \A prefix \in Seq(LogEntry): \A quorum \in Quorum:
            AgreedPrefix(prefix) =>
                \E replica \in quorum: IsPrefix(prefix, log[replica])
<1> SUFFICES ASSUME InductiveInvariant, LogMatchingInv,
                    NEW prefix \in Seq(LogEntry), NEW quorum \in Quorum,
                    AgreedPrefix(prefix)
             PROVE \E replica \in quorum: IsPrefix(prefix, log[replica])
    BY SMT
<1>empty. CASE prefix = << >>
    <2>nonempty. quorum # {} BY QuorumsIntersect
    <2> PICK replica \in quorum: TRUE BY <2>nonempty
    <2>types. /\ replica \in Server /\ log[replica] \in Seq(LogEntry)
        BY DEF Quorum, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2> QED BY <1>empty, <2>types, SequencePrefixEmpty
<1>certificate. CASE prefix # << >>
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in ClusterReplicated(entry.index, entry.term):
                IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))
        BY <1>certificate DEF AgreedPrefix
    <2> PICK anchor \in ClusterReplicated(entry.index, entry.term):
            IsPrefix(prefix, SubSeq(log[anchor], 1, entry.index))
        BY SMT
    <2>quorum. ClusterAgree(entry.index, entry.term) \in Quorum
        BY DEF ClusterAgreeEntries
    <2>intersection. quorum \cap ClusterAgree(entry.index, entry.term) # {}
        BY <2>quorum, QuorumsIntersect
    <2> PICK replica \in quorum \cap ClusterAgree(entry.index, entry.term): TRUE
        BY <2>intersection
    <2>replica. replica \in ClusterReplicated(entry.index, entry.term)
        BY DEF ClusterAgree
    <2>prefix. IsPrefix(prefix, log[replica])
        BY <2>replica, AgreedPrefixAtReplica
    <2> QED BY <2>prefix
<1> QED BY <1>empty, <1>certificate

LEMMA AgreedPrefixesComparable ==
    InductiveInvariant /\ LogMatchingInv =>
        \A left, right \in Seq(LogEntry):
            AgreedPrefix(left) /\ AgreedPrefix(right) =>
                IsPrefix(left, right) \/ IsPrefix(right, left)
<1> SUFFICES ASSUME InductiveInvariant, LogMatchingInv,
                    NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    AgreedPrefix(left), AgreedPrefix(right)
             PROVE IsPrefix(left, right) \/ IsPrefix(right, left)
    BY SMT
<1>leftEmpty. CASE left = << >>
    BY <1>leftEmpty, SequencePrefixEmpty
<1>rightEmpty. CASE right = << >>
    BY <1>rightEmpty, SequencePrefixEmpty
<1>certificates. CASE left # << >> /\ right # << >>
    <2> PICK leftEntry \in ClusterAgreeEntries:
            \E anchor \in ClusterReplicated(leftEntry.index, leftEntry.term):
                IsPrefix(left, SubSeq(log[anchor], 1, leftEntry.index))
        BY <1>certificates DEF AgreedPrefix
    <2> PICK leftAnchor \in ClusterReplicated(leftEntry.index, leftEntry.term):
            IsPrefix(left, SubSeq(log[leftAnchor], 1, leftEntry.index))
        BY SMT
    <2> PICK rightEntry \in ClusterAgreeEntries:
            \E anchor \in ClusterReplicated(rightEntry.index, rightEntry.term):
                IsPrefix(right, SubSeq(log[anchor], 1, rightEntry.index))
        BY <1>certificates DEF AgreedPrefix
    <2> PICK rightAnchor \in ClusterReplicated(rightEntry.index, rightEntry.term):
            IsPrefix(right, SubSeq(log[rightAnchor], 1, rightEntry.index))
        BY SMT
    <2>quorums. /\ ClusterAgree(leftEntry.index, leftEntry.term) \in Quorum
                /\ ClusterAgree(rightEntry.index, rightEntry.term) \in Quorum
        BY DEF ClusterAgreeEntries
    <2>intersection. ClusterAgree(leftEntry.index, leftEntry.term)
                        \cap ClusterAgree(rightEntry.index, rightEntry.term) # {}
        BY <2>quorums, QuorumsIntersect
    <2> PICK replica \in ClusterAgree(leftEntry.index, leftEntry.term)
                           \cap ClusterAgree(rightEntry.index, rightEntry.term): TRUE
        BY <2>intersection
    <2>replicas. /\ replica \in ClusterReplicated(leftEntry.index, leftEntry.term)
                 /\ replica \in ClusterReplicated(rightEntry.index, rightEntry.term)
        BY DEF ClusterAgree
    <2>prefixes. /\ IsPrefix(left, log[replica]) /\ IsPrefix(right, log[replica])
        BY <2>replicas, AgreedPrefixAtReplica
    <2>types. log[replica] \in Seq(LogEntry)
        BY <2>replicas DEF ClusterReplicated, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2> QED BY <2>prefixes, <2>types, SequencePrefixesComparable
<1> QED BY <1>leftEmpty, <1>rightEmpty, <1>certificates

LEMMA CommitCertificatesImpliesCommitIndexBound ==
    InductiveInvariant /\ CommittedCertificateInv => CommitIndexBound
<1> SUFFICES ASSUME InductiveInvariant, CommittedCertificateInv, NEW server \in Server
             PROVE commitIndex[server] <= Len(log[server])
    BY DEF CommitIndexBound
<1>types. /\ commitIndex[server] \in Nat /\ log[server] \in Seq(LogEntry)
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>empty. CASE commitIndex[server] = 0
    BY <1>empty, <1>types, LenProperties, SMT
<1>certified. CASE commitIndex[server] # 0
    BY <1>certified DEF CommittedCertificateInv, CommitCertificate
<1> QED BY <1>empty, <1>certified

LEMMA CommittedPrefixesTypeOK ==
    InductiveInvariant /\ CommitIndexBound => \A server \in Server: Committed(server) \in Seq(LogEntry)
<1> SUFFICES ASSUME InductiveInvariant, CommitIndexBound, NEW server \in Server
             PROVE Committed(server) \in Seq(LogEntry)
    BY SMT
<1>types. /\ log[server] \in Seq(LogEntry)
          /\ commitIndex[server] \in 0..Len(log[server])
    BY SMT DEF InductiveInvariant, TypeOK, LogVarsTypeOK, CommitIndexBound
<1> QED BY <1>types, SequencePrefixTake DEF Committed

----

LEMMA CommittedPrefixImpliesQuorumLogInv ==
    InductiveInvariant /\ CommitIndexBound /\ LogMatchingInv /\ CommittedPrefixInv => QuorumLogInv
    BY CommittedPrefixesTypeOK, AgreedPrefixInQuorum
    DEF CommittedPrefixInv, QuorumLogInv

LEMMA CommittedPrefixImpliesLogInv ==
    InductiveInvariant /\ CommitIndexBound /\ LogMatchingInv /\ CommittedPrefixInv => LogInv
    BY CommittedPrefixesTypeOK, AgreedPrefixesComparable
    DEF CommittedPrefixInv, LogInv

LEMMA LeaderMatchResponseInit == Init => LeaderMatchResponseInv
    BY ServerStatesDistinct DEF Init, InitServerVars, LeaderMatchResponseInv

LEMMA LeaderMatchResponseNext ==
    InductiveInvariant /\ LeaderMatchResponseInv /\ [Next]_vars => LeaderMatchResponseInv'
<1> SUFFICES ASSUME InductiveInvariant, LeaderMatchResponseInv, [Next]_vars,
                    NEW leader \in Server, NEW server \in Server,
                    state'[leader] = Leader, matchIndex'[leader][server] > 0
             PROVE \E response \in messages':
                /\ response.mtype = AppendEntriesResponse /\ response.msuccess
                /\ response.msource = server /\ response.mdest = leader
                /\ response.mterm = currentTerm'[leader]
                /\ response.mmatchIndex = matchIndex'[leader][server]
    BY DEF LeaderMatchResponseInv
<1>types. /\ state \in [Server -> {Follower, Candidate, Leader}]
            /\ currentTerm \in [Server -> Nat]
            /\ matchIndex \in [Server -> [Server -> Nat]]
            /\ messages \subseteq Message
    BY DEF InductiveInvariant, TypeOK, ServerVarsTypeOK, LeaderVarsTypeOK, MsgTypeOK
<1>grow. messages \subseteq messages' BY MessagesMonotonicNext
<1>response. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
    <2> PICK m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
        BY <1>response
    <2>fields. m.mdest \in Server /\ m.msource \in Server
        BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>changed. CASE matchIndex'[leader][server] # matchIndex[leader][server]
        BY <1>types, <2>fields, <2>changed, SMT
        DEF HandleAppendEntriesResponse
    <2>unchanged. CASE matchIndex'[leader][server] = matchIndex[leader][server]
        BY <1>grow, <2>unchanged DEF HandleAppendEntriesResponse, LeaderMatchResponseInv
    <2> QED BY <2>changed, <2>unchanged
<1>other. CASE ~(\E m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m))
    <2>oldLeader. state[leader] = Leader
        BY NextCreatesLeaderOnlyByElection, <1>types, ServerStatesDistinct, SMT
        DEF BecomeLeader
    <2>same. matchIndex'[leader][server] = matchIndex[leader][server]
        <3>receive. CASE \E request \in messages: Receive(request)
            <4> PICK request \in messages: Receive(request) BY <3>receive
            <4>fields. request.mdest \in Server /\ request.msource \in Server
                BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK
            <4> QED BY <1>other, <1>types, <4>fields, MessageTypesDistinct, SMT
                DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                    HandleRequestVoteResponse, HandleAppendEntriesRequest,
                    HandleAppendEntriesResponse
        <3>nonreceive. CASE ~(\E request \in messages: Receive(request))
            <4>restart. CASE \E i \in Server: Restart(i)
                BY <4>restart, <1>types, <2>oldLeader, ServerStatesDistinct, SMT DEF Restart
            <4>election. CASE \E i \in Server: BecomeLeader(i)
                BY <4>election, <1>types, <2>oldLeader, ServerStatesDistinct, SMT DEF BecomeLeader
            <4>frame. CASE UNCHANGED matchIndex
                BY <4>frame
            <4> QED BY <4>restart, <4>election, <4>frame, <3>nonreceive
                DEF Next, vars, Timeout, ClientRequest, AdvanceCommitIndex, AppendEntries,
                    LeaderStepDown
        <3> QED BY <3>receive, <3>nonreceive
    <2>term. currentTerm'[leader] = currentTerm[leader]
        BY <2>oldLeader, ContinuingLeaderKeepsTerm
    <2> QED BY <1>grow, <2>oldLeader, <2>same, <2>term DEF LeaderMatchResponseInv
<1> QED BY <1>response, <1>other

LEMMA CurrentTermReplicaEvidenceInit == Init => CurrentTermReplicaEvidenceInv
    BY DEF Init, InitLogVars, CurrentTermReplicaEvidenceInv

LEMMA CurrentTermReplicaEvidenceNext ==
    InductiveInvariant /\ CurrentTermReplicaEvidenceInv /\ [Next]_vars =>
        CurrentTermReplicaEvidenceInv'
<1> SUFFICES ASSUME InductiveInvariant, CurrentTermReplicaEvidenceInv, [Next]_vars,
                    NEW server \in Server, NEW index \in DOMAIN log'[server],
                    NEW term \in Nat, currentTerm'[server] = term,
                    log'[server][index].term = term
             PROVE EntryAgreementEvidence(server, index, term)'
    BY TypeOKNext DEF CurrentTermReplicaEvidenceInv, InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>types. /\ log \in [Server -> Seq(LogEntry)] /\ currentTerm \in [Server -> Nat]
            /\ log' \in [Server -> Seq(LogEntry)] /\ currentTerm' \in [Server -> Nat]
            /\ index \in Nat
    BY TypeOKNext, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>old. CASE /\ index \in DOMAIN log[server]
               /\ log'[server][index] = log[server][index]
    <2>term. currentTerm'[server] = currentTerm[server]
        BY <1>types, <1>old, CurrentTermsMonotonicNext, SMT
        DEF InductiveInvariant, LogTermBoundInv
    <2>evidence. EntryAgreementEvidence(server, index, currentTerm[server])
        BY <1>old, <2>term DEF CurrentTermReplicaEvidenceInv
    <2> QED BY <1>types, <2>term, <2>evidence, MessagesMonotonicNext, WonMonotonicNext
        DEF EntryAgreementEvidence
<1>new. CASE ~(/\ index \in DOMAIN log[server]
                /\ log'[server][index] = log[server][index])
    <2>client. CASE \E leader \in Server, value \in Value: ClientRequest(leader, value)
        <3> PICK leader \in Server, value \in Value: ClientRequest(leader, value) BY <2>client
        <3>same. leader = server
            BY <1>types, <1>new DEF ClientRequest
        <3>won. Won(server, currentTerm[server]) BY <3>same, ActiveLeaderWon DEF ClientRequest
        <3> QED BY <3>won, WonMonotonicNext DEF ClientRequest, EntryAgreementEvidence
    <2>append. CASE \E request \in messages:
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        <3> PICK request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
            BY <2>append
        <3>fields. /\ request.mdest \in Server /\ request.msource \in Server
                   /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
                   /\ Len(request.mentries) <= 1
            BY MessageFieldsTypeOK
            DEF InductiveInvariant, TypeOK, MsgTypeOK, RequestCommitIndexBound
        <3>changed. /\ log' # log /\ request.mdest = server
            BY <1>types, <1>new, <3>fields DEF HandleAppendEntriesRequest
        <3>shape. /\ request.mprevLogIndex <= Len(log[server])
                  /\ request.mentries # << >>
                  /\ log'[server] = Append(SubSeq(log[server], 1, request.mprevLogIndex),
                                           request.mentries[1])
                  /\ currentTerm' = currentTerm
            BY <1>types, <3>fields, <3>changed, AppendRequestChangedLogShape
            DEF HandleAppendEntriesRequest
        <3>prefix. /\ SubSeq(log[server], 1, request.mprevLogIndex) \in Seq(LogEntry)
                   /\ Len(SubSeq(log[server], 1, request.mprevLogIndex)) = request.mprevLogIndex
            BY <1>types, <3>fields, <3>shape, SubSeqProperties,
                1 \in Int, Nat \subseteq Int
        <3>endpoint. index = request.mprevLogIndex + 1
            <4>length. Len(log'[server]) = request.mprevLogIndex + 1
                BY <3>fields, <3>changed, AppendRequestChangedLogShape
            <4>bound. index \in 1..(request.mprevLogIndex + 1)
                BY <1>types, <4>length, LenProperties
            <4>below. index <= request.mprevLogIndex =>
                /\ index \in DOMAIN log[server]
                /\ log'[server][index] = log[server][index]
                BY <1>types, <3>fields, <3>shape, <3>prefix,
                    AppendProperties, SubSeqProperties, LenProperties, SMT
            <4> QED BY <1>new, <3>fields, <4>bound, <4>below, SMT
        <3>single. Len(request.mentries) = 1
            BY <3>fields, <3>shape, EmptySeq, LenProperties, SMT
        <3>response. [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[server],
                      msuccess |-> TRUE, mmatchIndex |-> index,
                      msource |-> server, mdest |-> request.msource] \in messages'
            BY <1>types, <3>fields, <3>changed, <3>endpoint, <3>single
            DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
        <3> QED BY <3>shape, <3>response DEF EntryAgreementEvidence
    <2>unchanged. CASE log' = log
        BY <1>new, <2>unchanged
    <2> QED BY <2>client, <2>append, <2>unchanged, LogChangingActionNext
<1> QED BY <1>old, <1>new

LEMMA SuccessfulResponseLowerEvidenceInit == Init => SuccessfulResponseLowerEvidenceInv
    BY DEF Init, SuccessfulResponseLowerEvidenceInv

LEMMA PostSameTermEntryIntervals ==
    InductiveInvariant' /\ EntryEdgeConsistency' /\ HistoricalSameTermBoundaryInv' =>
        SameTermEntryIntervalsInv'
<1> SUFFICES ASSUME InductiveInvariant', EntryEdgeConsistency', HistoricalSameTermBoundaryInv',
                    NEW left \in Server, NEW right \in Server,
                    NEW high \in DOMAIN log'[left], NEW low \in DOMAIN log'[right],
                    low <= high, log'[left][high].term = log'[right][low].term
             PROVE /\ low \in DOMAIN log'[left]
                   /\ log'[left][low].term = log'[right][low].term
    BY DEF SameTermEntryIntervalsInv
<1>types. /\ log'[left] \in Seq(LogEntry) /\ log'[right] \in Seq(LogEntry)
            /\ high \in Nat /\ low \in Nat /\ low > 0 /\ high <= Len(log'[left])
    BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>domain. low \in DOMAIN log'[left] BY <1>types, LenProperties, SMT
<1>rightEdge. LogEntryEdge(log'[right], low) \in HistoricalEntryEdges'
    BY DEF HistoricalEntryEdges
<1> DEFINE P(distance) == distance <= high - low =>
        log'[left][high - distance].term = log'[right][low].term
<1>base. P(0) BY <1>types, SMT DEF P
<1>step. \A distance \in Nat: P(distance) => P(distance + 1)
    <2> SUFFICES ASSUME NEW distance \in Nat, P(distance), distance + 1 <= high - low
                 PROVE log'[left][high - (distance + 1)].term = log'[right][low].term
        BY DEF P
    <2>domain. /\ high - distance \in DOMAIN log'[left] /\ low < high - distance
                 /\ high - distance > 1 /\ high - (distance + 1) = high - distance - 1
        BY <1>types, LenProperties, SMT
    <2>term. log'[left][high - distance].term = log'[right][low].term
        BY <1>types, SMT DEF P
    <2>edge. LogEntryEdge(log'[left], high - distance) \in HistoricalEntryEdges'
        BY <2>domain DEF HistoricalEntryEdges
    <2>previous.
        LogEntryEdge(log'[left], high - distance).previous = log'[right][low].term
        BY <1>rightEdge, <2>edge, <2>term, <2>domain
        DEF HistoricalSameTermBoundaryInv, LogEntryEdge
    <2> QED BY <1>types, <2>domain, <2>previous, SMT DEF LogEntryEdge
<1>all. \A distance \in Nat: P(distance) BY <1>base, <1>step, NatInduction
<1>distance. high - low \in Nat /\ high - (high - low) = low
    BY <1>types, SMT
<1>endpoint. P(high - low) BY <1>all, <1>distance
<1>end. log'[left][low].term = log'[right][low].term
    BY <1>distance, <1>endpoint DEF P
<1> QED BY <1>domain, <1>end

LEMMA SuccessfulResponseLowerEvidenceNext ==
    /\ CandidateEntryBaseInv /\ CandidateEntryBaseInv'
    /\ LeaderCompletenessInductionInv /\ CurrentTermReplicaEvidenceInv'
    /\ SuccessfulResponseLowerEvidenceInv /\ [Next]_vars
    => SuccessfulResponseLowerEvidenceInv'
<1> SUFFICES ASSUME CandidateEntryBaseInv, CandidateEntryBaseInv',
                    LeaderCompletenessInductionInv, CurrentTermReplicaEvidenceInv',
                    SuccessfulResponseLowerEvidenceInv, [Next]_vars,
                    NEW leader \in Server, NEW response \in messages',
                    NEW index \in DOMAIN log'[leader], NEW term \in Nat,
                    state'[leader] = Leader, currentTerm'[leader] = term,
                    response.mtype = AppendEntriesResponse, response.msuccess,
                    response.mdest = leader, response.mterm = term,
                    log'[leader][index].term = term, index <= response.mmatchIndex
             PROVE EntryAgreementEvidence(response.msource, index, term)'
    BY DEF SuccessfulResponseLowerEvidenceInv, CandidateEntryBaseInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>types. /\ log \in [Server -> Seq(LogEntry)] /\ log' \in [Server -> Seq(LogEntry)]
            /\ currentTerm \in [Server -> Nat] /\ currentTerm' \in [Server -> Nat]
            /\ response.msource \in Server /\ response.mmatchIndex \in Nat
            /\ index \in Nat /\ index > 0
    BY MessageFieldsTypeOK, LenProperties
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, MsgTypeOK,
        LogVarsTypeOK, ServerVarsTypeOK
<1>oldLeader. state[leader] = Leader
    <2>newLeader. CASE state[leader] # Leader
        <3>election. BecomeLeader(leader)
            BY <2>newLeader, NextCreatesLeaderOnlyByElection DEF CandidateEntryBaseInv
        <3> QED BY <3>election, ServerStatesDistinct
            DEF CandidateEntryBaseInv, CandidateCurrentTermFree, BecomeLeader
    <2>continuing. CASE state[leader] = Leader
        BY <2>continuing
    <2> QED BY <2>newLeader, <2>continuing
<1>term. currentTerm[leader] = term
    BY <1>oldLeader, ContinuingLeaderKeepsTerm DEF CandidateEntryBaseInv
<1>old. CASE response \in messages
    <2>bound. response.mmatchIndex <= Len(log[leader])
        BY <1>old, <1>oldLeader, <1>term DEF CandidateEntryBaseInv,
            InductiveInvariant, ResponseIndexBound
    <2>domain. index \in DOMAIN log[leader]
        BY <1>types, <2>bound, LenProperties, SMT
    <2>copy. log'[leader][index] = log[leader][index]
        BY <1>oldLeader, <2>domain, PersistentLeaderRetainsLogEntries DEF CandidateEntryBaseInv
    <2>evidence. EntryAgreementEvidence(response.msource, index, term)
        BY <1>old, <1>oldLeader, <1>term, <2>domain, <2>copy
        DEF SuccessfulResponseLowerEvidenceInv
    <2> QED BY <1>types, <2>evidence, MessagesMonotonicNext, WonMonotonicNext
        DEF CandidateEntryBaseInv, EntryAgreementEvidence
<1>new. CASE response \notin messages
    <2> PICK request \in AppendRequests:
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        /\ response.mdest = request.msource /\ response.mterm = request.mterm
        BY <1>new, NewSuccessfulAppendResponseOrigin DEF CandidateEntryBaseInv
    <2>fields. /\ request.mdest \in Server /\ request.msource \in Server
               /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
        BY MessageFieldsTypeOK DEF CandidateEntryBaseInv, AppendRequests,
            InductiveInvariant, TypeOK, MsgTypeOK
    <2>sent. response = [mtype |-> AppendEntriesResponse,
                         mterm |-> currentTerm[request.mdest], msuccess |-> TRUE,
                         mmatchIndex |-> request.mprevLogIndex + Len(request.mentries),
                         msource |-> request.mdest, mdest |-> request.msource]
        BY <1>new, <2>fields DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
    <2>frame. log'[leader] = log[leader]
        BY <1>types, <1>oldLeader, <2>fields, <2>sent, SMT
        DEF HandleAppendEntriesRequest
    <2>bound. response.mmatchIndex <= Len(log[leader])
        BY <1>oldLeader, <1>term, <2>sent DEF CandidateEntryBaseInv,
            InductiveInvariant, RequestIndexBound, AppendRequests
    <2>domain. response.mmatchIndex \in DOMAIN log[leader]
        BY <1>types, <2>bound, LenProperties, SMT
    <2>highTerm. log[leader][response.mmatchIndex].term = term
        <3>domainLow. index \in DOMAIN log[leader] BY <2>frame
        <3>lowTerm. log[leader][index].term = term BY <2>frame
        <3>ordered. log[leader][index].term <= log[leader][response.mmatchIndex].term
            BY <3>domainLow, <2>domain DEF CandidateEntryBaseInv, TermOrderingInv, LogTermsMonotonic
        <3>bounded. log[leader][response.mmatchIndex].term <= term
            BY <1>term, <2>domain DEF CandidateEntryBaseInv, InductiveInvariant, LogTermBoundInv
        <3>termType. log[leader][response.mmatchIndex].term \in Nat
            BY <1>types, <2>domain, ElementOfSeq DEF LogEntry
        <3> QED BY <3>termType, <3>lowTerm, <3>ordered, <3>bounded, SMT
    <2> DEFINE high == [index |-> response.mmatchIndex, term |-> term]
    <2>key. high \in HistoricalEntryKeys
        BY <2>domain, <2>highTerm
        DEF high, HistoricalEntryKeys, HistoricalEntryEdges, LogEntryEdge
    <2>anchor. LogHasTermAt(response.msource, term, response.mmatchIndex)'
        BY <1>new, <2>key, NewSuccessfulAppendResponseLogAnchor
        DEF high, CandidateEntryBaseInv, LeaderCompletenessInductionInv, CandidateEntryAuxiliaryInv
    <2>postSupport. /\ InductiveInvariant' /\ EntryEdgeConsistency' /\ HistoricalSameTermBoundaryInv'
        BY DEF CandidateEntryBaseInv
    <2>intervals. SameTermEntryIntervalsInv'
        BY <2>postSupport, PostSameTermEntryIntervals
    <2>low. /\ index \in DOMAIN log'[response.msource]
              /\ log'[response.msource][index].term = term
        BY <1>types, <2>anchor, <2>intervals DEF LogHasTermAt, SameTermEntryIntervalsInv
    <2>sourceTerm. currentTerm'[response.msource] = term
        BY <1>new, <2>sent, NewSuccessfulAppendResponseSourceTerm
        DEF CandidateEntryBaseInv, HandleAppendEntriesRequest
    <2> QED BY <1>types, <2>low, <2>sourceTerm DEF CurrentTermReplicaEvidenceInv
<1> QED BY <1>old, <1>new

LEMMA LeaderAgreeIndexCertified ==
    \A leader \in Server: \A index \in AgreeIndexes(leader):
        /\ CandidateEntryBaseInv /\ LeaderCompletenessInductionInv /\ LeaderAgreementBridgeInv
        /\ state[leader] = Leader /\ log[leader][index].term = currentTerm[leader]
        => [index |-> index, term |-> currentTerm[leader]] \in ClusterAgreeEntries
<1> SUFFICES ASSUME NEW leader \in Server, NEW index \in AgreeIndexes(leader),
                    CandidateEntryBaseInv, LeaderCompletenessInductionInv, LeaderAgreementBridgeInv,
                    state[leader] = Leader, log[leader][index].term = currentTerm[leader]
             PROVE [index |-> index, term |-> currentTerm[leader]] \in ClusterAgreeEntries
    OBVIOUS
<1> DEFINE entry == [index |-> index, term |-> currentTerm[leader]]
<1>types. /\ index \in DOMAIN log[leader] /\ index \in Nat /\ index > 0
            /\ currentTerm[leader] \in Nat /\ Agree(leader, index) \in Quorum
    BY LenProperties DEF AgreeIndexes, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>evidence. \A server \in Agree(leader, index):
        EntryAgreementEvidence(server, index, currentTerm[leader])
    <2> SUFFICES ASSUME NEW server \in Agree(leader, index)
                 PROVE EntryAgreementEvidence(server, index, currentTerm[leader])
        OBVIOUS
    <2>server. server \in Server BY DEF Agree
    <2>self. CASE server = leader
        BY <2>self, ActiveLeaderWon DEF CandidateEntryBaseInv, EntryAgreementEvidence
    <2>other. CASE server # leader
        <3>matched. matchIndex[leader][server] >= index BY <2>other DEF Agree
        <3>matchType. matchIndex[leader][server] \in Nat
            BY <2>server DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LeaderVarsTypeOK
        <3>positive. matchIndex[leader][server] > 0
            BY <1>types, <3>matched, <3>matchType, SMT
        <3> PICK response \in messages:
            /\ response.mtype = AppendEntriesResponse /\ response.msuccess
            /\ response.msource = server /\ response.mdest = leader
            /\ response.mterm = currentTerm[leader]
            /\ response.mmatchIndex = matchIndex[leader][server]
            BY <2>server, <3>positive DEF LeaderAgreementBridgeInv, LeaderMatchResponseInv
        <3> QED BY <1>types, <2>other
            DEF Agree, LeaderAgreementBridgeInv, SuccessfulResponseLowerEvidenceInv
    <2> QED BY <2>self, <2>other
<1>might. Agree(leader, index) \subseteq ClusterMightAgree(index, currentTerm[leader])
    BY <1>evidence DEF Agree, ClusterMightAgree
<1>key. entry \in HistoricalEntryKeys
    BY <1>types DEF entry, HistoricalEntryKeys, HistoricalEntryEdges, LogEntryEdge
<1>candidate. entry \in ClusterAgreeCandidateEntries
    BY <1>types, <1>might, <1>key, QuorumSuperset
    DEF entry, ClusterAgreeCandidateEntries, ClusterMightAgree
<1>replicas. Agree(leader, index) \subseteq ClusterAgree(index, currentTerm[leader])
    BY <1>evidence, <1>candidate
    DEF entry, LeaderCompletenessInductionInv, CandidateEntryJointInv,
        CandidateEntryEvidenceRetainedInv, ClusterAgree, ClusterReplicated,
        EntryAgreementEvidence, LogHasTermAt, Agree
<1>cluster. entry \in ClusterEntries
    BY <1>types DEF entry, ClusterEntries
<1>quorum. ClusterAgree(index, currentTerm[leader]) \in Quorum
    BY <1>types, <1>replicas, QuorumSuperset DEF ClusterAgree, ClusterReplicated
<1> QED BY <1>cluster, <1>quorum DEF entry, ClusterAgreeEntries

LEMMA AgreedReplicaPrefixRetained ==
    CommitCertificateBaseInv /\ [Next]_vars =>
        \A entry \in ClusterAgreeEntries: \A anchor \in ClusterReplicated(entry.index, entry.term):
            /\ entry \in ClusterAgreeEntries'
            /\ anchor \in ClusterReplicated(entry.index, entry.term)'
            /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
<1> SUFFICES ASSUME CommitCertificateBaseInv, [Next]_vars,
                    NEW entry \in ClusterAgreeEntries,
                    NEW anchor \in ClusterReplicated(entry.index, entry.term)
             PROVE /\ entry \in ClusterAgreeEntries'
                   /\ anchor \in ClusterReplicated(entry.index, entry.term)'
                   /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    OBVIOUS
<1>stable. entry \in ClusterAgreeEntries'
    BY ClusterAgreeSupportInvSufficesForNext
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv, StableClusterAgreeEntriesInv
<1>compatible. \A request \in AppendRequests:
        log[anchor][entry.index].term <= request.mterm =>
            AppendRequestPrefixCompatible(request, log[anchor], entry.index)
    BY DEF CommitCertificateBaseInv, ClusterAgreeSupportInv, ClusterAgreeAppendInv, ClusterReplicated
<1>prefix. /\ entry.index \in DOMAIN log'[anchor]
           /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    BY <1>compatible, ProtectedReplicaPrefixNext
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv, ClusterReplicated
<1>types. /\ log[anchor] \in Seq(LogEntry) /\ log'[anchor] \in Seq(LogEntry)
          /\ entry.index \in Nat \ {0}
          /\ entry.index <= Len(log[anchor]) /\ entry.index <= Len(log'[anchor])
    BY <1>prefix, TypeOKNext, LenProperties, SMT
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK, ClusterReplicated
<1>entry. log'[anchor][entry.index] = log[anchor][entry.index]
    BY <1>prefix, <1>types, EqualLogPrefixesEntryEqual
<1> QED BY <1>stable, <1>prefix, <1>entry DEF ClusterReplicated

LEMMA AgreedReplicaShortPrefixRetained ==
    CommitCertificateBaseInv /\ [Next]_vars =>
        \A entry \in ClusterAgreeEntries: \A anchor \in ClusterReplicated(entry.index, entry.term):
            \A endpoint \in 0..entry.index:
                SubSeq(log'[anchor], 1, endpoint) = SubSeq(log[anchor], 1, endpoint)
<1> SUFFICES ASSUME CommitCertificateBaseInv, [Next]_vars,
                    NEW entry \in ClusterAgreeEntries,
                    NEW anchor \in ClusterReplicated(entry.index, entry.term),
                    NEW endpoint \in 0..entry.index
             PROVE SubSeq(log'[anchor], 1, endpoint) = SubSeq(log[anchor], 1, endpoint)
    OBVIOUS
<1>retained. /\ entry.index \in DOMAIN log'[anchor]
             /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    BY AgreedReplicaPrefixRetained DEF ClusterReplicated
<1>types. /\ log[anchor] \in Seq(LogEntry) /\ log'[anchor] \in Seq(LogEntry)
          /\ entry.index \in Nat \ {0}
          /\ endpoint \in Nat /\ endpoint <= entry.index
          /\ entry.index <= Len(log[anchor]) /\ entry.index <= Len(log'[anchor])
    BY <1>retained, TypeOKNext, LenProperties, SMT
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK, ClusterReplicated
<1>zero. CASE endpoint = 0
    BY <1>zero, <1>types, SubSeqProperties, EmptySeq
<1>positive. CASE endpoint > 0
    <2>prefixTypes. /\ SubSeq(log[anchor], 1, entry.index) \in Seq(LogEntry)
                    /\ SubSeq(log'[anchor], 1, entry.index) \in Seq(LogEntry)
                    /\ Len(SubSeq(log[anchor], 1, entry.index)) = entry.index
                    /\ Len(SubSeq(log'[anchor], 1, entry.index)) = entry.index
        BY <1>types, SubSeqProperties, ElementOfSeq
    <2>left. SubSeq(SubSeq(log[anchor], 1, entry.index), 1, endpoint)
                  = SubSeq(log[anchor], 1, endpoint)
        BY <1>types, <1>positive, <2>prefixTypes, SubSeqOfSubSeq
    <2>right. SubSeq(SubSeq(log'[anchor], 1, entry.index), 1, endpoint)
                   = SubSeq(log'[anchor], 1, endpoint)
        BY <1>types, <1>positive, <2>prefixTypes, SubSeqOfSubSeq
    <2> QED BY <1>retained, <2>left, <2>right
<1> QED BY <1>zero, <1>positive, <1>types, SMT

LEMMA RequestCertificateRetained ==
    CommitCertificateBaseInv /\ [Next]_vars =>
        \A request \in AppendRequests: \A entry \in ClusterAgreeEntries: \A anchor \in Server:
            RequestCertificate(request, entry, anchor) => RequestCertificate(request, entry, anchor)'
<1> SUFFICES ASSUME CommitCertificateBaseInv, [Next]_vars,
                    NEW request \in AppendRequests, NEW entry \in ClusterAgreeEntries,
                    NEW anchor \in Server, RequestCertificate(request, entry, anchor)
             PROVE RequestCertificate(request, entry, anchor)'
    OBVIOUS
<1>retained. /\ entry \in ClusterAgreeEntries'
             /\ anchor \in ClusterReplicated(entry.index, entry.term)'
             /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    BY AgreedReplicaPrefixRetained DEF RequestCertificate
<1>types. /\ log[anchor] \in Seq(LogEntry) /\ log'[anchor] \in Seq(LogEntry)
          /\ request.mprevLogIndex \in Nat /\ entry.index \in Nat \ {0}
          /\ entry.index <= Len(log[anchor]) /\ entry.index <= Len(log'[anchor])
    BY <1>retained, TypeOKNext, MessageFieldsTypeOK, LenProperties, SMT
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK, MsgTypeOK, AppendRequests, RequestCertificate, ClusterReplicated
<1>bounds. /\ entry.term <= request.mterm /\ request.mcommitIndex <= entry.index
    BY DEF RequestCertificate
<1>before. CASE request.mprevLogIndex < entry.index
    <2>positions. /\ request.mprevLogIndex + 1 \in 1..entry.index
                  /\ request.mprevLogIndex > 0 => request.mprevLogIndex \in 1..entry.index
        BY <1>types, <1>before, SMT
    <2>equal. /\ log'[anchor][request.mprevLogIndex + 1] = log[anchor][request.mprevLogIndex + 1]
              /\ request.mprevLogIndex > 0 =>
                     log'[anchor][request.mprevLogIndex] = log[anchor][request.mprevLogIndex]
        BY <1>types, <1>retained, <2>positions, EqualLogPrefixesEntryEqual
    <2> QED BY <1>retained, <1>before, <2>equal DEF RequestCertificate
<1>after. CASE request.mprevLogIndex >= entry.index
    BY <1>retained, <1>after, <1>bounds, <1>types, SMT DEF RequestCertificate
<1> QED BY <1>before, <1>after, <1>types, SMT

LEMMA ClientRequestRetainsCommitPrefix ==
    \A server \in Server: \A value \in Value:
        InductiveInvariant /\ commitIndex[server] <= Len(log[server]) /\ ClientRequest(server, value) =>
            /\ commitIndex'[server] = commitIndex[server]
            /\ SubSeq(log'[server], 1, commitIndex[server])
                   = SubSeq(log[server], 1, commitIndex[server])
<1> SUFFICES ASSUME NEW server \in Server, NEW value \in Value,
                    InductiveInvariant, commitIndex[server] <= Len(log[server]), ClientRequest(server, value)
             PROVE /\ commitIndex'[server] = commitIndex[server]
                   /\ SubSeq(log'[server], 1, commitIndex[server])
                          = SubSeq(log[server], 1, commitIndex[server])
    OBVIOUS
<1>types. /\ log[server] \in Seq(LogEntry) /\ commitIndex[server] \in Nat
          /\ commitIndex[server] <= Len(log[server])
          /\ [term |-> currentTerm[server], value |-> value] \in LogEntry
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK,
        LogEntry
<1>shape. /\ commitIndex'[server] = commitIndex[server]
          /\ log'[server] = Append(log[server], [term |-> currentTerm[server], value |-> value])
    BY SMT DEF ClientRequest, InductiveInvariant, TypeOK, LogVarsTypeOK
<1>zero. CASE commitIndex[server] = 0
    BY <1>zero, <1>types, <1>shape, AppendProperties, SubSeqProperties, EmptySeq
<1>positive. CASE commitIndex[server] > 0
    <2>domain. commitIndex[server] \in 1..Len(log[server])
        BY <1>types, <1>positive, SMT
    <2> QED BY <2>domain, <1>types, <1>shape, AppendRetainsLogPrefix
<1> QED BY <1>zero, <1>positive, <1>types, SMT

LEMMA CommitCertificatesInit == Init => CommitCertificatesInv
    BY DEF Init, InitLogVars, CommittedCertificateInv, RequestCertificateInv,
        CommitCertificatesInv, AppendRequests


LEMMA AppendSendBeforeEndpointPayload ==
    \A sender, recipient \in Server: \A endpoint \in DOMAIN log[sender]:
        /\ InductiveInvariant /\ AppendEntries(sender, recipient)
        /\ AppendEntriesMessage(sender, recipient).mprevLogIndex < endpoint
        => /\ AppendEntriesMessage(sender, recipient).mentries # << >>
           /\ 1 \in DOMAIN AppendEntriesMessage(sender, recipient).mentries
           /\ AppendEntriesMessage(sender, recipient).mentries[1]
                  = log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    NEW endpoint \in DOMAIN log[sender], InductiveInvariant,
                    AppendEntries(sender, recipient),
                    AppendEntriesMessage(sender, recipient).mprevLogIndex < endpoint
             PROVE /\ AppendEntriesMessage(sender, recipient).mentries # << >>
                   /\ 1 \in DOMAIN AppendEntriesMessage(sender, recipient).mentries
                   /\ AppendEntriesMessage(sender, recipient).mentries[1]
                          = log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
    BY SMT
<1>types. /\ log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat
          /\ nextIndex[sender][recipient] \in Nat \ {0}
          /\ endpoint \in 1..Len(log[sender])
    BY LenProperties DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LeaderVarsTypeOK
<1>bound. nextIndex[sender][recipient] <= Len(log[sender])
    BY <1>types, SMT DEF AppendEntriesMessage
<1>last. AppendEntriesLastEntry(sender, recipient) = nextIndex[sender][recipient]
    BY <1>types, <1>bound, MinTypeOK, SMT DEF AppendEntriesLastEntry, Min
<1>element. log[sender][nextIndex[sender][recipient]] \in LogEntry
    BY <1>types, <1>bound, ElementOfSeq, SMT
<1>length. Len(AppendEntriesEntries(sender, recipient)) = 1
    BY <1>types, <1>last, <1>element, SubSeqProperties, SMT DEF AppendEntriesEntries
<1>payloadType. AppendEntriesEntries(sender, recipient) \in Seq(LogEntry)
    BY AppendEntriesEntriesTypeOK DEF InductiveInvariant
<1>nonempty. /\ AppendEntriesMessage(sender, recipient).mentries # << >>
             /\ 1 \in DOMAIN AppendEntriesMessage(sender, recipient).mentries
    BY <1>length, <1>payloadType, EmptySeq, LenProperties, SMT DEF AppendEntriesMessage
<1> QED BY <1>nonempty, AppendEntriesSenderSnapshot

LEMMA AppendSendCertificatePrefixFields ==
    \A sender, recipient, anchor \in Server: \A entry \in ClusterAgreeEntries:
        /\ CandidateEntryBaseInv /\ ClusterAgreeSupportInv
        /\ CommitCertificate(sender, entry, anchor) /\ AppendEntries(sender, recipient)
        /\ AppendEntriesMessage(sender, recipient).mprevLogIndex < entry.index
        => /\ AppendEntriesMessage(sender, recipient).mprevLogIndex > 0 =>
                  AppendEntriesMessage(sender, recipient).mprevLogTerm
                      = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex].term
           /\ AppendEntriesMessage(sender, recipient).mentries # << >>
           /\ AppendEntriesMessage(sender, recipient).mentries[1]
                  = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    NEW anchor \in Server, NEW entry \in ClusterAgreeEntries,
                    CandidateEntryBaseInv, ClusterAgreeSupportInv,
                    CommitCertificate(sender, entry, anchor), AppendEntries(sender, recipient),
                    AppendEntriesMessage(sender, recipient).mprevLogIndex < entry.index
             PROVE /\ AppendEntriesMessage(sender, recipient).mprevLogIndex > 0 =>
                          AppendEntriesMessage(sender, recipient).mprevLogTerm
                              = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex].term
                   /\ AppendEntriesMessage(sender, recipient).mentries # << >>
                   /\ AppendEntriesMessage(sender, recipient).mentries[1]
                          = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
    BY SMT
<1>shared. SharedLogPrefix(sender, anchor, entry.index)
    BY LeaderClusterAgreeGivesSharedPrefix
    DEF CandidateEntryBaseInv, ClusterAgreeSupportInv, CommitCertificate, AppendEntries
<1>types. /\ log[sender] \in Seq(LogEntry) /\ log[anchor] \in Seq(LogEntry)
          /\ entry.index \in Nat /\ entry.index <= Len(log[sender])
          /\ entry.index <= Len(log[anchor])
          /\ AppendEntriesMessage(sender, recipient).mprevLogIndex \in Nat
    BY <1>shared, LenProperties, SMT
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK,
        LeaderVarsTypeOK, AppendEntriesMessage, SharedLogPrefix
<1>payload. /\ AppendEntriesMessage(sender, recipient).mentries # << >>
            /\ AppendEntriesMessage(sender, recipient).mentries[1]
                   = log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
    BY <1>shared, AppendSendBeforeEndpointPayload DEF CandidateEntryBaseInv, SharedLogPrefix
<1>entryEqual. log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
                  = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex + 1]
    BY <1>types, <1>shared, EqualLogPrefixesEntryEqual, SMT DEF SharedLogPrefix
<1>header. AppendEntriesMessage(sender, recipient).mprevLogIndex > 0 =>
              AppendEntriesMessage(sender, recipient).mprevLogTerm
                  = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex].term
    <2> SUFFICES ASSUME AppendEntriesMessage(sender, recipient).mprevLogIndex > 0
                 PROVE AppendEntriesMessage(sender, recipient).mprevLogTerm
                           = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex].term
        BY SMT
    <2>equal. log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex]
                 = log[anchor][AppendEntriesMessage(sender, recipient).mprevLogIndex]
        BY <1>types, <1>shared, EqualLogPrefixesEntryEqual, SMT DEF SharedLogPrefix
    <2> QED BY <2>equal, AppendEntriesSenderSnapshot DEF CandidateEntryBaseInv
<1> QED BY <1>payload, <1>entryEqual, <1>header

LEMMA AppendSendCertificateCoveredHeader ==
    \A sender, recipient, anchor \in Server: \A entry \in ClusterAgreeEntries:
        /\ CandidateEntryBaseInv /\ ClusterAgreeSupportInv
        /\ CommitCertificate(sender, entry, anchor) /\ AppendEntries(sender, recipient)
        /\ entry.index <= AppendEntriesMessage(sender, recipient).mprevLogIndex
        => entry.term <= AppendEntriesMessage(sender, recipient).mprevLogTerm
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    NEW anchor \in Server, NEW entry \in ClusterAgreeEntries,
                    CandidateEntryBaseInv, ClusterAgreeSupportInv,
                    CommitCertificate(sender, entry, anchor), AppendEntries(sender, recipient),
                    entry.index <= AppendEntriesMessage(sender, recipient).mprevLogIndex
             PROVE entry.term <= AppendEntriesMessage(sender, recipient).mprevLogTerm
    BY SMT
<1>entry. /\ entry.index \in DOMAIN log[sender]
          /\ log[sender][entry.index].term = entry.term
    BY DEF ClusterAgreeSupportInv, LeaderClusterAgreeInv, CommitCertificate, AppendEntries
<1>types. /\ log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat
          /\ entry.index \in 1..Len(log[sender])
          /\ nextIndex[sender][recipient] \in Nat \ {0}
          /\ nextIndex[sender][recipient] <= Len(log[sender]) + 1
    BY <1>entry, LenProperties
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK,
        LeaderVarsTypeOK, NextIndexBound, AppendEntries
<1>previous. /\ AppendEntriesMessage(sender, recipient).mprevLogIndex \in DOMAIN log[sender]
             /\ AppendEntriesMessage(sender, recipient).mprevLogIndex > 0
    BY <1>types, LenProperties, SMT DEF AppendEntriesMessage
<1>ordered. entry.term <= log[sender][AppendEntriesMessage(sender, recipient).mprevLogIndex].term
    BY <1>entry, <1>previous DEF CandidateEntryBaseInv, TermOrderingInv, LogTermsMonotonic
<1> QED BY <1>ordered, <1>previous, AppendEntriesSenderSnapshot DEF CandidateEntryBaseInv

----

LEMMA SendCommitCertificateRequest ==
    \A sender, recipient, anchor \in Server: \A entry \in ClusterAgreeEntries:
        /\ CandidateEntryBaseInv /\ ClusterAgreeSupportInv
        /\ CommitCertificate(sender, entry, anchor) /\ AppendEntries(sender, recipient)
        => RequestCertificate(AppendEntriesMessage(sender, recipient), entry, anchor)
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    NEW anchor \in Server, NEW entry \in ClusterAgreeEntries,
                    CandidateEntryBaseInv, ClusterAgreeSupportInv,
                    CommitCertificate(sender, entry, anchor), AppendEntries(sender, recipient)
             PROVE RequestCertificate(AppendEntriesMessage(sender, recipient), entry, anchor)
    BY SMT
<1>commitType. commitIndex[sender] \in Nat
    BY DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
<1>lastType. AppendEntriesLastEntry(sender, recipient) \in Nat
    BY AppendEntriesLastEntryTypeOK DEF CandidateEntryBaseInv, InductiveInvariant
<1>previousType. AppendEntriesMessage(sender, recipient).mprevLogIndex \in Nat
    BY SMT DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
        LeaderVarsTypeOK, AppendEntriesMessage
<1>entryType. entry.index \in Nat
    BY LenProperties DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK,
        LogVarsTypeOK, CommitCertificate, ClusterReplicated
<1>types. /\ commitIndex[sender] \in Nat
          /\ AppendEntriesLastEntry(sender, recipient) \in Nat
          /\ AppendEntriesMessage(sender, recipient).mprevLogIndex \in Nat
          /\ entry.index \in Nat
    BY <1>commitType, <1>lastType, <1>previousType, <1>entryType
<1>bounds. /\ entry \in ClusterAgreeEntries
           /\ anchor \in ClusterReplicated(entry.index, entry.term)
           /\ entry.term <= AppendEntriesMessage(sender, recipient).mterm
           /\ AppendEntriesMessage(sender, recipient).mcommitIndex <= entry.index
    BY <1>types, MinTypeOK, SMT DEF CommitCertificate, AppendEntriesMessage
<1>before. CASE AppendEntriesMessage(sender, recipient).mprevLogIndex < entry.index
    BY <1>before, <1>bounds, AppendSendCertificatePrefixFields DEF RequestCertificate
<1>covered. CASE entry.index <= AppendEntriesMessage(sender, recipient).mprevLogIndex
    <2>header. entry.term <= AppendEntriesMessage(sender, recipient).mprevLogTerm
        BY <1>covered, AppendSendCertificateCoveredHeader
    <2> QED BY <1>covered, <1>bounds, <1>types, <2>header, SMT DEF RequestCertificate
<1> QED BY <1>before, <1>covered, <1>types, SMT

LEMMA CertifiedRequestTypes ==
    InductiveInvariant => \A request \in AppendRequests:
        /\ request \in messages /\ request.mtype = AppendEntriesRequest
        /\ request.msource \in Server /\ request.mdest \in Server
        /\ request.mprevLogIndex \in Nat /\ request.mprevLogTerm \in Nat
        /\ request.mterm \in Nat /\ request.mcommitIndex \in Nat
        /\ request.mentries \in Seq(LogEntry)
        /\ Len(request.mentries) <= 1
        /\ request.mcommitIndex <= request.mprevLogIndex + Len(request.mentries)
    BY MessageFieldsTypeOK
    DEF InductiveInvariant, TypeOK, MsgTypeOK, AppendRequests, RequestCommitIndexBound

LEMMA EqualCertifiedPrefixesShorten ==
    \A left, right \in Seq(LogEntry): \A endpoint \in 0..Len(left):
        \A cut \in 0..endpoint:
            endpoint <= Len(right) /\ SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
            => SubSeq(left, 1, cut) = SubSeq(right, 1, cut)
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    NEW endpoint \in 0..Len(left), NEW cut \in 0..endpoint,
                    endpoint <= Len(right),
                    SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
             PROVE SubSeq(left, 1, cut) = SubSeq(right, 1, cut)
    BY SMT
<1>types. /\ endpoint \in 0..Len(right) /\ cut \in Nat
    BY LenProperties, SMT
<1>take. /\ SubSeq(left, 1, endpoint) \in Seq(LogEntry)
          /\ Len(SubSeq(left, 1, endpoint)) = endpoint
          /\ IsPrefix(SubSeq(left, 1, endpoint), left)
          /\ IsPrefix(SubSeq(right, 1, endpoint), right)
    BY <1>types, SequencePrefixTake
<1> QED BY <1>take, SequencePrefixShorten

LEMMA CertifiedPrefixSuccessor ==
    \A entries \in Seq(LogEntry): \A cut \in 0..Len(entries):
        cut < Len(entries) =>
            SubSeq(entries, 1, cut + 1) = Append(SubSeq(entries, 1, cut), entries[cut + 1])
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW cut \in 0..Len(entries),
                    cut < Len(entries)
             PROVE SubSeq(entries, 1, cut + 1) = Append(SubSeq(entries, 1, cut), entries[cut + 1])
    BY SMT
<1>types. /\ cut \in Nat /\ cut + 1 \in 1..Len(entries)
          /\ entries[cut + 1] \in LogEntry
    BY LenProperties, ElementOfSeq, SMT
<1>take. /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
         /\ Len(SubSeq(entries, 1, cut)) = cut
         /\ SubSeq(entries, 1, cut + 1) \in Seq(LogEntry)
         /\ Len(SubSeq(entries, 1, cut + 1)) = cut + 1
    BY <1>types, SequencePrefixTake, SMT
<1>pointwise. \A index \in 1..(cut + 1):
        SubSeq(entries, 1, cut + 1)[index] =
            Append(SubSeq(entries, 1, cut), entries[cut + 1])[index]
    <2> SUFFICES ASSUME NEW index \in 1..(cut + 1)
                 PROVE SubSeq(entries, 1, cut + 1)[index] =
                     Append(SubSeq(entries, 1, cut), entries[cut + 1])[index]
        BY SMT
    <2>old. CASE index <= cut
        <3>sub. /\ SubSeq(entries, 1, cut + 1)[index] = entries[index]
                 /\ SubSeq(entries, 1, cut)[index] = entries[index]
            BY <1>types, <1>take, <2>old, SubSeqProperties, SMT
        <3> QED BY <1>take, <2>old, <3>sub, AppendProperties, SMT
    <2>new. CASE index = cut + 1
        <3>sub. SubSeq(entries, 1, cut + 1)[index] = entries[index]
            BY <1>types, <1>take, <2>new, SubSeqProperties, SMT
        <3> QED BY <1>take, <2>new, <3>sub, AppendProperties, SMT
    <2> QED BY <2>old, <2>new, <1>types, SMT
<1> QED BY <1>types, <1>take, <1>pointwise, AppendProperties, SeqEqual, SMT

LEMMA AcceptedCertifiedRequestPostFacts ==
    InductiveInvariant => \A recipient, sender \in Server: \A request \in AppendRequests:
        AcceptedCertifiedRequest(recipient, sender, request) =>
            /\ request.mprevLogIndex \in 0..Len(log[recipient])
            /\ commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                       THEN request.mcommitIndex ELSE commitIndex[recipient]
            /\ currentTerm'[recipient] = request.mterm
            /\ log'[recipient] \in Seq(LogEntry)
<1> SUFFICES ASSUME InductiveInvariant, NEW recipient \in Server, NEW sender \in Server,
                    NEW request \in AppendRequests,
                    AcceptedCertifiedRequest(recipient, sender, request)
             PROVE /\ request.mprevLogIndex \in 0..Len(log[recipient])
                   /\ commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                              THEN request.mcommitIndex ELSE commitIndex[recipient]
                   /\ currentTerm'[recipient] = request.mterm
                   /\ log'[recipient] \in Seq(LogEntry)
    BY SMT
<1>types. /\ request.mprevLogIndex \in Nat /\ request \in messages
          /\ request.mtype = AppendEntriesRequest
          /\ commitIndex \in [Server -> Nat] /\ currentTerm \in [Server -> Nat]
          /\ log[recipient] \in Seq(LogEntry)
    BY CertifiedRequestTypes DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>logType. log'[recipient] \in Seq(LogEntry)
    BY <1>types, HandleAppendEntriesRequestLogVarsTypeOK
    DEF AcceptedCertifiedRequest, InductiveInvariant, LogVarsTypeOK
<1>bound. request.mprevLogIndex \in 0..Len(log[recipient])
    BY <1>types, LenProperties, SMT DEF AcceptedCertifiedRequest
<1>term. currentTerm'[recipient] = request.mterm
    BY <1>types, SMT DEF AcceptedCertifiedRequest, HandleAppendEntriesRequest
<1>commit. commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                  THEN request.mcommitIndex ELSE commitIndex[recipient]
    BY <1>types, SMT DEF AcceptedCertifiedRequest, HandleAppendEntriesRequest
<1> QED BY <1>bound, <1>term, <1>commit, <1>logType

LEMMA AcceptedCertifiedRequestFirstEntry ==
    InductiveInvariant /\ EntryEdgeConsistency =>
        \A recipient, sender \in Server: \A request \in AppendRequests:
            AcceptedCertifiedRequest(recipient, sender, request) /\ request.mentries # << >> =>
                /\ request.mprevLogIndex + 1 \in DOMAIN log'[recipient]
                /\ log'[recipient][request.mprevLogIndex + 1] = request.mentries[1]
<1> SUFFICES ASSUME InductiveInvariant, EntryEdgeConsistency,
                    NEW recipient \in Server, NEW sender \in Server,
                    NEW request \in AppendRequests,
                    AcceptedCertifiedRequest(recipient, sender, request), request.mentries # << >>
             PROVE /\ request.mprevLogIndex + 1 \in DOMAIN log'[recipient]
                   /\ log'[recipient][request.mprevLogIndex + 1] = request.mentries[1]
    BY SMT
<1>types. /\ request \in messages /\ request.mtype = AppendEntriesRequest
          /\ request.mprevLogIndex \in Nat /\ request.mentries \in Seq(LogEntry)
          /\ log[recipient] \in Seq(LogEntry)
          /\ log \in [Server -> Seq(LogEntry)]
          /\ log'[recipient] \in Seq(LogEntry)
          /\ request.mprevLogIndex <= Len(log[recipient])
    BY CertifiedRequestTypes, AcceptedCertifiedRequestPostFacts
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>offset. 1 \in DOMAIN request.mentries
    BY <1>types, LenProperties, EmptySeq, SMT
<1>changed. CASE log' # log
    <2>length. Len(log'[recipient]) = request.mprevLogIndex + 1
        BY <1>types, <1>changed, AppendRequestChangedLogShape DEF AcceptedCertifiedRequest
    <2>entry. log'[recipient][request.mprevLogIndex + 1] = request.mentries[1]
        BY <1>types, <1>changed, AppendRequestCopiesEndpointEntry DEF AcceptedCertifiedRequest
    <2> QED BY <1>types, <2>length, <2>entry, LenProperties, SMT
<1>unchanged. CASE log' = log
    <2>take. /\ SubSeq(log[recipient], 1, request.mprevLogIndex) \in Seq(LogEntry)
             /\ Len(SubSeq(log[recipient], 1, request.mprevLogIndex)) = request.mprevLogIndex
             /\ request.mentries[1] \in LogEntry
        BY <1>types, <1>offset, SequencePrefixTake, ElementOfSeq, SMT
    <2>guard. ~ (Len(log[recipient]) = request.mprevLogIndex
                \/ log[recipient][request.mprevLogIndex + 1].term # request.mentries[1].term)
        <3> SUFFICES ASSUME Len(log[recipient]) = request.mprevLogIndex
                           \/ log[recipient][request.mprevLogIndex + 1].term # request.mentries[1].term
                     PROVE FALSE
            BY SMT
        <3>shape. log[recipient] = Append(SubSeq(log[recipient], 1, request.mprevLogIndex), request.mentries[1])
            BY <1>types, <1>unchanged, SMT DEF AcceptedCertifiedRequest, HandleAppendEntriesRequest
        <3>length. Len(log[recipient]) = request.mprevLogIndex + 1
            BY <2>take, <3>shape, AppendProperties, SMT
        <3>last. log[recipient][request.mprevLogIndex + 1] = request.mentries[1]
            BY <2>take, <3>shape, AppendProperties, SMT
        <3> QED BY <1>types, <3>length, <3>last, SMT
    <2>same. /\ request.mprevLogIndex < Len(log[recipient])
             /\ log[recipient][request.mprevLogIndex + 1].term = request.mentries[1].term
        BY <1>types, <2>guard, LenProperties, SMT
    <2>domain. request.mprevLogIndex + 1 \in DOMAIN log[recipient]
        BY <1>types, <2>same, LenProperties, SMT
    <2>edges. /\ LogEntryEdge(log[recipient], request.mprevLogIndex + 1) \in HistoricalEntryEdges
              /\ RequestEntryEdge(request, 1) \in HistoricalEntryEdges
        BY <2>domain, <1>offset DEF HistoricalEntryEdges
    <2>equal. log[recipient][request.mprevLogIndex + 1] = request.mentries[1]
        BY <2>edges, <2>same, SMT DEF EntryEdgeConsistency, LogEntryEdge, RequestEntryEdge
    <2> QED BY <2>domain, <2>equal, <1>unchanged
<1> QED BY <1>changed, <1>unchanged

LEMMA AcceptedRequestCertifiedPrefix ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv =>
        \A recipient, sender, anchor \in Server: \A request \in AppendRequests:
            \A entry \in ClusterAgreeEntries:
                AcceptedCertifiedRequest(recipient, sender, request) /\ RequestCertificate(request, entry, anchor)
                => /\ commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                               THEN request.mcommitIndex ELSE commitIndex[recipient]
                   /\ currentTerm'[recipient] = request.mterm
                   /\ request.mcommitIndex <= Len(log'[recipient])
                   /\ SubSeq(log'[recipient], 1, request.mcommitIndex)
                          = SubSeq(log[anchor], 1, request.mcommitIndex)
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                    NEW recipient \in Server, NEW sender \in Server, NEW anchor \in Server,
                    NEW request \in AppendRequests, NEW entry \in ClusterAgreeEntries,
                    AcceptedCertifiedRequest(recipient, sender, request), RequestCertificate(request, entry, anchor)
             PROVE /\ commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                              THEN request.mcommitIndex ELSE commitIndex[recipient]
                   /\ currentTerm'[recipient] = request.mterm
                   /\ request.mcommitIndex <= Len(log'[recipient])
                   /\ SubSeq(log'[recipient], 1, request.mcommitIndex)
                          = SubSeq(log[anchor], 1, request.mcommitIndex)
    BY SMT
<1>inductive. /\ InductiveInvariant /\ EntryEdgeConsistency /\ LogMatchingInv
              /\ HistoricalSameTermBoundaryInv /\ HistoricalNewerEntryBoundaryInv
    BY DEF CandidateEntryBaseInv, LeaderCompletenessInductionInv, CandidateEntryJointInv
<1>types. /\ log[recipient] \in Seq(LogEntry) /\ log[anchor] \in Seq(LogEntry)
          /\ log'[recipient] \in Seq(LogEntry)
          /\ request.mprevLogIndex \in 0..Len(log[recipient])
          /\ request.mcommitIndex \in Nat /\ request.mprevLogIndex \in Nat
          /\ request.mprevLogTerm \in Nat /\ entry.index \in Nat /\ entry.term \in Nat
          /\ entry.index \in DOMAIN log[anchor] /\ log[anchor][entry.index].term = entry.term
          /\ request \in messages /\ request.mtype = AppendEntriesRequest
          /\ request.mentries \in Seq(LogEntry) /\ Len(request.mentries) <= 1
          /\ request.mcommitIndex <= request.mprevLogIndex + Len(request.mentries)
          /\ request.mcommitIndex <= entry.index
    <2>logs. /\ log[recipient] \in Seq(LogEntry) /\ log[anchor] \in Seq(LogEntry)
        BY <1>inductive DEF InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>request. /\ request \in messages /\ request.mtype = AppendEntriesRequest
                 /\ request.mprevLogIndex \in Nat /\ request.mprevLogTerm \in Nat
                 /\ request.mcommitIndex \in Nat /\ request.mentries \in Seq(LogEntry)
                 /\ Len(request.mentries) <= 1
                 /\ request.mcommitIndex <= request.mprevLogIndex + Len(request.mentries)
        BY <1>inductive, CertifiedRequestTypes
    <2>post. /\ request.mprevLogIndex \in 0..Len(log[recipient])
              /\ log'[recipient] \in Seq(LogEntry)
        BY <1>inductive, AcceptedCertifiedRequestPostFacts
    <2>anchor. /\ entry.index \in DOMAIN log[anchor]
                /\ log[anchor][entry.index].term = entry.term
                /\ request.mcommitIndex <= entry.index
        BY DEF RequestCertificate, ClusterReplicated
    <2>entryTypes. /\ entry.index \in Nat /\ entry.term \in Nat
        BY <2>logs, <2>anchor, LenProperties, ElementOfSeq, SMT DEF LogEntry
    <2> QED BY <2>logs, <2>request, <2>post, <2>anchor, <2>entryTypes
<1>postFacts. /\ commitIndex'[recipient] = IF request.mcommitIndex > commitIndex[recipient]
                                        THEN request.mcommitIndex ELSE commitIndex[recipient]
              /\ currentTerm'[recipient] = request.mterm
    BY <1>inductive, AcceptedCertifiedRequestPostFacts
<1>before. CASE request.mprevLogIndex < entry.index
    <2>prefix. SubSeq(log[recipient], 1, request.mprevLogIndex)
                  = SubSeq(log[anchor], 1, request.mprevLogIndex)
        BY <1>types, <1>before, <1>inductive, SubSeqEmpty, LenProperties, SMT
        DEF RequestCertificate, AcceptedCertifiedRequest, LogMatchingInv
    <2>first. /\ request.mentries # << >>
               /\ request.mentries[1] = log[anchor][request.mprevLogIndex + 1]
               /\ request.mprevLogIndex + 1 \in DOMAIN log'[recipient]
               /\ log'[recipient][request.mprevLogIndex + 1] = request.mentries[1]
        BY <1>inductive, <1>before, AcceptedCertifiedRequestFirstEntry DEF RequestCertificate
    <2>retained. SubSeq(log'[recipient], 1, request.mprevLogIndex)
                    = SubSeq(log[recipient], 1, request.mprevLogIndex)
        BY <1>types, <1>inductive, AppendRequestRetainsMatchedPrefix, SubSeqEmpty, SMT
        DEF AcceptedCertifiedRequest
    <2>bounds. /\ request.mprevLogIndex + 1 \in 0..Len(log'[recipient])
                /\ request.mprevLogIndex + 1 \in 0..Len(log[anchor])
                /\ request.mcommitIndex \in 0..(request.mprevLogIndex + 1)
        BY <1>types, <2>first, <1>before, LenProperties, SMT
    <2>extended. SubSeq(log'[recipient], 1, request.mprevLogIndex + 1)
                    = SubSeq(log[anchor], 1, request.mprevLogIndex + 1)
        <3>postSuccessor. SubSeq(log'[recipient], 1, request.mprevLogIndex + 1)
                             = Append(SubSeq(log'[recipient], 1, request.mprevLogIndex),
                                      log'[recipient][request.mprevLogIndex + 1])
            BY <1>types, <2>bounds, CertifiedPrefixSuccessor, SMT
        <3>anchorSuccessor. SubSeq(log[anchor], 1, request.mprevLogIndex + 1)
                               = Append(SubSeq(log[anchor], 1, request.mprevLogIndex),
                                        log[anchor][request.mprevLogIndex + 1])
            BY <1>types, <2>bounds, CertifiedPrefixSuccessor, SMT
        <3> QED BY <3>postSuccessor, <3>anchorSuccessor, <2>prefix, <2>retained, <2>first
    <2> QED BY <1>postFacts, <1>types, <2>bounds, <2>extended, EqualCertifiedPrefixesShorten, SMT
<1>after. CASE entry.index <= request.mprevLogIndex
    <2>header. /\ request.mprevLogIndex \in DOMAIN log[recipient]
                /\ log[recipient][request.mprevLogIndex].term = request.mprevLogTerm
                /\ entry.term <= request.mprevLogTerm
        BY <1>types, <1>inductive, <1>after, LenProperties, SMT
        DEF RequestCertificate, AcceptedCertifiedRequest
    <2>derived. /\ SameTermEntryIntervalsInv /\ CandidateNewerLogPrefixesInv
                 /\ entry \in ClusterAgreeCandidateEntries
        BY <1>inductive, HistoricalSameTermBoundaryImpliesIntervals,
           HistoricalBoundaryImpliesCandidateNewerPrefixes, ClusterAgreeEntriesAreCandidateEntries
    <2>replica. /\ entry.index \in DOMAIN log[recipient]
                 /\ log[recipient][entry.index].term = entry.term
        BY <1>types, <1>after, <2>header, <2>derived, SMT
        DEF SameTermEntryIntervalsInv, CandidateNewerLogPrefixesInv, LogHasTermAt
    <2>prefix. SubSeq(log[recipient], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
        <3>bounds. /\ entry.index \in 1..Len(log[recipient])
                   /\ entry.index \in 1..Len(log[anchor])
            BY <1>types, <2>replica, LenProperties, SMT
        <3>sameTerm. log[recipient][entry.index].term = log[anchor][entry.index].term
            BY <1>types, <2>replica
        <3>matching. LogMatchingInv
            BY <1>inductive
        <3> QED BY <3>bounds, <3>sameTerm, <3>matching DEF LogMatchingInv
    <2>retained. SubSeq(log'[recipient], 1, entry.index) = SubSeq(log[recipient], 1, entry.index)
        BY <1>types, <1>after, <1>inductive, LenProperties, AppendRequestRetainsMatchedPrefix, SMT
        DEF AcceptedCertifiedRequest
    <2>postBound. entry.index \in 0..Len(log'[recipient])
        BY <1>types, <1>after, <2>replica, <1>inductive, AppendRequestChangedLogShape, LenProperties, SMT
        DEF AcceptedCertifiedRequest
    <2> QED BY <1>postFacts, <1>types, <2>prefix, <2>retained, <2>postBound,
        EqualCertifiedPrefixesShorten, SMT
<1> QED BY <1>types, <1>before, <1>after, SMT

LEMMA AcceptedRequestTransfersCommitCertificate ==
    CandidateEntryBaseInv /\ LeaderCompletenessInductionInv =>
        \A recipient, sender, anchor \in Server: \A request \in AppendRequests:
            \A entry \in ClusterAgreeEntries:
                /\ AcceptedCertifiedRequest(recipient, sender, request)
                /\ RequestCertificate(request, entry, anchor)
                /\ commitIndex[recipient] <= request.mcommitIndex
                /\ entry \in ClusterAgreeEntries'
                /\ anchor \in ClusterReplicated(entry.index, entry.term)'
                /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
                => CommitCertificate(recipient, entry, anchor)'
<1> SUFFICES ASSUME CandidateEntryBaseInv, LeaderCompletenessInductionInv,
                    NEW recipient \in Server, NEW sender \in Server, NEW anchor \in Server,
                    NEW request \in AppendRequests, NEW entry \in ClusterAgreeEntries,
                    AcceptedCertifiedRequest(recipient, sender, request), RequestCertificate(request, entry, anchor),
                    commitIndex[recipient] <= request.mcommitIndex,
                    entry \in ClusterAgreeEntries', anchor \in ClusterReplicated(entry.index, entry.term)',
                    SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
             PROVE CommitCertificate(recipient, entry, anchor)'
    BY SMT
<1>types. /\ log[anchor] \in Seq(LogEntry) /\ log'[anchor] \in Seq(LogEntry)
          /\ entry.index \in 0..Len(log[anchor]) /\ entry.index <= Len(log'[anchor])
          /\ request.mcommitIndex \in 0..entry.index
    BY CertifiedRequestTypes, HandleAppendEntriesRequestLogVarsTypeOK, LenProperties, SMT
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK,
        AcceptedCertifiedRequest, AppendRequests, ClusterReplicated, RequestCertificate
<1>anchorPrefix. SubSeq(log'[anchor], 1, request.mcommitIndex)
                    = SubSeq(log[anchor], 1, request.mcommitIndex)
    BY <1>types, EqualCertifiedPrefixesShorten, SMT
<1>prefix. /\ commitIndex'[recipient] = request.mcommitIndex
           /\ currentTerm'[recipient] = request.mterm
           /\ commitIndex'[recipient] <= Len(log'[recipient])
           /\ SubSeq(log'[recipient], 1, request.mcommitIndex)
                   = SubSeq(log[anchor], 1, request.mcommitIndex)
    BY AcceptedRequestCertifiedPrefix, CertifiedRequestTypes, SMT
    DEF CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK
<1> QED BY <1>anchorPrefix, <1>prefix DEF RequestCertificate, CommitCertificate


LEMMA AcceptedRequestRetainsCommitPrefix ==
    CommitCertificateBaseInv =>
        \A recipient, sender, anchor \in Server: \A request \in AppendRequests:
            \A entry \in ClusterAgreeEntries:
                /\ AcceptedCertifiedRequest(recipient, sender, request)
                /\ request.mdest = recipient
                /\ request.msource = sender
                /\ CommitCertificate(recipient, entry, anchor)
                /\ commitIndex[recipient] > 0
                => /\ commitIndex[recipient] <= Len(log'[recipient])
                   /\ SubSeq(log'[recipient], 1, commitIndex[recipient])
                          = SubSeq(log[recipient], 1, commitIndex[recipient])
<1> SUFFICES ASSUME CommitCertificateBaseInv,
                    NEW recipient \in Server, NEW sender \in Server, NEW anchor \in Server,
                    NEW request \in AppendRequests, NEW entry \in ClusterAgreeEntries,
                    AcceptedCertifiedRequest(recipient, sender, request),
                    request.mdest = recipient, request.msource = sender,
                    CommitCertificate(recipient, entry, anchor), commitIndex[recipient] > 0
             PROVE /\ commitIndex[recipient] <= Len(log'[recipient])
                   /\ SubSeq(log'[recipient], 1, commitIndex[recipient])
                          = SubSeq(log[recipient], 1, commitIndex[recipient])
    OBVIOUS
<1>types. /\ InductiveInvariant
          /\ log[recipient] \in Seq(LogEntry) /\ log[anchor] \in Seq(LogEntry)
          /\ log'[recipient] \in Seq(LogEntry)
          /\ request \in messages /\ request.mtype = AppendEntriesRequest
          /\ request.mprevLogIndex \in Nat /\ request.mdest = recipient
          /\ commitIndex[recipient] \in 1..Len(log[recipient])
          /\ commitIndex[recipient] \in 1..Len(log[anchor])
          /\ commitIndex[recipient] <= entry.index
    <2>base. InductiveInvariant
        BY DEF CommitCertificateBaseInv, CandidateEntryBaseInv
    <2>request. /\ request \in messages /\ request.mtype = AppendEntriesRequest
                /\ request.mprevLogIndex \in Nat
        BY <2>base, CertifiedRequestTypes
    <2>logs. /\ log[recipient] \in Seq(LogEntry) /\ log[anchor] \in Seq(LogEntry)
              /\ commitIndex[recipient] \in Nat
        BY <2>base DEF InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>post. log'[recipient] \in Seq(LogEntry)
        BY <2>base, AcceptedCertifiedRequestPostFacts
    <2>bound. /\ entry.index \in DOMAIN log[anchor]
               /\ commitIndex[recipient] <= entry.index
               /\ commitIndex[recipient] <= Len(log[recipient])
        BY DEF CommitCertificate, ClusterReplicated
    <2> QED BY <2>base, <2>request, <2>logs, <2>post, <2>bound, LenProperties, SMT
<1>shared. SharedLogPrefix(anchor, recipient, commitIndex[recipient])
    BY <1>types, LenProperties DEF SharedLogPrefix, CommitCertificate
<1>anchorCompatible. AppendRequestPrefixCompatible(request, log[anchor], commitIndex[recipient])
    <2>full. AppendRequestPrefixCompatible(request, log[anchor], entry.index)
        BY DEF CommitCertificateBaseInv, ClusterAgreeSupportInv, ClusterAgreeAppendInv,
            CommitCertificate, AcceptedCertifiedRequest
    <2>bound. commitIndex[recipient] <= entry.index BY <1>types
    <2>numbers. /\ request.mprevLogIndex \in Nat /\ commitIndex[recipient] \in Nat
                 /\ entry.index \in Nat
        BY <1>types, LenProperties DEF CommitCertificate, ClusterReplicated
    <2> QED BY <2>bound, <2>full, <2>numbers, SMT DEF AppendRequestPrefixCompatible
<1>compatible. AppendRequestPrefixCompatible(request, log[recipient], commitIndex[recipient])
    BY <1>types, <1>shared, <1>anchorCompatible, SharedPrefixTransfersRequestCompatibility
    DEF SharedLogPrefix
<1>retained. /\ commitIndex[recipient] \in DOMAIN log'[recipient]
             /\ SubSeq(log'[recipient], 1, commitIndex[recipient])
                    = SubSeq(log[recipient], 1, commitIndex[recipient])
    <2>domain. commitIndex[recipient] \in DOMAIN log[recipient]
        BY <1>types, LenProperties, SMT
    <2>request. /\ request \in messages /\ request.mtype = AppendEntriesRequest
                 /\ request.mdest = recipient
                 /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        BY <1>types DEF AcceptedCertifiedRequest
    <2>base. InductiveInvariant BY <1>types
    <2> QED BY <2>domain, <2>request, <2>base, <1>compatible,
        AppendRequestPreservesCompatiblePrefix
<1> QED BY <1>types, <1>retained, LenProperties, SMT

LEMMA CertifiedCommitPrefixRetained ==
    CommitCertificateBaseInv /\ [Next]_vars =>
        \A server, anchor \in Server: \A entry \in ClusterAgreeEntries:
            CommitCertificate(server, entry, anchor) /\ commitIndex[server] > 0
            => /\ commitIndex[server] <= Len(log'[server])
               /\ SubSeq(log'[server], 1, commitIndex[server])
                      = SubSeq(log[server], 1, commitIndex[server])
<1> SUFFICES ASSUME CommitCertificateBaseInv, [Next]_vars,
                    NEW server \in Server, NEW anchor \in Server,
                    NEW entry \in ClusterAgreeEntries,
                    CommitCertificate(server, entry, anchor), commitIndex[server] > 0
             PROVE /\ commitIndex[server] <= Len(log'[server])
                   /\ SubSeq(log'[server], 1, commitIndex[server])
                          = SubSeq(log[server], 1, commitIndex[server])
    OBVIOUS
<1>base. InductiveInvariant BY DEF CommitCertificateBaseInv, CandidateEntryBaseInv
<1>types. /\ log \in [Server -> Seq(LogEntry)] /\ commitIndex[server] \in Nat
          /\ commitIndex[server] <= Len(log[server])
    BY <1>base DEF InductiveInvariant, TypeOK, LogVarsTypeOK, CommitCertificate
<1>unchanged. CASE log'[server] = log[server]
    BY <1>unchanged, <1>types
<1>client. CASE \E actor \in Server, value \in Value: ClientRequest(actor, value)
    <2> PICK actor \in Server, value \in Value: ClientRequest(actor, value)
        BY <1>client
    <2>same. CASE actor = server
        <3>prefix. SubSeq(log'[server], 1, commitIndex[server])
                     = SubSeq(log[server], 1, commitIndex[server])
            BY <2>same, <1>base, <1>types, ClientRequestRetainsCommitPrefix
        <3>length. Len(log[server]) <= Len(log'[server])
            BY <2>same, <1>base, ClientRequestDoesNotShrinkLogs DEF InductiveInvariant
        <3>post. log'[server] \in Seq(LogEntry)
            BY <2>same, <1>base, ClientRequestDoesNotShrinkLogs
            DEF InductiveInvariant, LogVarsTypeOK
        <3> QED BY <3>prefix, <3>length, <3>post, <1>types, LenProperties, SMT
    <2>other. CASE actor # server
        BY <2>other, <1>types DEF ClientRequest
    <2> QED BY <2>same, <2>other
<1>append. CASE \E request \in messages:
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    <2> PICK request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        BY <1>append
    <2>fields. /\ request.mdest \in Server /\ request.msource \in Server
        BY <1>base, MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK
    <2>unchanged. CASE log'[server] = log[server]
        BY <2>unchanged, <1>types
    <2>changed. CASE log'[server] # log[server]
        <3>accepted. /\ request.mdest = server
                     /\ request \in AppendRequests
                     /\ AcceptedCertifiedRequest(server, request.msource, request)
            BY <2>changed, <2>fields, <1>types, SMT
            DEF HandleAppendEntriesRequest, AcceptedCertifiedRequest, AppendRequests
        <3> QED BY <3>accepted, <2>fields, AcceptedRequestRetainsCommitPrefix
    <2> QED BY <2>unchanged, <2>changed
<1> QED BY <1>unchanged, <1>client, <1>append, <1>base, LogChangingActionNext

LEMMA CommitCertificatePreserved ==
    CommitCertificateBaseInv /\ [Next]_vars =>
        \A server, anchor \in Server: \A entry \in ClusterAgreeEntries:
            /\ CommitCertificate(server, entry, anchor)
            /\ commitIndex'[server] = commitIndex[server]
            /\ commitIndex[server] > 0
            => CommitCertificate(server, entry, anchor)'
<1> SUFFICES ASSUME CommitCertificateBaseInv, [Next]_vars,
                    NEW server \in Server, NEW anchor \in Server,
                    NEW entry \in ClusterAgreeEntries,
                    CommitCertificate(server, entry, anchor),
                    commitIndex'[server] = commitIndex[server], commitIndex[server] > 0
             PROVE CommitCertificate(server, entry, anchor)'
    OBVIOUS
<1>prefix. /\ commitIndex'[server] <= Len(log'[server])
           /\ SubSeq(log'[server], 1, commitIndex[server])
                  = SubSeq(log[server], 1, commitIndex[server])
    BY CertifiedCommitPrefixRetained
<1>retained. /\ entry \in ClusterAgreeEntries'
             /\ anchor \in ClusterReplicated(entry.index, entry.term)'
    BY AgreedReplicaPrefixRetained DEF CommitCertificate
<1>short. SubSeq(log'[anchor], 1, commitIndex[server])
               = SubSeq(log[anchor], 1, commitIndex[server])
    BY AgreedReplicaShortPrefixRetained
    DEF CommitCertificate, CommitCertificateBaseInv, CandidateEntryBaseInv,
        InductiveInvariant, TypeOK, LogVarsTypeOK
<1>term. currentTerm[server] <= currentTerm'[server]
    BY CurrentTermsMonotonicNext
    DEF CommitCertificateBaseInv, CandidateEntryBaseInv
<1>currentType. currentTerm[server] \in Nat
    BY DEF CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, ServerVarsTypeOK
<1>nextCurrentType. currentTerm'[server] \in Nat
    BY TypeOKNext DEF CommitCertificateBaseInv, CandidateEntryBaseInv,
        InductiveInvariant, TypeOK, ServerVarsTypeOK
<1>anchorLogType. log[anchor] \in Seq(LogEntry)
    BY DEF CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant,
        TypeOK, LogVarsTypeOK
<1>entryType. entry.term \in Nat
    BY <1>anchorLogType, ElementOfSeq, LenProperties
    DEF CommitCertificate, ClusterReplicated, LogEntry
<1>oldBound. entry.term <= currentTerm[server]
    BY DEF CommitCertificate
<1>nextBound. entry.term <= currentTerm'[server]
    BY <1>currentType, <1>nextCurrentType, <1>entryType, <1>oldBound, <1>term, SMT
<1>commitBound. commitIndex'[server] <= entry.index
    BY DEF CommitCertificate
<1>oldPrefix. SubSeq(log[server], 1, commitIndex[server])
                 = SubSeq(log[anchor], 1, commitIndex[server])
    BY DEF CommitCertificate
<1>nextPrefix. SubSeq(log'[server], 1, commitIndex'[server])
                  = SubSeq(log'[anchor], 1, commitIndex'[server])
    BY <1>short, <1>oldPrefix, <1>prefix
<1> QED BY <1>retained, <1>nextBound, <1>commitBound, <1>nextPrefix, <1>prefix DEF CommitCertificate

LEMMA CommitCertificatesImpliesCommittedPrefixInv ==
    InductiveInvariant /\ CommittedCertificateInv => CommittedPrefixInv
<1> SUFFICES ASSUME InductiveInvariant, CommittedCertificateInv, NEW server \in Server
             PROVE AgreedPrefix(Committed(server))
    BY DEF CommittedPrefixInv
<1>empty. CASE commitIndex[server] = 0
    BY <1>empty, SubSeqEmpty DEF Committed, AgreedPrefix
<1>certificate. CASE commitIndex[server] # 0
    <2> PICK entry \in ClusterAgreeEntries: \E anchor \in Server: CommitCertificate(server, entry, anchor)
        BY <1>certificate DEF CommittedCertificateInv
    <2> PICK anchor \in Server: CommitCertificate(server, entry, anchor)
        BY SMT
    <2>types. /\ log[anchor] \in Seq(LogEntry)
              /\ entry.index \in 0..Len(log[anchor])
              /\ commitIndex[server] \in 0..entry.index
        BY LenProperties, SMT
        DEF InductiveInvariant, TypeOK, LogVarsTypeOK, CommitCertificate, ClusterReplicated
    <2>take. /\ SubSeq(log[anchor], 1, entry.index) \in Seq(LogEntry)
             /\ Len(SubSeq(log[anchor], 1, entry.index)) = entry.index
             /\ IsPrefix(SubSeq(log[anchor], 1, entry.index), log[anchor])
        BY <2>types, SequencePrefixTake
    <2>shorten. SubSeq(SubSeq(log[anchor], 1, entry.index), 1, commitIndex[server])
                   = SubSeq(log[anchor], 1, commitIndex[server])
        BY <2>types, <2>take, SequencePrefixShorten
    <2>prefix. IsPrefix(Committed(server), SubSeq(log[anchor], 1, entry.index))
        BY <2>types, <2>take, <2>shorten, SequencePrefixTake
        DEF Committed, CommitCertificate, IsPrefix
    <2> QED BY <2>prefix DEF AgreedPrefix, CommitCertificate
<1> QED BY <1>empty, <1>certificate

LEMMA AppendRequestsHaveCertificatesNext ==
    CommittedProofInv /\ [Next]_vars => RequestCertificateInv'
<1> SUFFICES ASSUME CommittedProofInv, [Next]_vars,
                    NEW request \in AppendRequests', request.mcommitIndex # 0
             PROVE \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                       RequestCertificate(request, entry, anchor)'
    BY DEF RequestCertificateInv
<1>old. CASE request \in AppendRequests
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in Server: RequestCertificate(request, entry, anchor)
        BY <1>old DEF CommittedProofInv, CommitCertificatesInv, RequestCertificateInv
    <2> PICK anchor \in Server: RequestCertificate(request, entry, anchor)
        OBVIOUS
    <2>premises. /\ CommitCertificateBaseInv
                 /\ anchor \in Server
                 /\ anchor \in ClusterReplicated(entry.index, entry.term)
        BY DEF CommittedProofInv, RequestCertificate
    <2>retained. RequestCertificate(request, entry, anchor)'
        BY <2>premises, <1>old, RequestCertificateRetained
    <2> QED BY <2>retained DEF RequestCertificate
<1>new. CASE request \notin AppendRequests
    <2> PICK sender \in Server:
            \E recipient \in Server:
                /\ AppendEntries(sender, recipient)
                /\ request = AppendEntriesMessage(sender, recipient)
        BY <1>new, NewAppendRequestOrigin
        DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv, AppendRequests
    <2> PICK recipient \in Server:
            /\ AppendEntries(sender, recipient)
            /\ request = AppendEntriesMessage(sender, recipient)
        OBVIOUS
    <2>types. /\ commitIndex[sender] \in Nat
              /\ AppendEntriesLastEntry(sender, recipient) \in Nat
        BY AppendEntriesLastEntryTypeOK
        DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv,
            InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>commitBound. request.mcommitIndex <= commitIndex[sender]
        BY <2>types DEF AppendEntriesMessage, Min
    <2>requestNat. request.mcommitIndex \in Nat \ {0}
        BY MinTypeOK, <2>types, SMT DEF AppendEntriesMessage
    <2>positive. commitIndex[sender] # 0
        BY <2>commitBound, <2>types, <2>requestNat, SMT
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in Server: CommitCertificate(sender, entry, anchor)
        BY <2>positive DEF CommittedProofInv, CommitCertificatesInv, CommittedCertificateInv
    <2> PICK anchor \in Server: CommitCertificate(sender, entry, anchor)
        OBVIOUS
    <2>certificate. RequestCertificate(request, entry, anchor)
        BY SendCommitCertificateRequest
        DEF CommittedProofInv, CommitCertificateBaseInv
    <2>stable. entry \in ClusterAgreeEntries'
        BY ClusterAgreeSupportInvSufficesForNext
        DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv, StableClusterAgreeEntriesInv
    <2>frame. log' = log
        BY DEF AppendEntries
    <2>nextCertificate. RequestCertificate(request, entry, anchor)'
        BY <2>certificate, <2>stable, <2>frame DEF RequestCertificate, ClusterReplicated
    <2> QED BY <2>stable, <2>nextCertificate
<1> QED BY <1>old, <1>new

LEMMA LeaderAdvanceCreatesCommitCertificate ==
    CommittedProofInv /\ [Next]_vars =>
        \A server \in Server:
            /\ AdvanceCommitIndex(server)
            /\ commitIndex'[server] # commitIndex[server]
            => \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                   CommitCertificate(server, entry, anchor)'
<1> SUFFICES ASSUME CommittedProofInv, [Next]_vars, NEW server \in Server,
                    AdvanceCommitIndex(server), commitIndex'[server] # commitIndex[server]
             PROVE \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                       CommitCertificate(server, entry, anchor)'
    OBVIOUS
<1>chosen. /\ AgreeIndexes(server) # {}
            /\ commitIndex'[server] = Max(AgreeIndexes(server))
            /\ Max(AgreeIndexes(server)) \in AgreeIndexes(server)
            /\ log[server][Max(AgreeIndexes(server))].term = currentTerm[server]
            /\ state[server] = Leader
    <2>typeOK. TypeOK
        BY DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant
    <2>shape. /\ state[server] = Leader
               /\ commitIndex'[server] = NewCommitIndex(server)
        BY <2>typeOK, SMT DEF AdvanceCommitIndex, TypeOK, LogVarsTypeOK
    <2>changed. /\ AgreeIndexes(server) # {}
                 /\ NewCommitIndex(server) = Max(AgreeIndexes(server))
                 /\ log[server][Max(AgreeIndexes(server))].term = currentTerm[server]
        BY <2>shape DEF NewCommitIndex
    <2>maximum. Max(AgreeIndexes(server)) \in AgreeIndexes(server)
        BY <2>changed, <2>typeOK, MaxAgreeIndexesTypeOK
    <2> QED BY <2>shape, <2>changed, <2>maximum
<1> DEFINE endpoint == Max(AgreeIndexes(server))
           entry == [index |-> endpoint, term |-> currentTerm[server]]
<1>agreed. entry \in ClusterAgreeEntries
    BY <1>chosen, LeaderAgreeIndexCertified
    DEF entry, endpoint, CommittedProofInv, CommitCertificateBaseInv
<1>stable. entry \in ClusterAgreeEntries'
    BY <1>agreed, ClusterAgreeSupportInvSufficesForNext
    DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv, StableClusterAgreeEntriesInv
<1>types. /\ log[server] \in Seq(LogEntry) /\ endpoint \in DOMAIN log[server]
          /\ currentTerm[server] \in Nat
    BY <1>chosen, LenProperties, SMT
    DEF endpoint, AgreeIndexes, CommittedProofInv, CommitCertificateBaseInv,
        CandidateEntryBaseInv, InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>frame. /\ log' = log /\ currentTerm' = currentTerm /\ matchIndex' = matchIndex
    BY DEF AdvanceCommitIndex
<1>agreeFrame. AgreeIndexes(server)' = AgreeIndexes(server)
    BY <1>frame DEF AgreeIndexes, Agree
<1>endpointFrame. endpoint' = endpoint
    BY <1>agreeFrame DEF endpoint
<1>entryFrame. entry' = entry
    BY <1>endpointFrame, <1>frame DEF entry
<1>certificate. CommitCertificate(server, entry, server)'
    <2>fields. /\ entry.index = endpoint /\ entry.term = currentTerm[server]
               /\ commitIndex'[server] = endpoint
               /\ log'[server][endpoint].term = entry.term
               /\ endpoint \in DOMAIN log'[server]
        BY <1>types, <1>chosen, <1>frame DEF entry, endpoint
    <2>endpointReplica. server \in ClusterReplicated(endpoint, currentTerm[server])'
        BY <2>fields, <1>endpointFrame, <1>frame DEF ClusterReplicated
    <2>replica. server \in ClusterReplicated(entry.index, entry.term)'
        BY <2>endpointReplica DEF entry
    <2>term. currentTerm'[server] = entry.term
        BY <1>frame DEF entry
    <2>bound. commitIndex'[server] = entry.index
        BY <2>fields
    <2>nextTermType. currentTerm'[server] \in Nat
        BY <1>types, <1>frame
    <2>indexType. entry.index \in Nat
        BY <1>types, LenProperties DEF entry
    <2>termBound. entry.term <= currentTerm'[server]
        BY <2>term, <2>nextTermType, SMT
    <2>commitBound. commitIndex'[server] <= entry.index
        BY <2>bound, <2>indexType, SMT
    <2>logBound. commitIndex'[server] <= Len(log'[server])
        BY <2>fields, <1>types, <1>frame, LenProperties, SMT
    <2>prefix. SubSeq(log'[server], 1, commitIndex'[server])
                  = SubSeq(log'[server], 1, commitIndex'[server])
        BY SMT
    <2> QED BY <1>stable, <1>entryFrame, <2>replica, <2>termBound,
        <2>commitBound, <2>logBound, <2>prefix DEF CommitCertificate
<1> QED BY <1>stable, <1>entryFrame, <1>certificate

LEMMA AcceptedRequestCreatesCommitCertificate ==
    CommittedProofInv /\ [Next]_vars =>
        \A server \in Server: \A request \in AppendRequests:
            /\ request.mdest = server
            /\ AcceptedCertifiedRequest(server, request.msource, request)
            /\ commitIndex'[server] # commitIndex[server]
            => \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                   CommitCertificate(server, entry, anchor)'
<1> SUFFICES ASSUME CommittedProofInv, [Next]_vars, NEW server \in Server,
                    NEW request \in AppendRequests, request.mdest = server,
                    AcceptedCertifiedRequest(server, request.msource, request),
                    commitIndex'[server] # commitIndex[server]
             PROVE \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                       CommitCertificate(server, entry, anchor)'
    OBVIOUS
<1>post. /\ commitIndex'[server] = request.mcommitIndex
         /\ commitIndex[server] < request.mcommitIndex
         /\ request.mcommitIndex > 0 /\ request.msource \in Server
    BY CertifiedRequestTypes, AcceptedCertifiedRequestPostFacts, SMT
    DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv,
        InductiveInvariant, TypeOK, LogVarsTypeOK
<1> PICK entry \in ClusterAgreeEntries:
        \E anchor \in Server: RequestCertificate(request, entry, anchor)
    BY <1>post DEF CommittedProofInv, CommitCertificatesInv, RequestCertificateInv
<1> PICK anchor \in Server: RequestCertificate(request, entry, anchor)
    OBVIOUS
<1>retained. /\ entry \in ClusterAgreeEntries'
             /\ anchor \in ClusterReplicated(entry.index, entry.term)'
             /\ SubSeq(log'[anchor], 1, entry.index) = SubSeq(log[anchor], 1, entry.index)
    BY AgreedReplicaPrefixRetained DEF CommittedProofInv, RequestCertificate
<1>certificate. CommitCertificate(server, entry, anchor)'
    BY <1>post, <1>retained, AcceptedRequestTransfersCommitCertificate, SMT
    DEF CommittedProofInv, CommitCertificateBaseInv
<1> QED BY <1>certificate, <1>retained

LEMMA CommittedCertificatesNext ==
    CommittedProofInv /\ [Next]_vars => CommittedCertificateInv'
<1> SUFFICES ASSUME CommittedProofInv, [Next]_vars,
                    NEW server \in Server, commitIndex'[server] # 0
             PROVE \E entry \in ClusterAgreeEntries': \E anchor \in Server:
                       CommitCertificate(server, entry, anchor)'
    BY DEF CommittedCertificateInv
<1>unchanged. CASE commitIndex'[server] = commitIndex[server]
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in Server: CommitCertificate(server, entry, anchor)
        BY <1>unchanged DEF CommittedProofInv, CommitCertificatesInv, CommittedCertificateInv
    <2> PICK anchor \in Server: CommitCertificate(server, entry, anchor)
        OBVIOUS
    <2>positive. commitIndex[server] > 0
        BY <1>unchanged, SMT
        DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv,
            InductiveInvariant, TypeOK, LogVarsTypeOK
    <2>certificate. CommitCertificate(server, entry, anchor)'
        BY <1>unchanged, <2>positive, CommitCertificatePreserved DEF CommittedProofInv
    <2> QED BY <2>certificate DEF CommitCertificate
<1>changed. CASE commitIndex'[server] # commitIndex[server]
    <2>shape. \/ AdvanceCommitIndex(server)
              \/ \E request \in AppendRequests:
                     /\ request.mdest = server
                     /\ AcceptedCertifiedRequest(server, request.msource, request)
        <3>typeok. TypeOK
            BY DEF CommittedProofInv, CommitCertificateBaseInv, CandidateEntryBaseInv, InductiveInvariant
        <3>nonreceive. CASE ~(\E request \in messages: Receive(request))
            BY <3>nonreceive, <1>changed, <3>typeok, SMT
            DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest, AdvanceCommitIndex,
                AppendEntries, LeaderStepDown, TypeOK, LogVarsTypeOK
        <3>receive. CASE \E request \in messages: Receive(request)
            <4> PICK request \in messages: Receive(request) BY <3>receive
            <4>fields. /\ request.mdest \in Server /\ request.msource \in Server
                /\ (request.mtype = AppendEntriesRequest => request.mterm \in Nat)
                BY <3>typeok, MessageFieldsTypeOK DEF TypeOK, MsgTypeOK
            <4>handler. /\ request.mtype = AppendEntriesRequest
                        /\ request.mdest = server
                        /\ HandleAppendEntriesRequest(server, request.msource, request)
                BY <1>changed, <3>typeok, <4>fields, SMT
                DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                    HandleRequestVoteResponse, HandleAppendEntriesResponse,
                    HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
            <4>accepted. AcceptedCertifiedRequest(server, request.msource, request)
                BY <4>handler, <1>changed, <3>typeok, <4>fields, SMT
                DEF AcceptedCertifiedRequest, HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
            <4> QED BY <4>handler, <4>accepted DEF AppendRequests
        <3> QED BY <3>nonreceive, <3>receive
    <2> QED BY <1>changed, <2>shape, LeaderAdvanceCreatesCommitCertificate,
        AcceptedRequestCreatesCommitCertificate
<1> QED BY <1>unchanged, <1>changed

LEMMA CommitCertificatesNext ==
    CommittedProofInv /\ [Next]_vars => CommitCertificatesInv'
    BY CommittedCertificatesNext, AppendRequestsHaveCertificatesNext DEF CommitCertificatesInv

LEMMA CommitCertificatesImpliesLeaderCompletenessInv ==
    InductiveInvariant /\ LogMatchingInv /\ LeaderClusterAgreeInv
    /\ CommittedCertificateInv => LeaderCompletenessInv
<1> SUFFICES ASSUME InductiveInvariant, LogMatchingInv, LeaderClusterAgreeInv,
                    CommittedCertificateInv, NEW server \in Server,
                    NEW leader \in CurrentLeaders,
                    currentTerm[server] <= currentTerm[leader]
             PROVE IsPrefix(Committed(server), log[leader])
    BY DEF LeaderCompletenessInv
<1>types. /\ leader \in Server /\ state[leader] = Leader
          /\ log[leader] \in Seq(LogEntry) /\ log[server] \in Seq(LogEntry)
          /\ commitIndex[server] \in Nat
          /\ commitIndex[server] <= Len(log[server])
          /\ currentTerm[server] \in Nat /\ currentTerm[leader] \in Nat
    BY CommitCertificatesImpliesCommitIndexBound
    DEF CurrentLeaders, InductiveInvariant, TypeOK, LogVarsTypeOK,
        ServerVarsTypeOK, CommitIndexBound
<1>empty. CASE commitIndex[server] = 0
    BY <1>empty, <1>types, SequencePrefixEmpty, SubSeqEmpty DEF Committed
<1>certificate. CASE commitIndex[server] # 0
    <2> PICK entry \in ClusterAgreeEntries:
            \E anchor \in Server: CommitCertificate(server, entry, anchor)
        BY <1>certificate DEF CommittedCertificateInv
    <2> PICK anchor \in Server: CommitCertificate(server, entry, anchor)
        BY SMT
    <2>bounds. /\ entry.term <= currentTerm[leader]
               /\ anchor \in ClusterReplicated(entry.index, entry.term)
               /\ log[anchor] \in Seq(LogEntry)
               /\ commitIndex[server] \in 0..entry.index
               /\ entry.index \in 0..Len(log[anchor])
        <3>certificate. /\ entry.term <= currentTerm[server]
                         /\ anchor \in ClusterReplicated(entry.index, entry.term)
                         /\ commitIndex[server] <= entry.index
            BY DEF CommitCertificate
        <3>replica. /\ anchor \in Server
                    /\ entry.index \in DOMAIN log[anchor]
                    /\ log[anchor][entry.index].term = entry.term
            BY <3>certificate DEF ClusterReplicated
        <3>logType. log[anchor] \in Seq(LogEntry)
            BY <3>replica DEF InductiveInvariant, TypeOK, LogVarsTypeOK
        <3>entryTypes. /\ entry.index \in Nat /\ entry.term \in Nat
                       /\ entry.index <= Len(log[anchor])
            BY <3>replica, <3>logType, LenProperties, ElementOfSeq, SMT DEF LogEntry
        <3> QED BY <3>certificate, <3>logType, <3>entryTypes, <1>types, SMT
    <2>shared. SharedLogPrefix(leader, anchor, entry.index)
        BY <2>bounds, <1>types, LeaderClusterAgreeGivesSharedPrefix
    <2>take. /\ SubSeq(log[anchor], 1, entry.index) \in Seq(LogEntry)
             /\ Len(SubSeq(log[anchor], 1, entry.index)) = entry.index
             /\ IsPrefix(SubSeq(log[anchor], 1, entry.index), log[anchor])
        BY <2>bounds, SequencePrefixTake
    <2>shorten. SubSeq(SubSeq(log[anchor], 1, entry.index), 1, commitIndex[server])
                   = SubSeq(log[anchor], 1, commitIndex[server])
        BY <2>bounds, <2>take, SequencePrefixShorten
    <2>prefix. IsPrefix(Committed(server), SubSeq(log[anchor], 1, entry.index))
        BY <2>bounds, <2>take, <2>shorten, SequencePrefixTake
        DEF Committed, CommitCertificate, IsPrefix
    <2>leaderPrefix. IsPrefix(SubSeq(log[anchor], 1, entry.index), log[leader])
        BY <2>shared, <2>take, <1>types, LenProperties
        DEF SharedLogPrefix, IsPrefix
    <2>committedType. Committed(server) \in Seq(LogEntry)
        BY CommitCertificatesImpliesCommitIndexBound, CommittedPrefixesTypeOK
    <2> QED BY <2>prefix, <2>leaderPrefix, <2>committedType,
        <2>take, <1>types, SequencePrefixTransitive
<1> QED BY <1>empty, <1>certificate

------------------------------------------------------------------------

THEOREM LeaderAgreementBridgeInvariant == Spec => []LeaderAgreementBridgeInv
<1>base. Spec => []CandidateEntryBaseInv /\ []LeaderCompletenessInductionInv
    BY CandidateEntryBaseInvariant, LeaderCompletenessInductionInvariant
<1>replica. Spec => []CurrentTermReplicaEvidenceInv
    BY CurrentTermReplicaEvidenceInit, CurrentTermReplicaEvidenceNext, <1>base, PTL
    DEF CandidateEntryBaseInv, Spec
<1>match. Spec => []LeaderMatchResponseInv
    BY LeaderMatchResponseInit, LeaderMatchResponseNext, <1>base, PTL
    DEF CandidateEntryBaseInv, Spec
<1>lower. Spec => []SuccessfulResponseLowerEvidenceInv
    BY SuccessfulResponseLowerEvidenceInit, SuccessfulResponseLowerEvidenceNext,
        <1>base, <1>replica, PTL DEF Spec
<1> QED BY <1>replica, <1>match, <1>lower, PTL DEF LeaderAgreementBridgeInv

THEOREM CommitCertificatesInvariant == Spec => []CommitCertificatesInv
<1>independent. Spec => /\ []CommitCertificateBaseInv /\ []LeaderAgreementBridgeInv
    BY CandidateEntryBaseInvariant, LeaderCompletenessInductionInvariant,
        ClusterAgreeSupportInvariant, LeaderAgreementBridgeInvariant, PTL
    DEF CommitCertificateBaseInv
<1>init. Init => CommitCertificatesInv BY CommitCertificatesInit
<1>next. CommitCertificateBaseInv /\ LeaderAgreementBridgeInv
         /\ CommitCertificatesInv /\ [Next]_vars => CommitCertificatesInv'
    BY CommitCertificatesNext DEF CommittedProofInv
<1> QED BY <1>independent, <1>init, <1>next, PTL DEF Spec

THEOREM CommitIndexBoundInvariant == Spec => []CommitIndexBound
    BY CommitCertificatesInvariant, InductiveInvariantInvariant,
        CommitCertificatesImpliesCommitIndexBound, PTL DEF CommitCertificatesInv

THEOREM CommitPhaseInvariant == Spec => []CommitPhaseInv
<1>init. Init => CommitPhaseInv
    BY CommitPhaseInvInit
<1>next. InductiveInvariant /\ CommitIndexBound /\ CommitPhaseInv /\ [Next]_vars => CommitPhaseInv'
    BY CommitPhaseInvNext
<1> QED BY <1>init, <1>next, InductiveInvariantInvariant, CommitIndexBoundInvariant, PTL DEF Spec


THEOREM LeaderCommitPhaseInvariant == Spec => []LeaderCommitPhaseInv
    BY CommitPhaseInvariant, PTL DEF CommitPhaseInv

THEOREM CommitIndexMonotonicInvariant == Spec => [][CommitIndexMonotonicInv]_vars
    BY TypeOKInvariant, LeaderCommitPhaseInvariant, CommitIndexMonotonicNext, PTL DEF Spec

THEOREM MonotonicCommitIndexInvariant == Spec => [][MonotonicCommitIndexInv]_vars
    BY TypeOKInvariant, LeaderCommitPhaseInvariant, MonotonicCommitIndexNext, PTL DEF Spec

THEOREM CommittedPrefixInvariant == Spec => []CommittedPrefixInv
    BY CommitCertificatesInvariant, InductiveInvariantInvariant,
        CommitCertificatesImpliesCommittedPrefixInv, PTL DEF CommitCertificatesInv

THEOREM QuorumLogInvariant == Spec => []QuorumLogInv
    BY CommittedPrefixInvariant, InductiveInvariantInvariant, ClusterLogMatchingInvariant,
        CommitIndexBoundInvariant, CommittedPrefixImpliesQuorumLogInv, PTL

THEOREM CommittedLogInvariant == Spec => []LogInv
    BY CommittedPrefixInvariant, InductiveInvariantInvariant, ClusterLogMatchingInvariant,
        CommitIndexBoundInvariant, CommittedPrefixImpliesLogInv, PTL

THEOREM LeaderCompletenessInvariant == Spec => []LeaderCompletenessInv
    BY CommitCertificatesInvariant, InductiveInvariantInvariant, ClusterLogMatchingInvariant,
        ClusterAgreeSupportInvariant, CommitCertificatesImpliesLeaderCompletenessInv, PTL
    DEF CommitCertificatesInv, ClusterAgreeSupportInv

====================================================================
