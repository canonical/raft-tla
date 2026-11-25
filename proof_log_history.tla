------------------------------ MODULE proof_log_history ------------------------------
\* proof_log_history.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_election_history

\* Edge transport requires type and replication bounds, not election safety.
EntryEdgeBase == TypeOK /\ NextIndexBound

AppendRequests == {m \in messages: m.mtype = AppendEntriesRequest}

LogEntryEdge(entries, index) ==
    [index |-> index, term |-> entries[index].term,
     previous |-> IF index = 1 THEN 0 ELSE entries[index - 1].term,
     entry |-> entries[index]]

RequestEntryEdge(request, offset) ==
    [index |-> request.mprevLogIndex + offset,
     term |-> request.mentries[offset].term,
     previous |-> IF offset = 1 THEN request.mprevLogTerm
                  ELSE request.mentries[offset - 1].term,
     entry |-> request.mentries[offset]]

HistoricalEntryEdges ==
    (UNION { {LogEntryEdge(log[server], index): index \in DOMAIN log[server]}:
              server \in Server })
    \cup (UNION { {RequestEntryEdge(request, offset): offset \in DOMAIN request.mentries}:
                  request \in AppendRequests })

EntryEdgeConsistency ==
    \A left, right \in HistoricalEntryEdges:
        left.index = right.index /\ left.term = right.term
        => /\ left.entry = right.entry /\ left.previous = right.previous

AppendRequestRootTerm ==
    \A m \in AppendRequests: m.mprevLogIndex = 0 => m.mprevLogTerm = 0
\* An entry's creator cannot regain active status in its old term after losing
\* that campaign. While still active in that term, its original prefixes stay.
OwnerPrefix(owner, term, prefix) ==
    /\ term <= currentTerm[owner]
    /\ /\ currentTerm[owner] = term
          /\ state[owner] \in {Candidate, Leader}
       => IsPrefix(prefix, log[owner])
\* Witnesses are quantified in the state predicate, not additional state.
\* A witness retains the complete prefix at an entry's local append, together
\* with the campaign snapshot and certificate captured by that append.
WitnessPrefixData(witness) ==
    /\ witness.prefix \in Seq(LogEntry)
    /\ witness.edge.index = Len(witness.prefix)
    /\ witness.edge.index \in Nat \ {0}
    /\ witness.edge.term \in Nat
    /\ witness.edge = LogEntryEdge(witness.prefix, witness.edge.index)
    /\ TermsOrdered(witness.prefix)
    /\ EntryStructure(witness.prefix, witness.edge.term)
    /\ witness.owner \in Server
    /\ witness.snapshot \in Seq(LogEntry)
    /\ witness.snapshot = CampaignPrefix(witness.prefix, witness.edge.term)
    /\ IsPrefix(witness.snapshot, witness.prefix)
    /\ Len(witness.snapshot) < witness.edge.index

CertificateWitness(voteHistory, witness) ==
    /\ WitnessPrefixData(witness)
    /\ OwnerPrefix(witness.owner, witness.edge.term, witness.prefix)
    /\ RetainedElectionCertificate(voteHistory, witness.owner, witness.edge.term,
                                    witness.snapshot, witness.occurrence,
                                    witness.support)


CertificateFamily(voteHistory, family) ==
    /\ CampaignHistory(voteHistory)
    /\ IsFiniteSet(family)
    /\ \A witness \in family: CertificateWitness(voteHistory, witness)
    /\ \A witness \in family: \A index \in DOMAIN witness.prefix:
           \E ancestor \in family:
               ancestor.edge = LogEntryEdge(witness.prefix, index)

CoversEntryEdges(family, edges) ==
    \A edge \in edges: \E witness \in family: witness.edge = edge

\* Coverage asks only for surviving edges and their witness ancestry. It does
\* not require witnesses for every old campaign. Distinct witnesses with equal
\* (index, term) keys are not yet asserted to have consistent prefixes.
EntryAncestryInv(voteHistory) ==
    \E family:
        /\ CertificateFamily(voteHistory, family)
        /\ CoversEntryEdges(family, HistoricalEntryEdges)

MembershipEntryAncestryInv(voteHistory) ==
    /\ MembershipCampaignsInv(voteHistory)
    /\ AppendRequestRootTerm
    /\ EntryAncestryInv(voteHistory)


SuccessfulAppendResponse(response) ==
    response.mtype = AppendEntriesResponse /\ response.msuccess

ResponseMatchesRequest(response, request) ==
    /\ request.mtype = AppendEntriesRequest
    /\ request.msource = response.mdest
    /\ request.mdest = response.msource
    /\ request.mterm = response.mterm
    /\ request.mprevLogIndex + Len(request.mentries) = response.mmatchIndex

AppendAnchorMatches(request, peer) ==
    \/ request.mprevLogIndex = 0
    \/ /\ request.mprevLogIndex > 0
       /\ request.mprevLogIndex <= Len(log[peer])
       /\ request.mprevLogTerm = log[peer][request.mprevLogIndex].term

SuccessfulResponseOriginInv ==
    \A response \in messages:
        SuccessfulAppendResponse(response) =>
            \E request \in messages: ResponseMatchesRequest(response, request)

MatchIndexEvidenceInv ==
    \A leader, peer \in Server:
        state[leader] = Leader /\ matchIndex[leader][peer] > 0 =>
            \E response \in messages:
                /\ SuccessfulAppendResponse(response)
                /\ response.msource = peer
                /\ response.mdest = leader
                /\ response.mterm = currentTerm[leader]
                /\ response.mmatchIndex = matchIndex[leader][peer]

AppendRequestElectionEvidenceInv(voteHistory) ==
    \A request \in AppendRequests:
        \E snapshot \in Seq(LogEntry): \E occurrence, support:
            RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                                        snapshot, occurrence, support)

ReplicationEvidenceInv(voteHistory) ==
    /\ MembershipEntryAncestryInv(voteHistory)
    /\ SuccessfulResponseOriginInv
    /\ MatchIndexEvidenceInv
    /\ AppendRequestElectionEvidenceInv(voteHistory)
\* Availability is already invariant. This is the additional consistency
\* obligation for its witnessing family; it is not asserted invariant here.
WitnessEdgeConsistency(family) ==
    \A left, right \in family:
        /\ left.edge.index = right.edge.index
        /\ left.edge.term = right.edge.term
        => /\ left.edge.entry = right.edge.entry
           /\ left.edge.previous = right.edge.previous
\* Empty requests can acknowledge a nonempty prefix. Capture their complete
\* sender prefix too, rather than treating the absence of a payload as index 0.
RequestPrefixData(request, prefix) ==
    /\ prefix \in Seq(LogEntry)
    /\ Len(prefix) = request.mprevLogIndex + Len(request.mentries)
    /\ request.mprevLogIndex \in 0..Len(prefix)
    /\ (request.mprevLogIndex = 0 => request.mprevLogTerm = 0)
    /\ (request.mprevLogIndex > 0 =>
           prefix[request.mprevLogIndex].term = request.mprevLogTerm)
    /\ \A offset \in DOMAIN request.mentries:
           prefix[request.mprevLogIndex + offset] = request.mentries[offset]
    /\ TermsOrdered(prefix)
    /\ EntryStructure(prefix, request.mterm)

RequestPrefixEvidence(request) ==
    /\ request.msource \in Server
    /\ request.mterm \in Nat
    /\ \E prefix \in Seq(LogEntry):
           /\ RequestPrefixData(request, prefix)
           /\ OwnerPrefix(request.msource, request.mterm, prefix)

RequestPrefixEvidenceInv ==
    \A request \in AppendRequests: RequestPrefixEvidence(request)

ReplicationPrefixInv(voteHistory) == ReplicationEvidenceInv(voteHistory) /\ RequestPrefixEvidenceInv
RecordedAcknowledgment(peer, leader, term, index) ==
    \E response \in messages:
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = peer
        /\ response.mdest = leader
        /\ response.mterm = term
        /\ response.mmatchIndex >= index

\* The leader's own slot counts only when a caller-configured quorum includes
\* it. These sets keep original RPC evidence after its sender advances term.
RecordedReplicationSupport(leader, term, index) ==
    {peer \in Server: peer = leader \/ RecordedAcknowledgment(peer, leader, term, index)}

\* This connects the local commit guard to actual retained responses. Full
\* compatible-prefix agreement still needs the joint consistency invariant.
ReplicationQuorumEvidence(leader, index, support) ==
    /\ leader \in Server
    /\ state[leader] = Leader
    /\ index \in DOMAIN log[leader]
    /\ log[leader][index].term = currentTerm[leader]
    /\ support \in Quorums(LastConfiguration(leader))
    /\ support \subseteq RecordedReplicationSupport(leader, currentTerm[leader], index)
SnapshotFreshFor(snapshot, voter) ==
    \/ LastTerm(snapshot) > LastTerm(log[voter])
    \/ /\ LastTerm(snapshot) = LastTerm(log[voter])
       /\ Len(snapshot) >= Len(log[voter])

VoteRequestFreshFor(request, voter) ==
    \/ request.mlastLogTerm > LastTerm(log[voter])
    \/ /\ request.mlastLogTerm = LastTerm(log[voter])
       /\ request.mlastLogIndex >= Len(log[voter])

VoteRequestEligible(request, voter) ==
    /\ request.mtype = RequestVoteRequest
    /\ VoteRequestFreshFor(request, voter)
    /\ \/ currentTerm[voter] < request.mterm
       \/ /\ currentTerm[voter] = request.mterm
          /\ votedFor[voter] \in {Nil, request.msource}

RecordedCampaignVote(voteHistory, voter, candidate, term) ==
    \/ Grant(voter, candidate, term)
    \/ voter = candidate /\ Started(voteHistory, candidate, term)

NewPeerVoteEligible(voter, candidate, term, snapshot) ==
    /\ voter # candidate
    /\ SnapshotFreshFor(snapshot, voter)
    /\ \/ currentTerm[voter] < term
       \/ /\ currentTerm[voter] = term
          /\ votedFor[voter] \in {Nil, candidate}
RecordedPrefixAcknowledgment(peer, leader, term, target) ==
    \E response, request \in messages: \E prefix \in Seq(LogEntry):
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = peer /\ response.mdest = leader
        /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        /\ ResponseMatchesRequest(response, request)
        /\ RequestPrefixData(request, prefix)
        /\ OwnerPrefix(leader, term, prefix)
        /\ IsPrefix(target, prefix)
CommitTarget(certificate) == SubSeq(certificate.entries, 1, certificate.index)

HistoryCommitCertificate(history, certificate) ==
    /\ certificate.leader \in Server /\ certificate.term \in Nat
    /\ certificate.entries \in Seq(LogEntry)
    /\ certificate.index \in 1..Len(certificate.entries)
    /\ certificate.entries[certificate.index].term = certificate.term
    /\ TermsOrdered(certificate.entries) /\ EntryStructure(certificate.entries, certificate.term)
    /\ OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    /\ certificate.snapshot \in Seq(LogEntry)
    /\ IsPrefix(certificate.snapshot, certificate.entries) /\ Len(certificate.snapshot) < certificate.index
    /\ HistoryElectionCertificate(history, certificate.leader, certificate.term,
                                   certificate.snapshot, certificate.electionOccurrence, certificate.election)
    /\ certificate.configuration = LatestConfigurationOccurrence(certificate.entries)
    /\ certificate.configuration.members \subseteq Server /\ certificate.configuration.members # {}
    /\ certificate.replication \in Quorums(certificate.configuration.members)
    /\ (certificate.replication \subseteq {certificate.leader} =>
           LocalAppendOrigin(history, certificate.leader, certificate.term, CommitTarget(certificate)))
    /\ \A peer \in certificate.replication \ {certificate.leader}:
           RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))

\* Retain the original quorum RPC evidence. The full sender log identifies the
\* configuration used by that quorum; only CommitTarget is claimed committed.
\* Protection by later leaders is a separate conjunct of the joint argument.
RetainedCommitCertificate(voteHistory, certificate) ==
    /\ certificate.leader \in Server
    /\ certificate.term \in Nat
    /\ certificate.entries \in Seq(LogEntry)
    /\ certificate.index \in 1..Len(certificate.entries)
    /\ certificate.entries[certificate.index].term = certificate.term
    /\ TermsOrdered(certificate.entries)
    /\ EntryStructure(certificate.entries, certificate.term)
    /\ OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    /\ certificate.snapshot \in Seq(LogEntry)
    /\ IsPrefix(certificate.snapshot, certificate.entries)
    /\ Len(certificate.snapshot) < certificate.index
    /\ RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
                                    certificate.snapshot, certificate.electionOccurrence,
                                    certificate.election)
    /\ certificate.configuration = LatestConfigurationOccurrence(certificate.entries)
    /\ certificate.configuration.members \subseteq Server
    /\ certificate.configuration.members # {}
    /\ certificate.replication \in Quorums(certificate.configuration.members)
    /\ (certificate.replication \subseteq {certificate.leader} =>
           LocalAppendOrigin(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate)))
    /\ \A peer \in certificate.replication \ {certificate.leader}:
           RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term,
                                        CommitTarget(certificate))
HistoryCommitCertificateRetention ==
    \A voteHistory, certificate:
        CampaignHistory(voteHistory) /\ HistoryCommitCertificate(voteHistory, certificate)
        => RetainedCommitCertificate(voteHistory, certificate)
CommitCertificateRecordedSupport ==
    \A voteHistory, certificate:
        RetainedCommitCertificate(voteHistory, certificate) =>
            certificate.replication \subseteq
                RecordedReplicationSupport(certificate.leader, certificate.term, certificate.index)
CommitCertificateFamily(voteHistory, family) ==
    /\ CampaignHistory(voteHistory)
    /\ IsFiniteSet(family)
    /\ \A certificate \in family: RetainedCommitCertificate(voteHistory, certificate)

LocalCommitEvidence(family) ==
    \A server \in Server:
        commitIndex[server] > 0 => \E certificate \in family:
            /\ commitIndex[server] <= certificate.index
            /\ certificate.term <= currentTerm[server]

AdvertisedCommitEvidence(family) ==
    \A request \in AppendRequests:
        request.mcommitIndex > 0 => \E certificate \in family:
            /\ request.mcommitIndex <= certificate.index
            /\ certificate.term <= request.mterm
\* These are pre-state premises of the unfinished joint induction, rather
\* than consequences of scalar commit evidence. No temporal claim is made here.
CommitLeaderProtection(family) ==
    \A certificate \in family: \A leader \in Server:
        state[leader] = Leader /\ certificate.term <= currentTerm[leader]
        => IsPrefix(CommitTarget(certificate), log[leader])

CommitElectionIntersections(voteHistory, family) ==
    \A certificate \in family: \A leader \in Server:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
        /\ certificate.term = currentTerm[leader]
        => certificate.election \cap support # {}

CurrentBarrierCertificate(voteHistory, leader, certificate) ==
    /\ RetainedCommitCertificate(voteHistory, certificate)
    /\ certificate.leader = leader
    /\ certificate.term = currentTerm[leader]
    /\ commitIndex[leader] \in 1..certificate.index
    /\ IsPrefix(certificate.entries, log[leader])
    /\ certificate.configuration = LatestConfigurationOccurrence(log[leader])
    /\ certificate.configuration.index <= certificate.index
    /\ IsPrefix(certificate.configuration.prefix, CommitTarget(certificate))
    /\ IsPrefix(Committed(leader), CommitTarget(certificate))

CoveredPrefix(family, prefix) ==
    \A index \in DOMAIN prefix: \E witness \in family:
        witness.edge = LogEntryEdge(prefix, index)

\* Freeze the campaign boundary and the snapshot's relation to the sent
\* prefix. This still anchors the election configuration after the sender
\* becomes inactive, including requests shorter than the campaign snapshot.
RequestCampaignBoundary(voteHistory, request, prefix) ==
    /\ request.msource \in Server /\ request.mterm \in Nat
    /\ \E snapshot \in Seq(LogEntry): \E occurrence, support:
           /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                                           snapshot, occurrence, support)
           /\ (IsPrefix(snapshot, prefix) \/ IsPrefix(prefix, snapshot))
           /\ \A index \in DOMAIN prefix:
                  prefix[index].term < request.mterm => index <= Len(snapshot)

AncestralRequestPrefix(voteHistory, family, request) ==
    /\ request.msource \in Server
    /\ request.mterm \in Nat
    /\ Len(request.mentries) <= 1
    /\ \E prefix \in Seq(LogEntry):
           /\ RequestPrefixData(request, prefix)
           /\ OwnerPrefix(request.msource, request.mterm, prefix)
           /\ CoveredPrefix(family, prefix)
           /\ RequestCampaignBoundary(voteHistory, request, prefix)

RequestPrefixAncestry(voteHistory, family) ==
    \A request \in AppendRequests: AncestralRequestPrefix(voteHistory, family, request)

RequestRespectsPrefix(request, target) ==
    \A offset \in DOMAIN request.mentries:
        request.mprevLogIndex + offset \in DOMAIN target
        => request.mentries[offset] = target[request.mprevLogIndex + offset]

\* Admission of this property for a newly agreed target is still part of
\* the joint exclusion argument. Once admitted, it protects existing holders.
ProtectedAppendRequests(target, term) ==
    \A request \in AppendRequests:
        request.mterm >= term => RequestRespectsPrefix(request, target)

ProtectedPeer(target, term, peer) ==
    /\ currentTerm[peer] >= term
    /\ IsPrefix(target, log[peer])

ProtectedLeaders(target, term) ==
    \A leader \in Server:
        state[leader] = Leader /\ currentTerm[leader] >= term
        => IsPrefix(target, log[leader])

\* Equal-term entries must share their creator's ordered append history, even
\* when their indexes differ. Equal-key consistency alone does not state this.
TermPrefixOrder(family) ==
    \A left, right \in family:
        left.edge.term = right.edge.term /\ left.edge.index <= right.edge.index
        => IsPrefix(left.prefix, right.prefix)

\* A historical boundary for a selected agreement target. Its admission is
\* still a joint obligation; a newer last term alone does not imply containment.
LaterTermPrefixProtection(family, target, term) ==
    \A witness \in family:
        witness.edge.term > term => IsPrefix(target, witness.prefix)

LEMMA NewAppendRequestOrigin ==
    EntryEdgeBase /\ [Next]_vars =>
        \A m \in messages' \ messages:
            m.mtype = AppendEntriesRequest =>
                \E i, j \in Server:
                    /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
<1> SUFFICES ASSUME EntryEdgeBase, [Next]_vars,
                    NEW m \in messages' \ messages,
                    m.mtype = AppendEntriesRequest
             PROVE \E i, j \in Server:
                 /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
    BY SMT
<1>1. CASE \E i, j \in Server: AppendEntries(i, j)
    BY SMT, <1>1 DEF AppendEntries, Send, WithMessage, WithMessages
<1>2. CASE \E i \in Server: Timeout(i)
    BY SMT, <1>2, MessageTypesDistinct DEF Timeout, RequestVoteRequests, WithMessages
<1>3. CASE \E request \in messages: Receive(request)
    BY SMT, <1>3, MessageTypesDistinct
       DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
           HandleRequestVoteResponse, HandleAppendEntriesRequest,
           HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY SMT, <1>1, <1>2, <1>3
    DEF Next, vars, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, LeaderStepDown

LEMMA EqualLogPrefixesEntryEqual ==
    \A left, right \in Seq(LogEntry), endpoint, index \in Nat:
        /\ endpoint <= Len(left) /\ endpoint <= Len(right)
        /\ index \in 1..endpoint
        /\ SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
        => left[index] = right[index]
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    NEW endpoint \in Nat, NEW index \in Nat,
                    endpoint <= Len(left), endpoint <= Len(right),
                    index \in 1..endpoint,
                    SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
             PROVE left[index] = right[index]
    BY SMT
<1>1. Len(left) \in Nat /\ Len(right) \in Nat
    BY SMT, LenProperties
<1>2. SubSeq(left, 1, endpoint)[index] = left[index]
    BY SMT, <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>3. SubSeq(right, 1, endpoint)[index] = right[index]
    BY SMT, <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1> QED BY SMT, <1>2, <1>3

LEMMA TruncateAppendRetainsPrefix ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, cut \in Nat:
        \A endpoint \in 1..cut:
            cut <= Len(entries)
            => /\ Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
               /\ SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
                    = SubSeq(entries, 1, endpoint)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW cut \in Nat, NEW endpoint \in 1..cut, cut <= Len(entries)
             PROVE /\ Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
                   /\ SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
                        = SubSeq(entries, 1, endpoint)
    BY SMT
<1>1. Len(entries) \in Nat /\ cut \in 1..Len(entries)
    BY SMT, LenProperties
<1>2. SubSeq(entries, 1, cut) \in Seq(LogEntry) /\ Len(SubSeq(entries, 1, cut)) = cut
    BY SMT, <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>3. SubSeq(entries, 1, cut)[endpoint] = entries[endpoint]
    BY SMT, <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>4. Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
    BY SMT, <1>2, <1>3, AppendProperties
<1>5. SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
         = SubSeq(SubSeq(entries, 1, cut), 1, endpoint)
    BY SMT, <1>2, AppendPreservesSequencePrefix
<1>6. SubSeq(SubSeq(entries, 1, cut), 1, endpoint) = SubSeq(entries, 1, endpoint)
    BY SMT, <1>1, <1>2, SubSeqOfSubSeq
<1> QED BY SMT, <1>4, <1>5, <1>6

LEMMA AppendRequestRetainsMatchedPrefix ==
    \A recipient, sender \in Server, m \in messages:
        \A endpoint \in 1..m.mprevLogIndex:
            /\ EntryEdgeBase /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(recipient, sender, m)
            /\ m.mprevLogIndex <= Len(log[recipient])
            => /\ log'[recipient][endpoint] = log[recipient][endpoint]
               /\ SubSeq(log'[recipient], 1, endpoint)
                    = SubSeq(log[recipient], 1, endpoint)
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, NEW endpoint \in 1..m.mprevLogIndex,
                    EntryEdgeBase, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m),
                    m.mprevLogIndex <= Len(log[recipient])
             PROVE /\ log'[recipient][endpoint] = log[recipient][endpoint]
                   /\ SubSeq(log'[recipient], 1, endpoint) = SubSeq(log[recipient], 1, endpoint)
    BY SMT
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry)
    BY SMT, MessageFieldsTypeOK DEF EntryEdgeBase, TypeOK, LogVarsTypeOK, MsgTypeOK
<1>2. CASE log' = log
    BY SMT, <1>2
<1>3. CASE log' # log
    <2>1. m.mentries # << >> /\
           log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
        BY SMT, <1>1, <1>3 DEF HandleAppendEntriesRequest
    <2>2. m.mentries[1] \in LogEntry
        BY SMT, <1>1, <2>1, LenProperties, EmptySeq, ElementOfSeq
    <2> QED BY SMT, <1>1, <2>1, <2>2, TruncateAppendRetainsPrefix
<1> QED BY SMT, <1>2, <1>3

LEMMA AppendRequestChangedLogShape ==
    \A recipient, sender \in Server, m \in messages:
        /\ EntryEdgeBase /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, m) /\ log' # log
        => /\ m.mprevLogIndex \in 0..Len(log[recipient])
           /\ m.mentries # << >> /\ m.mentries[1] \in LogEntry
           /\ Len(log'[recipient]) = m.mprevLogIndex + 1
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, EntryEdgeBase,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m), log' # log
             PROVE /\ m.mprevLogIndex \in 0..Len(log[recipient])
                   /\ m.mentries # << >> /\ m.mentries[1] \in LogEntry
                   /\ Len(log'[recipient]) = m.mprevLogIndex + 1
    BY SMT
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry) /\ currentTerm \in [Server -> Nat]
    BY SMT, MessageFieldsTypeOK DEF EntryEdgeBase, TypeOK, LogVarsTypeOK,
                               ServerVarsTypeOK, MsgTypeOK
<1>2. m.mprevLogIndex \in 0..Len(log[recipient]) /\ m.mentries # << >> /\
       log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
    BY SMT, <1>1 DEF HandleAppendEntriesRequest
<1>3. m.mentries[1] \in LogEntry
    BY SMT, <1>1, <1>2, EmptySeq, ElementOfSeq
<1>4. SubSeq(log[recipient], 1, m.mprevLogIndex) \in Seq(LogEntry) /\
       Len(SubSeq(log[recipient], 1, m.mprevLogIndex)) = m.mprevLogIndex
    BY SMT, <1>1, <1>2, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>5. Len(log'[recipient]) = m.mprevLogIndex + 1
    BY SMT, <1>2, <1>3, <1>4, AppendProperties
<1> QED BY SMT, <1>2, <1>3, <1>5

LEMMA AppendRequestCopiesEndpointEntry ==
    \A recipient, sender \in Server, m \in messages:
        /\ EntryEdgeBase /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, m) /\ log' # log
        => log'[recipient][m.mprevLogIndex + 1] = m.mentries[1]
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, EntryEdgeBase,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m), log' # log
             PROVE log'[recipient][m.mprevLogIndex + 1] = m.mentries[1]
    BY SMT
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat
    BY SMT, MessageFieldsTypeOK DEF EntryEdgeBase, TypeOK, LogVarsTypeOK, MsgTypeOK
<1>2. m.mprevLogIndex \in 0..Len(log[recipient]) /\ m.mentries[1] \in LogEntry
    BY SMT, AppendRequestChangedLogShape
<1>3. log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
    BY SMT, <1>1 DEF HandleAppendEntriesRequest
<1>4. SubSeq(log[recipient], 1, m.mprevLogIndex) \in Seq(LogEntry) /\
       Len(SubSeq(log[recipient], 1, m.mprevLogIndex)) = m.mprevLogIndex
    BY SMT, <1>1, <1>2, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1> QED BY SMT, <1>2, <1>3, <1>4, AppendProperties

LEMMA AppendRequestAcceptedPreviousAnchor ==
    \A recipient, sender \in Server, request \in messages:
        /\ EntryEdgeBase /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, request) /\ log' # log
        /\ request.mprevLogIndex > 0
        => log[recipient][request.mprevLogIndex].term = request.mprevLogTerm
    BY SMT DEF HandleAppendEntriesRequest

LEMMA AppendRetainsLogEntryEdge ==
    \A entries \in Seq(LogEntry), entry \in LogEntry:
        \A index \in DOMAIN entries:
            LogEntryEdge(Append(entries, entry), index) = LogEntryEdge(entries, index)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW index \in DOMAIN entries
             PROVE LogEntryEdge(Append(entries, entry), index)
                     = LogEntryEdge(entries, index)
    BY SMT
<1>1. index \in 1..Len(entries) /\ Len(entries) \in Nat
    BY SMT, LenProperties
<1>2. Append(entries, entry)[index] = entries[index]
    BY SMT, <1>1, AppendProperties
<1>3. CASE index = 1
    BY SMT, <1>2, <1>3 DEF LogEntryEdge
<1>4. CASE index # 1
    <2>1. index - 1 \in 1..Len(entries)
        BY SMT, <1>1, <1>4
    <2>2. Append(entries, entry)[index - 1] = entries[index - 1]
        BY SMT, <2>1, AppendProperties
    <2> QED BY SMT, <1>2, <2>2 DEF LogEntryEdge
<1> QED BY SMT, <1>3, <1>4

LEMMA ClientHistoricalEntryEdges ==
    \A i \in Server, payload \in ClientPayload:
        EntryEdgeBase /\ ClientRequest(i, payload)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup
             {LogEntryEdge(log'[i], Len(log[i]) + 1)}
<1> SUFFICES ASSUME NEW i \in Server, NEW payload \in ClientPayload,
                    EntryEdgeBase, ClientRequest(i, payload)
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup
                     {LogEntryEdge(log'[i], Len(log[i]) + 1)}
    BY SMT
<1> DEFINE fresh == LogEntryEdge(log'[i], Len(log[i]) + 1)
<1>0. log \in [Server -> Seq(LogEntry)] /\ currentTerm \in [Server -> Nat]
    BY SMT DEF EntryEdgeBase, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>entry. PICK entry \in LogEntry:
        /\ entry.term = currentTerm[i]
        /\ log'[i] = Append(log[i], entry)
    BY ClientRequestAppendsCurrentTerm, SMT DEF EntryEdgeBase
<1>1. log'[i] = Append(log[i], entry) /\
       (\A server \in Server: server # i => log'[server] = log[server]) /\
       AppendRequests' = AppendRequests
    BY SMT, <1>0, <1>entry DEF ClientRequest, AppendRequests
<1>2. DOMAIN log'[i] = 1..(Len(log[i]) + 1) /\
       DOMAIN log[i] = 1..Len(log[i]) /\ Len(log[i]) \in Nat
    BY SMT, <1>0, <1>1, AppendProperties, LenProperties
<1>3. \A index \in DOMAIN log[i]:
          LogEntryEdge(log'[i], index) = LogEntryEdge(log[i], index)
    BY SMT, <1>0, <1>1, AppendRetainsLogEntryEdge
<1>4. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh}
    <2> SUFFICES ASSUME NEW edge \in HistoricalEntryEdges'
                 PROVE edge \in HistoricalEntryEdges \cup {fresh}
        BY SMT
    <2>1. CASE \E server \in Server: \E index \in DOMAIN log'[server]:
                  edge = LogEntryEdge(log'[server], index)
        <3>1. PICK server, index:
                  server \in Server /\ index \in DOMAIN log'[server] /\ edge = LogEntryEdge(log'[server], index)
            BY SMT, <2>1
        <3>2. CASE server # i
            BY SMT, <1>1, <3>1, <3>2 DEF HistoricalEntryEdges
        <3>3. CASE server = i /\ index \in DOMAIN log[i]
            <4>same. edge = LogEntryEdge(log[i], index)
                BY <1>0, <1>3, <3>1, <3>3, SMT
            <4>member. edge \in
                    {LogEntryEdge(log[i], position): position \in DOMAIN log[i]}
                BY <1>0, <4>same, <3>3, SMT
            <4>family.
                    {LogEntryEdge(log[i], position): position \in DOMAIN log[i]}
                        \in {{LogEntryEdge(log[holder], position):
                                  position \in DOMAIN log[holder]}:
                                holder \in Server}
                BY <1>0, SMT
            <4> QED BY <4>member, <4>family, SMT DEF HistoricalEntryEdges
        <3>4. CASE server = i /\ index \notin DOMAIN log[i]
            <4>1. index = Len(log[i]) + 1
                BY SMT, <1>2, <3>1, <3>4
            <4> QED BY SMT, <3>1, <3>4, <4>1 DEF fresh
        <3> QED BY SMT, <3>2, <3>3, <3>4
    <2>2. CASE \E request \in AppendRequests':
                  \E offset \in DOMAIN request.mentries:
                      edge = RequestEntryEdge(request, offset)
        BY SMT, <1>1, <2>2 DEF HistoricalEntryEdges
    <2> QED BY SMT, <2>1, <2>2 DEF HistoricalEntryEdges
<1> QED BY SMT, <1>4 DEF fresh

LEMMA AppendSendEntryOffsetSnapshot ==
    \A sender, recipient \in Server:
        EntryEdgeBase =>
            \A offset \in DOMAIN AppendEntriesEntries(sender, recipient):
                /\ offset = 1
                /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
                /\ AppendEntriesEntries(sender, recipient)[offset]
                    = log[sender][nextIndex[sender][recipient]]
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    EntryEdgeBase,
                    NEW offset \in DOMAIN AppendEntriesEntries(sender, recipient)
             PROVE /\ offset = 1
                   /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
                   /\ AppendEntriesEntries(sender, recipient)[offset]
                        = log[sender][nextIndex[sender][recipient]]
    BY SMT
<1>1. TypeOK /\ nextIndex[sender][recipient] \in Nat \ {0} /\
       log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) <= Len(log[sender]) /\
       AppendEntriesLastEntry(sender, recipient) <= nextIndex[sender][recipient]
    BY SMT, AppendEntriesLastEntryTypeOK, MinTypeOK, LenProperties
       DEF EntryEdgeBase, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK,
           AppendEntriesLastEntry
<1>2. \A index \in nextIndex[sender][recipient]..AppendEntriesLastEntry(sender, recipient):
        log[sender][index] \in LogEntry
    BY SMT, <1>1, ElementOfSeq
<1>3. AppendEntriesEntries(sender, recipient) \in Seq(LogEntry) /\
       Len(AppendEntriesEntries(sender, recipient)) =
           IF nextIndex[sender][recipient] <= AppendEntriesLastEntry(sender, recipient)
           THEN AppendEntriesLastEntry(sender, recipient) - nextIndex[sender][recipient] + 1
           ELSE 0
    BY SMT, <1>1, <1>2, AppendEntriesEntriesTypeOK, SubSeqProperties
       DEF AppendEntriesEntries
<1>4. Len(AppendEntriesEntries(sender, recipient)) <= 1
    BY <1>1, <1>3, SMT
<1>5. Len(AppendEntriesEntries(sender, recipient)) \in Nat /\
       DOMAIN AppendEntriesEntries(sender, recipient)
           = 1..Len(AppendEntriesEntries(sender, recipient))
    BY SMT, <1>3, LenProperties
<1>6. offset = 1 /\ Len(AppendEntriesEntries(sender, recipient)) = 1
    BY <1>4, <1>5, SMT
<1>7. AppendEntriesEntries(sender, recipient) # << >>
    BY SMT, <1>3, <1>6, EmptySeq
<1>8. nextIndex[sender][recipient] \in DOMAIN log[sender] /\
       AppendEntriesEntries(sender, recipient)[1]
           = log[sender][nextIndex[sender][recipient]]
    BY SMT, <1>1, <1>7, AppendEntriesFirstEntrySnapshot
<1> QED BY SMT, <1>6, <1>8

LEMMA AppendSendPreviousSnapshot ==
    \A sender, recipient \in Server:
        EntryEdgeBase /\ state[sender] = Leader =>
            /\ nextIndex[sender][recipient] - 1 \in Nat
            /\ (nextIndex[sender][recipient] = 1 =>
                AppendEntriesPrevLogTerm(sender, recipient) = 0)
            /\ (nextIndex[sender][recipient] > 1 =>
                /\ nextIndex[sender][recipient] - 1 \in DOMAIN log[sender]
                /\ AppendEntriesPrevLogTerm(sender, recipient)
                    = log[sender][nextIndex[sender][recipient] - 1].term)
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    EntryEdgeBase, state[sender] = Leader
             PROVE /\ nextIndex[sender][recipient] - 1 \in Nat
                   /\ (nextIndex[sender][recipient] = 1 =>
                       AppendEntriesPrevLogTerm(sender, recipient) = 0)
                   /\ (nextIndex[sender][recipient] > 1 =>
                       /\ nextIndex[sender][recipient] - 1 \in DOMAIN log[sender]
                       /\ AppendEntriesPrevLogTerm(sender, recipient)
                           = log[sender][nextIndex[sender][recipient] - 1].term)
    BY SMT
<1>1. nextIndex[sender][recipient] \in Nat \ {0} /\
       nextIndex[sender][recipient] <= Len(log[sender]) + 1 /\
       log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat /\
       DOMAIN log[sender] = 1..Len(log[sender])
    BY SMT, LenProperties
       DEF EntryEdgeBase, NextIndexBound, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>2. nextIndex[sender][recipient] - 1 \in Nat /\
       (nextIndex[sender][recipient] > 1 =>
           nextIndex[sender][recipient] - 1 \in DOMAIN log[sender])
    BY <1>1, SMT
<1> QED BY SMT, <1>1, <1>2 DEF AppendEntriesPrevLogTerm

LEMMA AppendSendRequestEdgeSnapshot ==
    \A sender, recipient \in Server:
        EntryEdgeBase /\ state[sender] = Leader =>
            \A offset \in DOMAIN AppendEntriesMessage(sender, recipient).mentries:
                /\ AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
                    \in DOMAIN log[sender]
                /\ RequestEntryEdge(AppendEntriesMessage(sender, recipient), offset)
                    = LogEntryEdge(log[sender],
                        AppendEntriesMessage(sender, recipient).mprevLogIndex + offset)
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    EntryEdgeBase, state[sender] = Leader,
                    NEW offset \in DOMAIN AppendEntriesMessage(sender, recipient).mentries
             PROVE /\ AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
                        \in DOMAIN log[sender]
                   /\ RequestEntryEdge(AppendEntriesMessage(sender, recipient), offset)
                        = LogEntryEdge(log[sender],
                            AppendEntriesMessage(sender, recipient).mprevLogIndex + offset)
    BY SMT
<1>1. offset \in DOMAIN AppendEntriesEntries(sender, recipient)
    BY SMT DEF AppendEntriesMessage
<1>2. offset = 1 /\ nextIndex[sender][recipient] \in DOMAIN log[sender] /\
       AppendEntriesEntries(sender, recipient)[offset]
           = log[sender][nextIndex[sender][recipient]]
    BY SMT, <1>1, AppendSendEntryOffsetSnapshot
<1>3. nextIndex[sender][recipient] \in Nat \ {0} /\
       AppendEntriesMessage(sender, recipient).mprevLogIndex
           = nextIndex[sender][recipient] - 1 /\
       AppendEntriesMessage(sender, recipient).mentries
           = AppendEntriesEntries(sender, recipient) /\
       AppendEntriesMessage(sender, recipient).mprevLogTerm
           = AppendEntriesPrevLogTerm(sender, recipient)
    BY SMT DEF EntryEdgeBase, TypeOK, LeaderVarsTypeOK, AppendEntriesMessage
<1>4. AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
           = nextIndex[sender][recipient]
    BY <1>2, <1>3, SMT
<1>5. CASE nextIndex[sender][recipient] = 1
    BY SMT, <1>2, <1>3, <1>4, <1>5, AppendSendPreviousSnapshot
       DEF RequestEntryEdge, LogEntryEdge
<1>6. CASE nextIndex[sender][recipient] > 1
    BY SMT, <1>2, <1>3, <1>4, <1>6, AppendSendPreviousSnapshot
       DEF RequestEntryEdge, LogEntryEdge
<1> QED BY SMT, <1>3, <1>5, <1>6

LEMMA EntryEdgeAppendSendSubset ==
    \A i, j \in Server:
        EntryEdgeBase /\ AppendEntries(i, j)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    EntryEdgeBase, AppendEntries(i, j)
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    BY SMT
<1>1. log' = log /\ state[i] = Leader /\
       messages' = messages \cup {AppendEntriesMessage(i, j)} /\
       AppendRequests' = AppendRequests \cup {AppendEntriesMessage(i, j)}
    BY SMT DEF AppendEntries, Send, WithMessage, WithMessages,
           AppendRequests, AppendEntriesMessage
<1>2. \A server \in Server: \A index \in DOMAIN log'[server]:
        LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
    BY SMT, <1>1 DEF HistoricalEntryEdges
<1>3. \A request \in AppendRequests':
        \A offset \in DOMAIN request.mentries:
            RequestEntryEdge(request, offset) \in HistoricalEntryEdges
    <2> SUFFICES ASSUME NEW request \in AppendRequests',
                        NEW offset \in DOMAIN request.mentries
                 PROVE RequestEntryEdge(request, offset) \in HistoricalEntryEdges
        BY SMT
    <2>1. CASE request \in AppendRequests
        BY SMT, <2>1 DEF HistoricalEntryEdges
    <2>2. CASE request = AppendEntriesMessage(i, j)
        <3>1. request.mprevLogIndex + offset \in DOMAIN log[i] /\
               RequestEntryEdge(request, offset)
                   = LogEntryEdge(log[i], request.mprevLogIndex + offset)
            BY SMT, <1>1, <2>2, AppendSendRequestEdgeSnapshot
        <3> QED BY SMT, <3>1 DEF HistoricalEntryEdges
    <2> QED BY SMT, <1>1, <2>1, <2>2
<1> QED BY SMT, <1>2, <1>3 DEF HistoricalEntryEdges

LEMMA AppendRequestRootTermInit == Init => AppendRequestRootTerm
    BY SMT DEF Init, AppendRequests, AppendRequestRootTerm

LEMMA AppendRequestRootTermNext ==
    EntryEdgeBase /\ AppendRequestRootTerm /\ [Next]_vars => AppendRequestRootTerm'
<1> SUFFICES ASSUME EntryEdgeBase, AppendRequestRootTerm, [Next]_vars,
                    NEW m \in AppendRequests', m.mprevLogIndex = 0
             PROVE m.mprevLogTerm = 0
    BY SMT DEF AppendRequestRootTerm
<1>1. CASE m \in messages
    BY SMT, <1>1 DEF AppendRequests, AppendRequestRootTerm
<1>2. CASE m \notin messages
    <2>1. PICK i, j \in Server: AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
        BY SMT, <1>2, NewAppendRequestOrigin DEF AppendRequests
    <2> QED BY SMT, <2>1 DEF AppendEntriesMessage, AppendEntriesPrevLogTerm,
                            EntryEdgeBase, TypeOK, LeaderVarsTypeOK
<1> QED BY SMT, <1>1, <1>2

LEMMA AppendReceiveLogEdgeOrigin ==
    \A i, j \in Server, m \in messages:
        EntryEdgeBase /\ AppendRequestRootTerm /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => \A server \in Server: \A index \in DOMAIN log'[server]:
            LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server, NEW m \in messages,
                    EntryEdgeBase, AppendRequestRootTerm, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(i, j, m), NEW server \in Server,
                    NEW index \in DOMAIN log'[server]
             PROVE LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
    BY SMT
<1>0. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry) /\ m \in AppendRequests
    BY SMT, MessageFieldsTypeOK DEF EntryEdgeBase, TypeOK, LogVarsTypeOK, MsgTypeOK, AppendRequests
<1>1. CASE log' = log
    BY SMT, <1>1 DEF HistoricalEntryEdges
<1>2. CASE server # i
    <2>1. log'[server] = log[server]
        BY SMT, <1>0, <1>2 DEF HandleAppendEntriesRequest
    <2> QED BY SMT, <2>1 DEF HistoricalEntryEdges
<1>3. CASE log' # log /\ server = i
    <2>shape. m.mprevLogIndex \in 0..Len(log[i]) /\ m.mentries # << >> /\
              m.mentries[1] \in LogEntry /\ Len(log'[i]) = m.mprevLogIndex + 1
        BY SMT, <1>3, AppendRequestChangedLogShape
    <2>seq. SubSeq(log[i], 1, m.mprevLogIndex) \in Seq(LogEntry)
        BY SMT, <1>0, <2>shape, SubSeqProperties, ElementOfSeq, LenProperties,
           1 \in Int, Nat \subseteq Int
    <2>post. log'[i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])
        BY SMT, <1>0, <1>3 DEF HandleAppendEntriesRequest
    <2>typed. log'[i] \in Seq(LogEntry) /\ Len(log'[i]) \in Nat /\
              DOMAIN log'[i] = 1..Len(log'[i]) /\ DOMAIN m.mentries = 1..Len(m.mentries) /\
              Len(m.mentries) \in Nat
        BY SMT, <1>0, <2>shape, <2>seq, <2>post, AppendProperties, LenProperties
    <2>0. m.mprevLogIndex \in 0..Len(log[i]) /\ m.mentries # << >> /\
           Len(log'[i]) = m.mprevLogIndex + 1 /\
           DOMAIN log'[i] = 1..(m.mprevLogIndex + 1) /\ 1 \in DOMAIN m.mentries /\ index \in Nat
        BY SMT, <1>0, <1>3, <2>shape, <2>typed, EmptySeq
    <2>1. CASE index <= m.mprevLogIndex
        <3>1. index \in DOMAIN log[i] /\ log'[i][index] = log[i][index]
            BY SMT, <1>0, <1>3, <2>0, <2>1, AppendRequestRetainsMatchedPrefix, LenProperties
        <3>2. index > 1 => log'[i][index - 1] = log[i][index - 1]
            BY SMT, <1>0, <1>3, <2>0, <2>1, AppendRequestRetainsMatchedPrefix
        <3>3. LogEntryEdge(log'[server], index) = LogEntryEdge(log[i], index)
            BY SMT, <1>3, <2>0, <3>1, <3>2 DEF LogEntryEdge
        <3> QED BY SMT, <3>1, <3>3 DEF HistoricalEntryEdges
    <2>2. CASE index > m.mprevLogIndex
        <3>1. index = m.mprevLogIndex + 1 /\ log'[i][index] = m.mentries[1]
            BY SMT, <1>3, <2>0, <2>2, AppendRequestCopiesEndpointEntry
        <3>2. m.mprevLogIndex > 0 =>
                log'[i][index - 1].term = m.mprevLogTerm
            BY SMT, <1>0, <1>3, <2>0, <3>1, AppendRequestAcceptedPreviousAnchor,
               AppendRequestRetainsMatchedPrefix
        <3>3. m.mprevLogIndex = 0 => m.mprevLogTerm = 0
            BY SMT, <1>0 DEF AppendRequestRootTerm
        <3>4. LogEntryEdge(log'[server], index) = RequestEntryEdge(m, 1)
            BY SMT, <1>0, <1>3, <3>1, <3>2, <3>3 DEF LogEntryEdge, RequestEntryEdge
        <3> QED BY SMT, <1>0, <2>0, <3>4 DEF HistoricalEntryEdges
    <2> QED BY SMT, <2>0, <2>1, <2>2
<1> QED BY SMT, <1>1, <1>2, <1>3

LEMMA AppendReceiveRequestEdgesUnchanged ==
    \A i, j \in Server, m \in messages:
        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => AppendRequests' = AppendRequests
    BY SMT, MessageTypesDistinct DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages, AppendRequests

LEMMA EntryEdgeAppendReceiveSubset ==
    \A i, j \in Server, m \in messages:
        EntryEdgeBase /\ AppendRequestRootTerm /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    BY SMT, AppendReceiveLogEdgeOrigin, AppendReceiveRequestEdgesUnchanged DEF HistoricalEntryEdges

LEMMA LogChangingActionNext ==
    EntryEdgeBase /\ [Next]_vars =>
        \/ (\E leader \in Server, payload \in ClientPayload: ClientRequest(leader, payload))
        \/ (\E m \in messages:
                m.mtype = AppendEntriesRequest /\
                HandleAppendEntriesRequest(m.mdest, m.msource, m))
        \/ log' = log
<1> SUFFICES ASSUME EntryEdgeBase, [Next]_vars, log' # log,
                    ~(\E leader \in Server, payload \in ClientPayload: ClientRequest(leader, payload))
             PROVE \E m \in messages:
                 m.mtype = AppendEntriesRequest /\
                 HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY SMT
<1>receive. \E m \in messages: Receive(m)
    BY SMT DEF Next, vars, Restart, Timeout, BecomeLeader,
           AdvanceCommitIndex, AppendEntries, LeaderStepDown
<1> PICK m \in messages: Receive(m) BY SMT, <1>receive
<1>types. /\ m.mterm \in Nat /\ m.mdest \in Server /\ m.msource \in Server
    BY SMT, MessageFieldsTypeOK DEF EntryEdgeBase, TypeOK, MsgTypeOK
<1>append. m.mtype = AppendEntriesRequest /\
           HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY SMT, <1>types
       DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
           HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY SMT, <1>append

LEMMA EntryEdgeOtherSubset ==
    EntryEdgeBase /\ [Next]_vars
    /\ ~(\E i \in Server, payload \in ClientPayload: ClientRequest(i, payload))
    /\ ~(\E i, j \in Server: AppendEntries(i, j))
    /\ ~(\E i, j \in Server, m \in messages:
            m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m))
    => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
<1> SUFFICES ASSUME EntryEdgeBase, [Next]_vars,
                    ~(\E i \in Server, payload \in ClientPayload: ClientRequest(i, payload)),
                    ~(\E i, j \in Server: AppendEntries(i, j)),
                    ~(\E i, j \in Server, m \in messages:
                        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m))
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    BY SMT
<1>types. \A m \in messages: m.mdest \in Server /\ m.msource \in Server
    BY SMT, StoredMessageFieldsTypeOK DEF EntryEdgeBase
<1>1. log' = log
    BY SMT, LogChangingActionNext, <1>types
<1>2. AppendRequests' \subseteq AppendRequests
    BY SMT, NewAppendRequestOrigin DEF AppendRequests
<1> QED BY SMT, <1>1, <1>2 DEF HistoricalEntryEdges

LEMMA ConsistentLogEdgesPrefixEqual ==
    \A left, right \in Seq(LogEntry):
        /\ \A index \in (DOMAIN left) \cap (DOMAIN right):
            left[index].term = right[index].term =>
                /\ left[index] = right[index]
                /\ index > 1 => left[index - 1].term = right[index - 1].term
        => \A endpoint \in (DOMAIN left) \cap (DOMAIN right):
            left[endpoint].term = right[endpoint].term =>
                SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    \A index \in (DOMAIN left) \cap (DOMAIN right):
                        left[index].term = right[index].term =>
                            /\ left[index] = right[index]
                            /\ index > 1 => left[index - 1].term = right[index - 1].term
             PROVE \A endpoint \in (DOMAIN left) \cap (DOMAIN right):
                        left[endpoint].term = right[endpoint].term =>
                            SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
    BY SMT
<1> DEFINE P(n) == n \in (DOMAIN left) \cap (DOMAIN right) /\ left[n].term = right[n].term
                   => SubSeq(left, 1, n) = SubSeq(right, 1, n)
<1>0. Len(left) \in Nat /\ Len(right) \in Nat /\
       DOMAIN left = 1..Len(left) /\ DOMAIN right = 1..Len(right)
    BY SMT, LenProperties
<1>1. P(0)
    BY SMT, <1>0 DEF P
<1>2. \A n \in Nat: P(n) => P(n + 1)
    <2> SUFFICES ASSUME NEW n \in Nat, P(n),
                        n + 1 \in (DOMAIN left) \cap (DOMAIN right),
                        left[n + 1].term = right[n + 1].term
                 PROVE SubSeq(left, 1, n + 1) = SubSeq(right, 1, n + 1)
        BY SMT DEF P
    <2>1. left[n + 1] = right[n + 1]
        BY SMT
    <2>2. SubSeq(left, 1, n) = SubSeq(right, 1, n)
        <3>1. CASE n = 0
            BY SMT, <1>0, <3>1, SubSeqProperties, EmptySeq
        <3>2. CASE n > 0
            BY SMT, <1>0, <3>2 DEF P
        <3> QED BY SMT, <3>1, <3>2
    <2>3. \A index \in 1..(n + 1): left[index] = right[index]
        <3> SUFFICES ASSUME NEW index \in 1..(n + 1)
                     PROVE left[index] = right[index]
            BY SMT
        <3>1. CASE index = n + 1
            BY SMT, <2>1, <3>1
        <3>2. CASE index # n + 1
            <4>1. index \in Nat /\ index \in 1..n /\ n <= Len(left) /\ n <= Len(right)
                BY SMT, <1>0, <3>2
            <4> QED BY SMT, <2>2, <4>1, EqualLogPrefixesEntryEqual
        <3> QED BY SMT, <3>1, <3>2
    <2>4. SubSeq(left, 1, n + 1) \in Seq(LogEntry) /\
           SubSeq(right, 1, n + 1) \in Seq(LogEntry) /\
           Len(SubSeq(left, 1, n + 1)) = n + 1 /\ Len(SubSeq(right, 1, n + 1)) = n + 1
        BY SMT, <1>0, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
    <2>5. \A index \in 1..(n + 1):
            SubSeq(left, 1, n + 1)[index] = SubSeq(right, 1, n + 1)[index]
        BY SMT, <1>0, <2>3, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
    <2> QED BY SMT, <2>4, <2>5, SeqEqual
<1> HIDE DEF P
<1>3. \A n \in Nat: P(n)
    BY <1>1, <1>2, NatInduction, Isa
<1> QED BY SMT, <1>0, <1>3 DEF P

LEMMA EntryEdgeConsistencyLogBoundary ==
    EntryEdgeBase /\ EntryEdgeConsistency =>
        \A left, right \in Server:
            \A index \in (DOMAIN log[left]) \cap (DOMAIN log[right]):
                log[left][index].term = log[right][index].term =>
                    /\ log[left][index] = log[right][index]
                    /\ index > 1 => log[left][index - 1].term = log[right][index - 1].term
<1> SUFFICES ASSUME EntryEdgeBase, EntryEdgeConsistency,
                    NEW left \in Server, NEW right \in Server,
                    NEW index \in (DOMAIN log[left]) \cap (DOMAIN log[right]),
                    log[left][index].term = log[right][index].term
             PROVE /\ log[left][index] = log[right][index]
                   /\ index > 1 => log[left][index - 1].term = log[right][index - 1].term
    BY SMT
<1>1. LogEntryEdge(log[left], index) \in HistoricalEntryEdges /\
       LogEntryEdge(log[right], index) \in HistoricalEntryEdges
    BY SMT DEF HistoricalEntryEdges
<1> QED BY SMT, <1>1 DEF EntryEdgeConsistency, LogEntryEdge

LEMMA EntryEdgeConsistencyImpliesLogMatching ==
    EntryEdgeBase /\ EntryEdgeConsistency => LogMatchingInv
    BY SMT, EntryEdgeConsistencyLogBoundary, ConsistentLogEdgesPrefixEqual, LenProperties
       DEF EntryEdgeBase, TypeOK, LogVarsTypeOK, LogMatchingInv

LEMMA OwnerPrefixClientRequest ==
    \A owner, actor \in Server, term \in Nat, prefix \in Seq(LogEntry),
       payload \in ClientPayload:
        TypeOK /\ OwnerPrefix(owner, term, prefix) /\ ClientRequest(actor, payload)
        => OwnerPrefix(owner, term, prefix)'
    BY ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF OwnerPrefix, TypeOK, ServerVarsTypeOK, LogVarsTypeOK, ClientRequest

LEMMA OwnerPrefixOtherActions ==
    \A owner \in Server, term \in Nat, prefix \in Seq(LogEntry):
        /\ TypeOK /\ OwnerPrefix(owner, term, prefix)
        /\ \/ UNCHANGED vars
           \/ \E actor \in Server: Restart(actor)
           \/ \E actor \in Server: Timeout(actor)
           \/ \E actor \in Server: BecomeLeader(actor)
           \/ \E actor \in Server: AdvanceCommitIndex(actor)
           \/ \E actor, peer \in Server: AppendEntries(actor, peer)
           \/ \E actor \in Server: LeaderStepDown(actor)
           \/ \E message \in messages: Receive(message)
        => OwnerPrefix(owner, term, prefix)'
    BY ServerStatesDistinct, MessageFieldsTypeOK, SMT
    DEF OwnerPrefix, TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK,
        vars, Restart, Timeout, BecomeLeader, AdvanceCommitIndex, AppendEntries,
        LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse

LEMMA OwnerPrefixNext ==
    \A owner \in Server, term \in Nat, prefix \in Seq(LogEntry):
        TypeOK /\ OwnerPrefix(owner, term, prefix) /\ [Next]_vars
        => OwnerPrefix(owner, term, prefix)'
    BY OwnerPrefixClientRequest, OwnerPrefixOtherActions, SMT DEF Next
LEMMA WitnessPrefixLastTerm ==
    ASSUME NEW witness, WitnessPrefixData(witness)
    PROVE Len(witness.prefix) > 0 /\ LastTerm(witness.prefix) = witness.edge.term
    BY LenProperties, SMT DEF WitnessPrefixData, LogEntryEdge, LastTerm
LEMMA CampaignsSupplyEntryBounds ==
    ASSUME NEW voteHistory
    PROVE MembershipCampaignsInv(voteHistory) => EntryEdgeBase /\ SendInvariant
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, EntryEdgeBase

LEMMA CertificateWitnessNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A witness:
        /\ TypeOK /\ SendInvariant /\ [Next]_vars
        /\ CertificateWitness(voteHistory, witness)
        => CertificateWitness(nextVoteHistory, witness)'
    BY RetainedElectionCertificateNext, OwnerPrefixNext, SMT
    DEF CertificateWitness, WitnessPrefixData

LEMMA CertificateFamilyNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A family:
        TypeOK /\ SendInvariant /\ [Next]_vars /\ CertificateFamily(voteHistory, family)
        => CertificateFamily(nextVoteHistory, family)'
    BY CertificateWitnessNext, SMT DEF CertificateFamily, CampaignHistoryContextStep

LEMMA ExtendCertificateFamilyAfter ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A family, fresh:
        /\ CertificateFamily(nextVoteHistory, family)'
        /\ CertificateWitness(nextVoteHistory, fresh)'
        /\ \A index \in DOMAIN fresh.prefix:
               \E ancestor \in family \cup {fresh}:
                   ancestor.edge = LogEntryEdge(fresh.prefix, index)
        => CertificateFamily(nextVoteHistory, family \cup {fresh})'
    BY FS_AddElement, SMT DEF CertificateFamily

LEMMA EntryAncestrySubsetNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE /\ TypeOK /\ SendInvariant /\ [Next]_vars /\ EntryAncestryInv(voteHistory)
    /\ HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    => EntryAncestryInv(nextVoteHistory)'
    BY CertificateFamilyNext, SMT DEF EntryAncestryInv, CoversEntryEdges

LEMMA ClientRequestCreatesCertificateWitness ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A actor \in Server, payload \in ClientPayload:
        MembershipCampaignsInv(voteHistory) /\ ClientRequest(actor, payload) =>
        \E fresh:
            /\ fresh.prefix = log'[actor]
            /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
            /\ CertificateWitness(nextVoteHistory, fresh)'
<1> SUFFICES ASSUME NEW actor \in Server, NEW payload \in ClientPayload,
                      MembershipCampaignsInv(voteHistory), ClientRequest(actor, payload)
             PROVE \E fresh:
                       /\ fresh.prefix = log'[actor]
                       /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
                       /\ CertificateWitness(nextVoteHistory, fresh)'
    BY SMT
<1>base.
        /\ TypeOK /\ SendInvariant /\ LogStructureInv
        /\ LogTermsMonotonic /\ LogTermBoundInv
    BY LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, TermOrderingInv
<1>next. [Next]_vars BY SMT DEF Next
<1>term. PICK term \in Nat: term = currentTerm[actor]
    BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK
<1>prefix. PICK prefix \in Seq(LogEntry): prefix = log'[actor]
    BY <1>base, ClientRequestLogTypeOK, SMT DEF LogVarsTypeOK
<1>appended.
        /\ Len(prefix) = Len(log[actor]) + 1
        /\ Len(prefix) \in Nat \ {0}
        /\ prefix[Len(prefix)].term = term
    BY <1>base, <1>term, <1>prefix, ClientRequestAppendsCurrentTerm,
       AppendProperties, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1>captured. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, actor, term, snapshot, occurrence, support)
        /\ snapshot = CampaignPrefix(log[actor], term)
        /\ IsPrefix(snapshot, prefix)
        /\ Len(snapshot) < Len(prefix)
    BY <1>term, <1>prefix, ClientRequestCapturesElectionCertificate, SMT
<1>canonical. snapshot = CampaignPrefix(prefix, term)
    BY <1>base, <1>term, <1>prefix, <1>captured, ClientRequestPreservesCampaignPrefix, SMT
    DEF ClientRequest
<1>certificate_after.
        RetainedElectionCertificate(nextVoteHistory, actor, term, snapshot, occurrence, support)'
    BY <1>base, <1>next, <1>term, <1>captured, RetainedElectionCertificateNext, SMT
<1>ordered. TermsOrdered(prefix)
    BY <1>base, <1>prefix, ClientRequestPreservesLogTermsMonotonic, SMT
    DEF OrderingBase, LogTermsMonotonic, TermsOrdered
<1>structure. EntryStructure(prefix, term)
    BY <1>base, <1>term, <1>prefix, ClientRequestPreservesLogStructure, SMT
    DEF LogStructureInv, ClientRequest
<1> DEFINE fresh ==
        [edge |-> LogEntryEdge(prefix, Len(prefix)), prefix |-> prefix,
         owner |-> actor, snapshot |-> snapshot,
         occurrence |-> occurrence, support |-> support]
<1>fields.
        /\ fresh.prefix = prefix
        /\ fresh.edge.index = Len(prefix)
        /\ fresh.edge.term = term
        /\ fresh.owner = actor
        /\ fresh.snapshot = snapshot
        /\ fresh.occurrence = occurrence
        /\ fresh.support = support
    BY <1>appended, SMT DEF fresh, LogEntryEdge
<1>data. WitnessPrefixData(fresh)
    BY <1>term, <1>prefix, <1>appended, <1>captured, <1>canonical,
       <1>ordered, <1>structure, <1>fields, SMT
    DEF WitnessPrefixData, fresh
<1>owner_after. OwnerPrefix(actor, term, prefix)'
    BY <1>base, <1>term, <1>prefix, WholeSequencePrefix, SMT
    DEF OwnerPrefix, IsPrefix, ClientRequest, TypeOK, ServerVarsTypeOK
<1>valid. CertificateWitness(nextVoteHistory, fresh)'
    BY <1>data, <1>fields, <1>owner_after, <1>certificate_after, SMT
    DEF CertificateWitness
<1> QED BY <1>valid, <1>prefix, <1>appended, SMT DEF fresh

LEMMA ClientRequestPreservesEntryAncestry ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A actor \in Server, payload \in ClientPayload:
        /\ MembershipCampaignsInv(voteHistory) /\ EntryAncestryInv(voteHistory)
        /\ ClientRequest(actor, payload)
        => EntryAncestryInv(nextVoteHistory)'
<1> SUFFICES ASSUME NEW actor \in Server, NEW payload \in ClientPayload,
                      MembershipCampaignsInv(voteHistory), EntryAncestryInv(voteHistory),
                      ClientRequest(actor, payload)
             PROVE EntryAncestryInv(nextVoteHistory)'
    BY SMT
<1>base. TypeOK /\ SendInvariant /\ EntryEdgeBase
    BY CampaignsSupplyEntryBounds, SMT DEF EntryEdgeBase
<1>next. [Next]_vars BY SMT DEF Next
<1>old. PICK family:
        /\ CertificateFamily(voteHistory, family)
        /\ CoversEntryEdges(family, HistoricalEntryEdges)
    BY SMT DEF EntryAncestryInv
<1>fresh. PICK fresh:
        /\ fresh.prefix = log'[actor]
        /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
        /\ CertificateWitness(nextVoteHistory, fresh)'
    BY ClientRequestCreatesCertificateWitness, SMT
<1>old_after. CertificateFamily(nextVoteHistory, family)'
    BY <1>base, <1>next, <1>old, CertificateFamilyNext, SMT
<1>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh.edge}
    BY <1>base, <1>fresh, ClientHistoricalEntryEdges, SMT
<1>coverage. CoversEntryEdges(family \cup {fresh}, HistoricalEntryEdges')
    BY <1>old, <1>fresh, <1>edges, SMT DEF CoversEntryEdges
<1>ancestors. \A index \in DOMAIN fresh.prefix:
        \E ancestor \in family \cup {fresh}:
            ancestor.edge = LogEntryEdge(fresh.prefix, index)
    <2> SUFFICES ASSUME NEW index \in DOMAIN fresh.prefix
                 PROVE \E ancestor \in family \cup {fresh}:
                           ancestor.edge = LogEntryEdge(fresh.prefix, index)
        BY SMT
    <2>edge. LogEntryEdge(fresh.prefix, index) \in HistoricalEntryEdges'
        BY <1>fresh, SMT DEF HistoricalEntryEdges
    <2> QED BY <1>coverage, <2>edge, SMT DEF CoversEntryEdges
<1>family_after. CertificateFamily(nextVoteHistory, family \cup {fresh})'
    BY <1>old_after, <1>fresh, <1>ancestors, ExtendCertificateFamilyAfter, SMT
<1> QED BY <1>family_after, <1>coverage, SMT DEF EntryAncestryInv

LEMMA EntryAncestryInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE /\ MembershipCampaignsInv(voteHistory) /\ AppendRequestRootTerm /\ EntryAncestryInv(voteHistory)
    /\ [Next]_vars
    => EntryAncestryInv(nextVoteHistory)'
<1> SUFFICES ASSUME MembershipCampaignsInv(voteHistory), AppendRequestRootTerm,
                      EntryAncestryInv(voteHistory), [Next]_vars
             PROVE EntryAncestryInv(nextVoteHistory)'
    BY SMT
<1>base. TypeOK /\ SendInvariant /\ EntryEdgeBase
    BY CampaignsSupplyEntryBounds, SMT DEF EntryEdgeBase
<1>client. CASE \E actor \in Server, payload \in ClientPayload:
        ClientRequest(actor, payload)
    BY <1>client, ClientRequestPreservesEntryAncestry, SMT
<1>send. CASE \E actor, peer \in Server: AppendEntries(actor, peer)
    BY <1>base, <1>send, EntryEdgeAppendSendSubset, EntryAncestrySubsetNext, SMT
<1>receive. CASE \E actor, peer \in Server, request \in messages:
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(actor, peer, request)
    BY <1>base, <1>receive, EntryEdgeAppendReceiveSubset, EntryAncestrySubsetNext, SMT
<1>other. CASE
        /\ ~(\E actor \in Server, payload \in ClientPayload:
                 ClientRequest(actor, payload))
        /\ ~(\E actor, peer \in Server: AppendEntries(actor, peer))
        /\ ~(\E actor, peer \in Server, request \in messages:
                 /\ request.mtype = AppendEntriesRequest
                 /\ HandleAppendEntriesRequest(actor, peer, request))
    BY <1>base, <1>other, EntryEdgeOtherSubset, EntryAncestrySubsetNext, SMT
<1> QED BY <1>client, <1>send, <1>receive, <1>other, SMT

LEMMA EntryAncestryInvInit ==
    Init => EntryAncestryInv({})
<1>empty. Init => HistoricalEntryEdges = {}
    BY SMT DEF Init, InitLogVars, HistoricalEntryEdges, AppendRequests
<1>family. Init => CertificateFamily({}, {})
    BY CampaignHistoryInit, FS_EmptySet, SMT DEF CertificateFamily
<1> QED BY <1>empty, <1>family, SMT DEF EntryAncestryInv, CoversEntryEdges

LEMMA MembershipEntryAncestryInvInit ==
    Init => MembershipEntryAncestryInv({})
    BY MembershipCampaignsInvInit, AppendRequestRootTermInit, EntryAncestryInvInit, SMT
    DEF MembershipEntryAncestryInv

LEMMA MembershipEntryAncestryInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE MembershipEntryAncestryInv(voteHistory) /\ [Next]_vars => MembershipEntryAncestryInv(nextVoteHistory)'
    BY MembershipCampaignsInvNext, AppendRequestRootTermNext, EntryAncestryInvNext,
       CampaignsSupplyEntryBounds, SMT DEF MembershipEntryAncestryInv

LEMMA NewAcknowledgmentReceiveOrigin ==
    ASSUME TypeOK, [Next]_vars, NEW response \in messages' \ messages,
           SuccessfulAppendResponse(response)
    PROVE \E request \in AppendRequests:
              /\ ResponseMatchesRequest(response, request)
              /\ HandleAppendEntriesRequest(response.msource, response.mdest, request)
              /\ currentTerm[response.msource] = request.mterm
              /\ state[response.msource] # Leader
              /\ AppendAnchorMatches(request, response.msource)
<1>changed. ~UNCHANGED messages BY SMT
<1>other_actions.
        /\ \A actor \in Server:
               ~(Restart(actor) \/ BecomeLeader(actor)
                 \/ AdvanceCommitIndex(actor) \/ LeaderStepDown(actor))
        /\ \A actor \in Server, payload \in ClientPayload:
               ~ClientRequest(actor, payload)
    BY <1>changed, SMT
    DEF Restart, BecomeLeader, AdvanceCommitIndex, LeaderStepDown, ClientRequest
<1>timeout. \A actor \in Server: ~Timeout(actor)
    BY MessageTypesDistinct, SMT
    DEF Timeout, RequestVoteRequests, WithMessages, SuccessfulAppendResponse
<1>append. \A actor, peer \in Server: ~AppendEntries(actor, peer)
    BY MessageTypesDistinct, SMT
    DEF AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages,
        SuccessfulAppendResponse
<1>receive. PICK request \in messages: Receive(request)
    BY <1>changed, <1>other_actions, <1>timeout, <1>append, SMT DEF Next, vars
<1>handled.
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    BY <1>receive, MessageTypesDistinct, SMT
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages, SuccessfulAppendResponse
<1>accepted.
        /\ response.msource = request.mdest
        /\ response.mdest = request.msource
        /\ ResponseMatchesRequest(response, request)
        /\ currentTerm[request.mdest] = request.mterm
        /\ state[request.mdest] # Leader
        /\ AppendAnchorMatches(request, request.mdest)
    BY <1>receive, <1>handled, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, HandleAppendEntriesRequest,
        Send, WithMessage, WithMessages, SuccessfulAppendResponse,
        ResponseMatchesRequest, AppendAnchorMatches
<1> QED BY <1>receive, <1>handled, <1>accepted, SMT DEF AppendRequests

LEMMA NewSuccessfulResponseOrigin ==
    TypeOK /\ [Next]_vars =>
        \A response \in messages' \ messages:
            SuccessfulAppendResponse(response) =>
                /\ response.msource \in Server
                /\ response.mdest \in Server
                /\ response.mterm = currentTerm[response.msource]
                /\ \E request \in messages: ResponseMatchesRequest(response, request)
    BY NewAcknowledgmentReceiveOrigin, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, AppendRequests, ResponseMatchesRequest

LEMMA SuccessfulResponseOriginInvNext ==
    TypeOK /\ SuccessfulResponseOriginInv /\ [Next]_vars
    => SuccessfulResponseOriginInv'
    BY NewSuccessfulResponseOrigin, MessagesMonotonicNext, SMT
    DEF SuccessfulResponseOriginInv

LEMMA MatchIndexEvidenceInvNext ==
    TypeOK /\ MatchIndexEvidenceInv /\ [Next]_vars => MatchIndexEvidenceInv'
<1> SUFFICES ASSUME TypeOK, MatchIndexEvidenceInv, [Next]_vars
             PROVE MatchIndexEvidenceInv' BY SMT
<1>messages. messages \subseteq messages' BY MessagesMonotonicNext, SMT
<1>stutter. CASE UNCHANGED vars
    BY <1>stutter, SMT DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, vars
<1>restart. CASE \E actor \in Server: Restart(actor)
    BY <1>restart, <1>messages, ServerStatesDistinct, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, Restart, TypeOK,
        ServerVarsTypeOK, LeaderVarsTypeOK
<1>timeout. CASE \E actor \in Server: Timeout(actor)
    BY <1>timeout, <1>messages, ServerStatesDistinct, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, Timeout, TypeOK,
        ServerVarsTypeOK, LeaderVarsTypeOK
<1>leader. CASE \E actor \in Server: BecomeLeader(actor)
    BY <1>leader, <1>messages, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, BecomeLeader, TypeOK,
        ServerVarsTypeOK, LeaderVarsTypeOK
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>client, <1>messages, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, ClientRequest
<1>commit. CASE \E actor \in Server: AdvanceCommitIndex(actor)
    BY <1>commit, <1>messages, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, AdvanceCommitIndex
<1>append. CASE \E actor, peer \in Server: AppendEntries(actor, peer)
    BY <1>append, <1>messages, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, AppendEntries
<1>stepdown. CASE \E actor \in Server: LeaderStepDown(actor)
    BY <1>stepdown, <1>messages, ServerStatesDistinct, SMT
    DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, LeaderStepDown, TypeOK,
        ServerVarsTypeOK, LeaderVarsTypeOK
<1>receive. CASE \E message \in messages: Receive(message)
    <2>message. PICK message \in messages: Receive(message) BY <1>receive, SMT
    <2>update. CASE UpdateTerm(message.mdest, message.msource, message)
        BY <2>message, <2>update, <1>messages, MessageFieldsTypeOK,
           ServerStatesDistinct, SMT
        DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, UpdateTerm,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, LeaderVarsTypeOK
    <2>vote_request. CASE /\ message.mtype = RequestVoteRequest
                         /\ HandleRequestVoteRequest(message.mdest, message.msource, message)
        BY <2>message, <2>vote_request, <1>messages, SMT
        DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, HandleRequestVoteRequest
    <2>vote_response. CASE /\ message.mtype = RequestVoteResponse
                          /\ HandleRequestVoteResponse(message.mdest, message.msource, message)
        BY <2>message, <2>vote_response, <1>messages, SMT
        DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, HandleRequestVoteResponse
    <2>append_request. CASE /\ message.mtype = AppendEntriesRequest
                           /\ HandleAppendEntriesRequest(message.mdest, message.msource, message)
        BY <2>message, <2>append_request, <1>messages, MessageFieldsTypeOK,
           ServerStatesDistinct, SMT
        DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, HandleAppendEntriesRequest,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, LeaderVarsTypeOK
    <2>append_response. CASE /\ message.mtype = AppendEntriesResponse
                            /\ HandleAppendEntriesResponse(message.mdest, message.msource, message)
        BY <2>message, <2>append_response, <1>messages, MessageFieldsTypeOK, SMTT(20)
        DEF MatchIndexEvidenceInv, SuccessfulAppendResponse, HandleAppendEntriesResponse,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, LeaderVarsTypeOK
    <2> QED BY <2>message, <2>update, <2>vote_request, <2>vote_response,
        <2>append_request, <2>append_response, SMT DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader, <1>client,
    <1>commit, <1>append, <1>stepdown, <1>receive, SMT DEF Next

LEMMA AppendRequestElectionEvidenceInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE /\ MembershipCampaignsInv(voteHistory) /\ AppendRequestElectionEvidenceInv(voteHistory) /\ [Next]_vars
    => AppendRequestElectionEvidenceInv(nextVoteHistory)'
<1> SUFFICES ASSUME MembershipCampaignsInv(voteHistory), AppendRequestElectionEvidenceInv(voteHistory),
                      [Next]_vars, NEW request \in AppendRequests'
             PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
                       RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                                                   snapshot, occurrence, support)'
    BY SMT DEF AppendRequestElectionEvidenceInv
<1>base. TypeOK /\ SendInvariant /\ EntryEdgeBase
    BY CampaignsSupplyEntryBounds, SMT DEF EntryEdgeBase
<1>old. CASE request \in messages
    <2>certificate. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                                            snapshot, occurrence, support)
        BY <1>old, SMT DEF AppendRequests, AppendRequestElectionEvidenceInv
    <2>types. request.msource \in Server /\ request.mterm \in Nat
        BY <1>old, <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
    <2> QED BY <1>base, <2>certificate, <2>types,
        RetainedElectionCertificateNext, SMT
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>types.
            /\ state[leader] = Leader
            /\ currentTerm[leader] \in Nat
            /\ request.msource = leader
            /\ request.mterm = currentTerm[leader]
        BY <1>base, <2>origin, SMT
        DEF AppendEntries, AppendEntriesMessage, TypeOK, ServerVarsTypeOK
    <2>certificate. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader],
                                           snapshot, occurrence, support)
        BY <2>types, CurrentLeaderHasElectionCertificate, SMT
    <2>captured. RetainedElectionCertificate(voteHistory, leader, currentTerm[leader],
                                            snapshot, occurrence, support)
        BY <2>types, <2>certificate, CaptureCurrentElectionCertificate, SMT
    <2> QED BY <1>base, <2>origin, <2>types, <2>certificate, <2>captured,
        RetainedElectionCertificateNext, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA ReplicationEvidenceInvInit ==
    Init => ReplicationEvidenceInv({})
    BY MembershipEntryAncestryInvInit, ServerStatesDistinct, SMT
    DEF ReplicationEvidenceInv, SuccessfulResponseOriginInv,
        MatchIndexEvidenceInv, AppendRequestElectionEvidenceInv, AppendRequests,
        Init, InitServerVars

LEMMA ReplicationEvidenceInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE ReplicationEvidenceInv(voteHistory) /\ [Next]_vars => ReplicationEvidenceInv(nextVoteHistory)'
    BY MembershipEntryAncestryInvNext, SuccessfulResponseOriginInvNext,
       MatchIndexEvidenceInvNext, AppendRequestElectionEvidenceInvNext,
       CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase

LEMMA CoveringFamilyImpliesEntryEdgeConsistency ==
    \A family:
        CoversEntryEdges(family, HistoricalEntryEdges) /\ WitnessEdgeConsistency(family)
        => EntryEdgeConsistency
    BY SMT DEF CoversEntryEdges, WitnessEdgeConsistency, EntryEdgeConsistency

LEMMA ConsistentFamilyImpliesLogMatching ==
    \A family:
        /\ EntryEdgeBase
        /\ CoversEntryEdges(family, HistoricalEntryEdges)
        /\ WitnessEdgeConsistency(family)
        => LogMatchingInv
    BY CoveringFamilyImpliesEntryEdgeConsistency,
       EntryEdgeConsistencyImpliesLogMatching, SMT

LEMMA TermsOrderedOnPrefix ==
    \A entries \in Seq(LogEntry): \A cut \in 0..Len(entries):
        TermsOrdered(entries) => TermsOrdered(SubSeq(entries, 1, cut))
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF TermsOrdered

LEMMA NewRequestPrefixEvidence ==
    ASSUME NEW voteHistory, ReplicationEvidenceInv(voteHistory), NEW leader \in Server, NEW peer \in Server,
           AppendEntries(leader, peer), NEW request,
           request = AppendEntriesMessage(leader, peer)
    PROVE RequestPrefixEvidence(request)'
<1>base.
        /\ TypeOK /\ EntryEdgeBase
        /\ LogStructureInv /\ LogTermsMonotonic
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, MembershipCampaignsInv,
        MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        EntryEdgeBase, TermOrderingInv
<1>types.
        /\ request \in Message
        /\ request.msource = leader
        /\ request.mterm = currentTerm[leader]
        /\ request.mterm \in Nat
        /\ request.mprevLogIndex \in Nat
        /\ request.mentries \in Seq(LogEntry)
        /\ log[leader] \in Seq(LogEntry)
        /\ Len(log[leader]) \in Nat
        /\ state[leader] = Leader
    BY <1>base, AppendEntriesMessageTypeOK, MessageFieldsTypeOK, LenProperties, SMT
    DEF AppendEntriesMessage, AppendEntries, TypeOK, ServerVarsTypeOK,
        LogVarsTypeOK, EntryEdgeBase
<1>endpoint.
        /\ request.mprevLogIndex + Len(request.mentries) \in 0..Len(log[leader])
        /\ request.mprevLogIndex <= request.mprevLogIndex + Len(request.mentries)
    BY <1>base, <1>types, AppendEntriesMessageIndexBound, LenProperties, SMT
    DEF AppendEntriesMessage, EntryEdgeBase, TypeOK, LeaderVarsTypeOK
<1>prefix. PICK prefix \in Seq(LogEntry):
        prefix = SubSeq(log[leader], 1, request.mprevLogIndex + Len(request.mentries))
    BY <1>types, <1>endpoint, SubSeqTypeOK, SMT
<1>shape.
        /\ Len(prefix) = request.mprevLogIndex + Len(request.mentries)
        /\ IsPrefix(prefix, log[leader])
        /\ \A index \in 1..Len(prefix): prefix[index] = log[leader][index]
    BY <1>types, <1>endpoint, <1>prefix, SubSeqProperties,
       ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1>anchor.
        /\ (request.mprevLogIndex = 0 => request.mprevLogTerm = 0)
        /\ (request.mprevLogIndex > 0 =>
               prefix[request.mprevLogIndex].term = request.mprevLogTerm)
    BY <1>base, <1>types, <1>endpoint, <1>shape, AppendSendPreviousSnapshot, SMT
    DEF AppendEntriesMessage, EntryEdgeBase, TypeOK, LeaderVarsTypeOK
<1>entries. \A offset \in DOMAIN request.mentries:
        prefix[request.mprevLogIndex + offset] = request.mentries[offset]
    BY <1>base, <1>types, <1>shape, AppendSendEntryOffsetSnapshot, SMT
    DEF AppendEntriesMessage, TypeOK, LeaderVarsTypeOK
<1>structure.
        /\ TermsOrdered(prefix)
        /\ EntryStructure(prefix, request.mterm)
    BY <1>base, <1>types, <1>endpoint, <1>prefix,
       TermsOrderedOnPrefix, EntryStructureOnSubSeq, SMT
    DEF LogStructureInv, LogTermsMonotonic, TermsOrdered
<1>owner. OwnerPrefix(request.msource, request.mterm, prefix)'
    BY <1>base, <1>types, <1>shape, SMT
    DEF OwnerPrefix, AppendEntries, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1> QED BY <1>types, <1>endpoint, <1>prefix, <1>shape,
    <1>anchor, <1>entries, <1>structure, <1>owner, SMT
    DEF RequestPrefixEvidence, RequestPrefixData

LEMMA RequestPrefixEvidenceInvNext ==
    ASSUME NEW voteHistory
    PROVE ReplicationEvidenceInv(voteHistory) /\ RequestPrefixEvidenceInv /\ [Next]_vars
    => RequestPrefixEvidenceInv'
<1> SUFFICES ASSUME ReplicationEvidenceInv(voteHistory), RequestPrefixEvidenceInv, [Next]_vars,
                      NEW request \in AppendRequests'
             PROVE RequestPrefixEvidence(request)'
    BY SMT DEF RequestPrefixEvidenceInv
<1>base. TypeOK /\ EntryEdgeBase
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>old. CASE request \in messages
    BY <1>base, <1>old, OwnerPrefixNext, SMT
    DEF RequestPrefixEvidence, RequestPrefixEvidenceInv, AppendRequests
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2> QED BY <2>origin, NewRequestPrefixEvidence, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA SuccessfulResponseHasPrefixEvidence ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), NEW response \in messages,
           SuccessfulAppendResponse(response)
    PROVE \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
              /\ ResponseMatchesRequest(response, request)
              /\ RequestPrefixData(request, prefix)
              /\ OwnerPrefix(request.msource, request.mterm, prefix)
    BY SMT DEF ReplicationPrefixInv, ReplicationEvidenceInv,
        SuccessfulResponseOriginInv, RequestPrefixEvidenceInv,
        RequestPrefixEvidence, ResponseMatchesRequest, AppendRequests

LEMMA ReplicationPrefixInvInit ==
    Init => ReplicationPrefixInv({})
    BY ReplicationEvidenceInvInit, SMT
    DEF ReplicationPrefixInv, RequestPrefixEvidenceInv, AppendRequests, Init

LEMMA ReplicationPrefixInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE ReplicationPrefixInv(voteHistory) /\ [Next]_vars => ReplicationPrefixInv(nextVoteHistory)'
    BY ReplicationEvidenceInvNext, RequestPrefixEvidenceInvNext, SMT
    DEF ReplicationPrefixInv

LEMMA AgreeSetHasRecordedSupport ==
    ASSUME TypeOK, MatchIndexEvidenceInv, NEW leader \in Server,
           state[leader] = Leader, NEW index \in Nat \ {0}
    PROVE Agree(leader, index) \subseteq
              RecordedReplicationSupport(leader, currentTerm[leader], index)
<1>config. LastConfiguration(leader) \subseteq Server
    BY ConfigurationType, SMT DEF TypeOK, LogVarsTypeOK, LastConfiguration
<1> QED BY <1>config, SMT
    DEF Agree, RecordedReplicationSupport, RecordedAcknowledgment,
        MatchIndexEvidenceInv, TypeOK, LeaderVarsTypeOK

LEMMA ReadyCurrentTermEntryHasQuorumEvidence ==
    ASSUME TypeOK, MatchIndexEvidenceInv, NEW leader \in Server,
           state[leader] = Leader, NEW index \in AgreeIndexes(leader),
           log[leader][index].term = currentTerm[leader]
    PROVE ReplicationQuorumEvidence(leader, index, Agree(leader, index))
    BY AgreeSetHasRecordedSupport, LenProperties, SMT
    DEF AgreeIndexes, ReplicationQuorumEvidence, TypeOK, LogVarsTypeOK

LEMMA ChangedCommitIndexHasQuorumEvidence ==
    ASSUME NEW voteHistory, ReplicationEvidenceInv(voteHistory), NEW leader \in Server,
           AdvanceCommitIndex(leader), commitIndex'[leader] # commitIndex[leader]
    PROVE \E support:
              ReplicationQuorumEvidence(leader, commitIndex'[leader], support)
<1>base. TypeOK /\ MatchIndexEvidenceInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>choice.
        /\ AgreeIndexes(leader) # {}
        /\ commitIndex'[leader] = Max(AgreeIndexes(leader))
        /\ log[leader][Max(AgreeIndexes(leader))].term = currentTerm[leader]
        /\ state[leader] = Leader
    BY <1>base, SMT DEF AdvanceCommitIndex, NewCommitIndex, TypeOK, LogVarsTypeOK
<1>index. commitIndex'[leader] \in AgreeIndexes(leader)
    BY <1>base, <1>choice, MaxAgreeIndexesTypeOK, SMT
<1> QED BY <1>base, <1>choice, <1>index,
    ReadyCurrentTermEntryHasQuorumEvidence, SMT

LEMMA NewPositiveVoteHasEligibleRequest ==
    TypeOK /\ [Next]_vars =>
    \A response \in messages' \ messages:
        response.mtype = RequestVoteResponse /\ response.mvoteGranted =>
            \E request \in messages:
                /\ request.msource = response.mdest
                /\ request.mdest = response.msource
                /\ request.mterm = response.mterm
                /\ VoteRequestEligible(request, response.msource)
<1> SUFFICES ASSUME TypeOK, [Next]_vars,
                      NEW response \in messages' \ messages,
                      response.mtype = RequestVoteResponse, response.mvoteGranted
             PROVE \E request \in messages:
                       /\ request.msource = response.mdest
                       /\ request.mdest = response.msource
                       /\ request.mterm = response.mterm
                       /\ VoteRequestEligible(request, response.msource)
    BY SMT
<1>request. PICK request \in messages:
        /\ request.mtype = RequestVoteRequest
        /\ request.mterm = response.mterm
        /\ request.msource = response.mdest
        /\ request.mdest = response.msource
        /\ HandleRequestVoteRequest(response.msource, response.mdest, request)
    BY NewPositiveVoteResponseReceiveOrigin, SMT
<1>types.
        /\ response.msource \in Server /\ response.mdest \in Server
        /\ request.mterm \in Nat /\ currentTerm[response.msource] \in Nat
    BY <1>request, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, ServerVarsTypeOK
<1> QED BY <1>request, <1>types, SMT
    DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages,
        VoteRequestEligible, VoteRequestFreshFor

LEMMA CampaignRequestEligibilityUsesSnapshot ==
    ASSUME TypeOK, NEW voter \in Server, NEW candidate \in Server,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW request,
           request \in CampaignRequests(candidate, term, snapshot),
           voter = request.mdest
    PROVE VoteRequestEligible(request, voter)
          <=> NewPeerVoteEligible(voter, candidate, term, snapshot)
    BY SMT DEF CampaignRequests, VoteRequestEligible, VoteRequestFreshFor,
        NewPeerVoteEligible, SnapshotFreshFor

LEMMA CurrentRecordedAcknowledgmentCoversPrefix ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), NEW leader \in Server, NEW peer \in Server,
           state[leader] = Leader, NEW target \in Seq(LogEntry),
           IsPrefix(target, log[leader]),
           RecordedAcknowledgment(peer, leader, currentTerm[leader], Len(target))
    PROVE RecordedPrefixAcknowledgment(peer, leader, currentTerm[leader], target)
<1>base. TypeOK
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        EntryEdgeBase
<1>response. PICK response \in messages:
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = peer /\ response.mdest = leader
        /\ response.mterm = currentTerm[leader] /\ response.mmatchIndex >= Len(target)
    BY SMT DEF RecordedAcknowledgment
<1>prefix. PICK request, prefix:
        /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
        /\ ResponseMatchesRequest(response, request)
        /\ RequestPrefixData(request, prefix)
        /\ OwnerPrefix(request.msource, request.mterm, prefix)
    BY <1>response, SuccessfulResponseHasPrefixEvidence, SMT
<1>compatible.
        /\ IsPrefix(prefix, log[leader])
        /\ Len(target) <= Len(prefix)
        /\ log[leader] \in Seq(LogEntry)
        /\ OwnerPrefix(leader, currentTerm[leader], prefix)
    BY <1>base, <1>response, <1>prefix, SMT
    DEF ResponseMatchesRequest, RequestPrefixData, OwnerPrefix, TypeOK, LogVarsTypeOK
<1>contained. IsPrefix(target, prefix)
    BY <1>prefix, <1>compatible, PrefixesWithBoundedLength, SMT
<1> QED BY <1>response, <1>prefix, <1>compatible, <1>contained, SMT
    DEF RecordedPrefixAcknowledgment, AppendRequests

LEMMA HistoryCommitCertificateIsRetained ==
    ASSUME NEW voteHistory, CampaignHistory(voteHistory), NEW certificate,
           HistoryCommitCertificate(voteHistory, certificate)
    PROVE RetainedCommitCertificate(voteHistory, certificate)
    BY HistoryElectionCertificateIsRetained, SMT DEF HistoryCommitCertificate, RetainedCommitCertificate

LEMMA HistoryCommitCertificateRetentionRule == HistoryCommitCertificateRetention
    BY HistoryCommitCertificateIsRetained, SMT DEF HistoryCommitCertificateRetention

LEMMA HistoryCommitCertificateIsRetainedAfter ==
    ASSUME NEW voteHistory, NEW certificate, CampaignHistory(voteHistory)',
           HistoryCommitCertificate(voteHistory, certificate)'
    PROVE RetainedCommitCertificate(voteHistory, certificate)'
<1>rule. HistoryCommitCertificateRetention'
    BY HistoryCommitCertificateRetentionRule, PTL
<1> QED BY <1>rule, SMT DEF HistoryCommitCertificateRetention

LEMMA CommitCertificateTargetProperties ==
    ASSUME NEW voteHistory
    PROVE \A certificate:
        RetainedCommitCertificate(voteHistory, certificate) =>
            /\ CommitTarget(certificate) \in Seq(LogEntry)
            /\ Len(CommitTarget(certificate)) = certificate.index
            /\ IsPrefix(CommitTarget(certificate), certificate.entries)
            /\ CommitTarget(certificate)[certificate.index].term = certificate.term
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF RetainedCommitCertificate, CommitTarget, IsPrefix

LEMMA CommitCertificateSuppliesRecordedSupport == CommitCertificateRecordedSupport
    BY CommitCertificateTargetProperties, SMT
    DEF CommitCertificateRecordedSupport, RetainedCommitCertificate, RecordedPrefixAcknowledgment,
        RecordedAcknowledgment, RecordedReplicationSupport, Quorums

LEMMA RetainedCommitCertificateNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A certificate:
        TypeOK /\ SendInvariant /\ [Next]_vars /\ RetainedCommitCertificate(voteHistory, certificate)
        => RetainedCommitCertificate(nextVoteHistory, certificate)'
BY RetainedElectionCertificateNext, OwnerPrefixNext,
    MessagesMonotonicNext, CommitCertificateTargetProperties,
    CampaignHistoryContextMonotone, LocalAppendOriginIsMonotone, SMT
DEF RetainedCommitCertificate, RecordedPrefixAcknowledgment, Quorums

LEMMA ChangedCommitIndexCapturesCertificate ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), NEW leader \in Server,
           AdvanceCommitIndex(leader), commitIndex'[leader] # commitIndex[leader]
    PROVE \E certificate:
              /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
              /\ certificate.leader = leader
              /\ certificate.term = currentTerm[leader]
              /\ certificate.entries = log[leader]
              /\ certificate.index = commitIndex'[leader]
<1>base.
        /\ TypeOK /\ SendInvariant /\ ReplicationEvidenceInv(voteHistory)
        /\ MembershipCampaignsInv(voteHistory) /\ LogStructureInv /\ LogTermsMonotonic
        /\ state[leader] = Leader
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, TermOrderingInv, AdvanceCommitIndex, EntryEdgeBase
<1>next. [Next]_vars BY SMT DEF Next
<1>term. PICK term \in Nat: term = currentTerm[leader]
    BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK
<1>entries. PICK entries \in Seq(LogEntry): entries = log[leader]
    BY <1>base, SMT DEF TypeOK, LogVarsTypeOK
<1>index. PICK index \in 1..Len(entries): index = commitIndex'[leader]
    BY <1>base, <1>entries, ChangedCommitIndexHasQuorumEvidence,
       LenProperties, SMT DEF ReplicationQuorumEvidence, TypeOK, LogVarsTypeOK
<1>election. PICK snapshot, electionOccurrence, election:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, term, snapshot, electionOccurrence, election)
    BY <1>base, <1>term, CurrentLeaderHasElectionCertificate, SMT
<1>replication. PICK replication:
        ReplicationQuorumEvidence(leader, index, replication)
    BY <1>base, <1>index, ChangedCommitIndexHasQuorumEvidence, SMT
<1>target.
        /\ SubSeq(entries, 1, index) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, 1, index)) = index
        /\ IsPrefix(SubSeq(entries, 1, index), log[leader])
    BY <1>entries, <1>index, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1>acks. \A peer \in replication \ {leader}:
        RecordedPrefixAcknowledgment(peer, leader, term, SubSeq(entries, 1, index))
    BY <1>base, <1>term, <1>replication, <1>target,
       CurrentRecordedAcknowledgmentCoversPrefix, SMT
    DEF ReplicationQuorumEvidence, RecordedReplicationSupport
<1>configuration. PICK configuration:
        configuration = LatestConfigurationOccurrence(entries)
    BY SMT
<1>members.
        /\ configuration.members = LastConfiguration(leader)
        /\ configuration.members \subseteq Server
        /\ configuration.members # {}
    BY <1>entries, <1>configuration, ConfigurationType, SMT
    DEF LatestConfigurationOccurrence, LastConfiguration
<1>snapshot_bound. Len(snapshot) < index
    BY <1>base, <1>election, <1>entries, <1>index, <1>replication, <1>term,
       OrderedPreTermIndexes, PreTermIndexProperties, LenProperties, SMT
    DEF CurrentElectionCertificate, CampaignPrefix, ReplicationQuorumEvidence,
        PreTermIndexes, TermsOrdered, LogTermsMonotonic
<1>owner. OwnerPrefix(leader, term, entries)
    BY <1>base, <1>term, <1>entries, WholeSequencePrefix, SMT DEF OwnerPrefix, IsPrefix
<1>snapshot_prefix. IsPrefix(snapshot, entries)
    BY <1>base, <1>term, <1>entries, <1>election,
       CampaignPrefixProperties, PreTermIndexProperties, SMT
    DEF CurrentElectionCertificate, IsPrefix, LogTermsMonotonic, TermsOrdered
<1> DEFINE certificate ==
        [leader |-> leader, term |-> term, entries |-> entries, index |-> index,
         snapshot |-> snapshot, electionOccurrence |-> electionOccurrence,
         election |-> election, configuration |-> configuration, replication |-> replication]
<1>origin. LocalAppendOrigin(voteHistory, leader, term, CommitTarget(certificate))
    <2>whole. LocalAppendOrigin(voteHistory, leader, term, entries)
        BY <1>base, <1>term, <1>entries, <1>index, <1>replication, SMT
        DEF MembershipCampaignsInv, MembershipVotesInv, CampaignHistory, LocalAppendCoverage,
            ReplicationQuorumEvidence
    <2> QED BY <2>whole, <1>entries, <1>target, SequencePrefixTransitive, SMT
        DEF CommitTarget, certificate, LocalAppendOrigin
<1>valid. RetainedCommitCertificate(voteHistory, certificate)
    BY <1>base, <1>term, <1>entries, <1>index, <1>election, <1>replication,
       <1>target, <1>acks, <1>configuration, <1>members, <1>snapshot_bound,
       <1>owner, <1>snapshot_prefix, <1>origin, CaptureCurrentElectionCertificate, SMT
    DEF RetainedCommitCertificate, CommitTarget, CurrentElectionCertificate,
        ReplicationQuorumEvidence, LogStructureInv, LogTermsMonotonic, TermsOrdered,
        certificate
<1>after. RetainedCommitCertificate(nextVoteHistory, certificate)'
    BY <1>base, <1>next, <1>valid, RetainedCommitCertificateNext, SMT
<1> QED BY <1>after, <1>term, <1>entries, <1>index, SMT DEF certificate

LEMMA ClientRequestKeepsSelectedCampaignHistory ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           TypeOK, NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
    PROVE CampaignView(nextVoteHistory) = CampaignView(voteHistory)
    BY UnchangedTermsKeepCampaignHistory, SMT DEF ClientRequest

\* A fresh append needs no peer acknowledgment when the new membership is
\* exactly the appender. This covers data appends and removal down to one.
LEMMA SingletonAppendCreatesHistoryCommitCertificate ==
    ASSUME MembershipStructureInv, TermOrderingInv, GrantedVotesRecorded,
           NEW history, NEW larger, CampaignHistoryContextStep(history, larger), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), ConfigOf(log'[actor]) = {actor}
    PROVE \E certificate:
              /\ HistoryCommitCertificate(larger, certificate)'
              /\ certificate.leader = actor /\ certificate.term = currentTerm[actor]
              /\ certificate.entries = log'[actor] /\ certificate.index = Len(log'[actor])
              /\ certificate.replication = {actor}
<1>base. TypeOK /\ SendInvariant /\ LogStructureInv /\ LogTermsMonotonic /\ CampaignHistory(history)
    BY SMT DEF MembershipStructureInv, ReplicationBoundsInv, TermOrderingInv, CampaignHistoryContextStep
<1>next. [Next]_vars BY SMT DEF Next
<1>election. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ HistoryElectionCertificate(history, actor, currentTerm[actor], snapshot, occurrence, support)
        /\ snapshot = CampaignPrefix(log[actor], currentTerm[actor])
    BY <1>base, CurrentLeaderHasHistoryElectionCertificate, SMT DEF ClientRequest
<1>term. PICK term \in Nat: term = currentTerm[actor]
    BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK
<1>entries. PICK entries \in Seq(LogEntry): entries = log'[actor]
    BY <1>base, ClientRequestLogTypeOK, SMT DEF LogVarsTypeOK
<1>append. Len(entries) = Len(log[actor]) + 1 /\ entries[Len(entries)].term = term
    BY <1>base, <1>term, <1>entries, ClientRequestAppendsCurrentTerm, AppendProperties, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK
<1>snapshot. IsPrefix(snapshot, entries) /\ Len(snapshot) < Len(entries)
    BY <1>base, <1>election, <1>entries, <1>append, CampaignPrefixProperties,
       PreTermIndexProperties, AppendPreservesSequencePrefix, ClientRequestAppendsCurrentTerm,
       WholeSequencePrefix, LenProperties, SMT
    DEF IsPrefix, TypeOK, LogVarsTypeOK, ServerVarsTypeOK, LogTermsMonotonic, TermsOrdered
<1>old_election. HistoryElectionCertificate(history, actor, term, snapshot, occurrence, support)
    BY <1>election, <1>term, SMT
<1>subset. history \subseteq larger BY CampaignHistoryContextMonotone, SMT
<1>retained. HistoryElectionCertificate(larger, actor, term, snapshot, occurrence, support)'
    BY <1>base, <1>next, <1>old_election, <1>subset, HistoryElectionCertificateRetained, SMT
    DEF HistoryElectionCertificate
<1>structure. TermsOrdered(entries) /\ EntryStructure(entries, term)
    BY <1>base, <1>term, <1>entries, ClientRequestPreservesLogTermsMonotonic,
       ClientRequestPreservesLogStructure, SMT
    DEF OrderingBase, LogTermBoundInv, LogStructureInv, EntryStructure, LogTermsMonotonic,
        TermsOrdered, ClientRequest
<1>owner. OwnerPrefix(actor, term, entries)'
    BY <1>base, <1>term, <1>entries, WholeSequencePrefix, LenProperties, SMT
    DEF OwnerPrefix, ClientRequest, TypeOK, ServerVarsTypeOK, IsPrefix
<1>quorum. {actor} \in Quorums({actor})
    BY FS_Singleton, NonemptyFiniteSetIsQuorum, SMT
<1> DEFINE certificate ==
        [leader |-> actor, term |-> term, entries |-> entries, index |-> Len(entries),
         snapshot |-> snapshot, electionOccurrence |-> occurrence, election |-> support,
         configuration |-> LatestConfigurationOccurrence(entries), replication |-> {actor}]
<1>data. actor \in Server /\ term \in Nat /\ entries \in Seq(LogEntry)
          /\ Len(entries) > 0 /\ Len(entries) \in DOMAIN entries /\ entries[Len(entries)].term = term
          /\ snapshot \in Seq(LogEntry) /\ IsPrefix(snapshot, entries) /\ Len(snapshot) < Len(entries)
    BY <1>base, <1>term, <1>entries, <1>append, <1>election, <1>snapshot, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK
<1>configuration. LatestConfigurationOccurrence(entries).members = {actor}
          /\ LatestConfigurationOccurrence(entries).members \subseteq Server
          /\ LatestConfigurationOccurrence(entries).members # {}
          /\ {actor} \in Quorums(LatestConfigurationOccurrence(entries).members)
    BY <1>entries, <1>quorum, SMT DEF LatestConfigurationOccurrence
<1>origin. LocalAppendOrigin(larger, actor, term, CommitTarget(certificate))
    BY <1>base, <1>term, <1>entries, <1>data, ClientAppendHasRecordedOrigin, WholeSequencePrefix, LenProperties, SMT
    DEF CommitTarget, certificate, IsPrefix, CampaignHistoryContextStep
<1>valid. HistoryCommitCertificate(larger, certificate)'
    BY <1>data, <1>configuration, <1>retained, <1>structure, <1>owner, <1>origin, SMT
    DEF HistoryCommitCertificate, certificate
<1> QED BY <1>valid, <1>term, <1>entries, SMT DEF certificate

LEMMA SingletonAppendCreatesRetainedCommitCertificate ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           MembershipCampaignsInv(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), ConfigOf(log'[actor]) = {actor}
    PROVE \E certificate:
              /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
              /\ certificate.leader = actor /\ certificate.term = currentTerm[actor]
              /\ certificate.entries = log'[actor] /\ certificate.index = Len(log'[actor])
              /\ certificate.replication = {actor}
<1>base. MembershipStructureInv /\ TermOrderingInv /\ GrantedVotesRecorded /\ CampaignHistory(voteHistory) /\ TypeOK
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        ActiveVotesInv, GrantedVotesRecorded
<1>growing. voteHistory \subseteq nextVoteHistory
    BY CampaignHistoryContextMonotone, SMT
<1>certificate. PICK certificate:
        /\ HistoryCommitCertificate(nextVoteHistory, certificate)'
        /\ certificate.leader = actor /\ certificate.term = currentTerm[actor]
        /\ certificate.entries = log'[actor] /\ certificate.index = Len(log'[actor])
        /\ certificate.replication = {actor}
    BY <1>base, SingletonAppendCreatesHistoryCommitCertificate, SMT
<1>retained. RetainedCommitCertificate(nextVoteHistory, certificate)'
    BY <1>growing, <1>certificate, HistoryCommitCertificateIsRetainedAfter, SMT
    DEF CampaignHistoryContextStep
<1> QED BY <1>certificate, <1>retained, SMT

LEMMA CommitCertificateFamilyNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, SendInvariant, [Next]_vars, NEW family,
           CommitCertificateFamily(voteHistory, family)
    PROVE CommitCertificateFamily(nextVoteHistory, family)'
    BY RetainedCommitCertificateNext, SMT DEF CommitCertificateFamily, CampaignHistoryContextStep

LEMMA CommitCertificateFamilyTypes ==
    ASSUME NEW voteHistory
    PROVE \A family: CommitCertificateFamily(voteHistory, family) =>
        \A certificate \in family:
            certificate.index \in Nat /\ certificate.term \in Nat
    BY LenProperties, SMT DEF CommitCertificateFamily, RetainedCommitCertificate

LEMMA AppendEntriesAdvertisesExistingCommit ==
    ASSUME TypeOK, NEW leader \in Server, NEW peer \in Server,
           NEW request, request = AppendEntriesMessage(leader, peer)
    PROVE /\ request.mcommitIndex \in Nat
          /\ request.mcommitIndex <= commitIndex[leader]
          /\ request.mterm = currentTerm[leader]
          /\ request.msource = leader
    BY MinTypeOK, LenProperties, SMT
    DEF AppendEntriesMessage, AppendEntriesLastEntry, TypeOK,
        LogVarsTypeOK, LeaderVarsTypeOK

LEMMA AdvertisedCommitEvidenceNext ==
    ASSUME NEW voteHistory, TypeOK, NextIndexBound, [Next]_vars, NEW family, CommitCertificateFamily(voteHistory, family),
           LocalCommitEvidence(family), AdvertisedCommitEvidence(family)
    PROVE AdvertisedCommitEvidence(family)'
<1> SUFFICES ASSUME NEW request \in AppendRequests', request.mcommitIndex > 0
             PROVE \E certificate \in family:
                       /\ request.mcommitIndex <= certificate.index
                       /\ certificate.term <= request.mterm
    BY SMT DEF AdvertisedCommitEvidence
<1>old. CASE request \in messages
    BY <1>old, SMT DEF AppendRequests, AdvertisedCommitEvidence
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests, EntryEdgeBase
    <2>bounds.
            /\ request.mcommitIndex \in Nat
            /\ request.mcommitIndex <= commitIndex[leader]
            /\ request.mterm = currentTerm[leader]
            /\ commitIndex[leader] \in Nat
        BY <2>origin, AppendEntriesAdvertisesExistingCommit, SMT
        DEF TypeOK, LogVarsTypeOK
    <2>certificate. PICK certificate \in family:
            /\ commitIndex[leader] <= certificate.index
            /\ certificate.term <= currentTerm[leader]
        BY <2>origin, <2>bounds, SMT DEF LocalCommitEvidence
    <2> QED BY <2>bounds, <2>certificate, CommitCertificateFamilyTypes, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA NonLeaderCommitChangeOrigin ==
    ASSUME TypeOK, [Next]_vars, NEW server \in Server,
           commitIndex'[server] > 0, commitIndex'[server] # commitIndex[server],
           ~(\E leader \in Server:
                 AdvanceCommitIndex(leader) /\ commitIndex'[leader] # commitIndex[leader])
    PROVE \E request \in AppendRequests:
              /\ request.mdest = server
              /\ request.mterm = currentTerm[server]
              /\ commitIndex'[server] = request.mcommitIndex
<1>changed. ~UNCHANGED commitIndex BY SMT
<1>restart. \A actor \in Server: ~Restart(actor)
    BY SMT DEF Restart, TypeOK, LogVarsTypeOK
<1>advance. \A actor \in Server: ~AdvanceCommitIndex(actor)
    BY SMT DEF AdvanceCommitIndex, TypeOK, LogVarsTypeOK
<1>other_actions.
        /\ \A actor \in Server:
               ~(Timeout(actor) \/ BecomeLeader(actor) \/ LeaderStepDown(actor))
        /\ \A actor \in Server, payload \in ClientPayload:
               ~ClientRequest(actor, payload)
        /\ \A actor, peer \in Server: ~AppendEntries(actor, peer)
    BY <1>changed, SMT
    DEF Timeout, BecomeLeader, LeaderStepDown, ClientRequest, AppendEntries
<1>receive. PICK request \in messages: Receive(request)
    BY <1>changed, <1>restart, <1>advance, <1>other_actions, SMT DEF Next, vars
<1>handled.
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    BY <1>receive, <1>changed, SMT
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse
<1>types.
        /\ request.mdest \in Server /\ request.msource \in Server
        /\ request.mterm \in Nat /\ request.mcommitIndex \in Nat
        /\ currentTerm[server] \in Nat /\ commitIndex[server] \in Nat
    BY <1>receive, <1>handled, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>fields.
        /\ request.mdest = server
        /\ request.mterm = currentTerm[server]
        /\ commitIndex'[server] = request.mcommitIndex
    BY <1>handled, <1>types, SMT
    DEF HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
<1> QED BY <1>receive, <1>handled, <1>fields, SMT DEF AppendRequests

LEMMA LocalCommitEvidenceWithoutLeaderAdvance ==
    ASSUME NEW voteHistory, TypeOK, TypeOK', [Next]_vars, NEW family, CommitCertificateFamily(voteHistory, family),
           LocalCommitEvidence(family), AdvertisedCommitEvidence(family),
           ~(\E leader \in Server:
                 AdvanceCommitIndex(leader) /\ commitIndex'[leader] # commitIndex[leader])
    PROVE LocalCommitEvidence(family)'
<1>terms. \A server \in Server: currentTerm[server] <= currentTerm'[server]
    BY CurrentTermsMonotonicNext, SMT
<1>types.
        /\ \A server \in Server:
               currentTerm[server] \in Nat /\ currentTerm'[server] \in Nat
        /\ \A certificate \in family: certificate.term \in Nat
    BY CommitCertificateFamilyTypes, SMT DEF TypeOK, ServerVarsTypeOK
<1> SUFFICES ASSUME NEW server \in Server, commitIndex'[server] > 0
             PROVE \E certificate \in family:
                       /\ commitIndex'[server] <= certificate.index
                       /\ certificate.term <= currentTerm'[server]
    BY SMT DEF LocalCommitEvidence
<1>same. CASE commitIndex'[server] = commitIndex[server]
    BY <1>same, <1>terms, <1>types, SMT DEF LocalCommitEvidence
<1>changed. CASE commitIndex'[server] # commitIndex[server]
    <2>origin. PICK request \in AppendRequests:
            /\ request.mdest = server
            /\ request.mterm = currentTerm[server]
            /\ commitIndex'[server] = request.mcommitIndex
        BY <1>changed, NonLeaderCommitChangeOrigin, SMT
    <2> QED BY <2>origin, <1>terms, <1>types, SMT DEF AdvertisedCommitEvidence
<1> QED BY <1>same, <1>changed, SMT

LEMMA ConfigurationOccurrenceOnContainingPrefix ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry),
           IsPrefix(prefix, entries), LastConfigChangeIndex(entries) <= Len(prefix)
    PROVE LatestConfigurationOccurrence(prefix) = LatestConfigurationOccurrence(entries)
<1>bounds.
        /\ Len(prefix) \in Nat
        /\ Len(prefix) <= Len(entries)
        /\ LastConfigChangeIndex(entries) \in 0..Len(prefix)
        /\ ConfigChangeIndexes(entries) \subseteq 1..Len(prefix)
    BY ConfigurationIndexProperties, LenProperties, SMT DEF IsPrefix
<1>cells. \A index \in 1..Len(prefix): prefix[index] = entries[index]
    BY PrefixEntryEqual, SMT
<1>indexes. ConfigChangeIndexes(prefix) = ConfigChangeIndexes(entries)
    BY <1>bounds, <1>cells, ConfigurationIndexProperties, LenProperties, SMT
    DEF ConfigChangeIndexes
<1>last. LastConfigChangeIndex(prefix) = LastConfigChangeIndex(entries)
    BY <1>indexes, SMT DEF LastConfigChangeIndex
<1>segment. SubSeq(prefix, 1, LastConfigChangeIndex(entries)) =
               SubSeq(entries, 1, LastConfigChangeIndex(entries))
    BY <1>bounds, PrefixContainsInitialSegment, SMT
<1>members. ConfigOf(prefix) = ConfigOf(entries)
    BY <1>bounds, <1>last, PrefixEntryEqual, SMT DEF ConfigOf
<1> QED BY <1>last, <1>segment, <1>members, SMT DEF LatestConfigurationOccurrence

LEMMA ProtectedCurrentTermCommitHasCurrentCertificateTerm ==
    ASSUME NEW voteHistory, TypeOK, NEW leader \in Server, NEW certificate,
           RetainedCommitCertificate(voteHistory, certificate),
           certificate.term <= currentTerm[leader],
           commitIndex[leader] <= certificate.index,
           IsPrefix(CommitTarget(certificate), log[leader]),
           CommittedInCurrentTerm(leader)
    PROVE certificate.term = currentTerm[leader]
<1>types.
        /\ log[leader] \in Seq(LogEntry)
        /\ currentTerm[leader] \in Nat
        /\ commitIndex[leader] \in Nat
        /\ commitIndex[leader] \in 1..Len(log[leader])
        /\ certificate.entries \in Seq(LogEntry)
        /\ certificate.term \in Nat
    BY LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK, ServerVarsTypeOK, RetainedCommitCertificate,
        CommittedInCurrentTerm
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ Len(CommitTarget(certificate)) = certificate.index
        /\ IsPrefix(CommitTarget(certificate), certificate.entries)
        /\ commitIndex[leader] \in 1..certificate.index
    BY <1>types, CommitCertificateTargetProperties, SMT
<1>entry.
        /\ certificate.entries[commitIndex[leader]] = log[leader][commitIndex[leader]]
        /\ commitIndex[leader] \in DOMAIN certificate.entries
    BY <1>types, <1>target, PrefixEntryEqual, LenProperties, SMT
    DEF RetainedCommitCertificate
<1>bound. currentTerm[leader] <= certificate.term
    BY <1>types, <1>entry, SMT
    DEF RetainedCommitCertificate, EntryStructure, CommittedInCurrentTerm
<1> QED BY <1>types, <1>bound, SMT

LEMMA CanReconfigureHasCurrentBarrierCertificate ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), NEW family, CommitCertificateFamily(voteHistory, family),
           LocalCommitEvidence(family), CommitLeaderProtection(family),
           CommitElectionIntersections(voteHistory, family), NEW leader \in Server,
           NEW members \in SUBSET Server, CanReconfigure(leader, members)
    PROVE \E certificate \in family: CurrentBarrierCertificate(voteHistory, leader, certificate)
<1>base. TypeOK /\ VoteRecordInv(voteHistory) /\ MembershipCampaignsInv(voteHistory)
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, EntryEdgeBase
<1>barrier.
        /\ state[leader] = Leader
        /\ CommittedInCurrentTerm(leader)
        /\ LastConfigChangeIndex(log[leader]) <= commitIndex[leader]
        /\ commitIndex[leader] > 0
        /\ commitIndex[leader] \in Nat
        /\ currentTerm[leader] \in Nat
        /\ log[leader] \in Seq(LogEntry)
    BY <1>base, LenProperties, SMT
    DEF CanReconfigure, CommittedInCurrentTerm, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>certificate. PICK certificate \in family:
        /\ RetainedCommitCertificate(voteHistory, certificate)
        /\ commitIndex[leader] <= certificate.index
        /\ certificate.term <= currentTerm[leader]
        /\ IsPrefix(CommitTarget(certificate), log[leader])
    BY <1>barrier, SMT
    DEF CommitCertificateFamily, LocalCommitEvidence, CommitLeaderProtection
<1>same_term. certificate.term = currentTerm[leader]
    BY <1>base, <1>barrier, <1>certificate,
       ProtectedCurrentTermCommitHasCurrentCertificateTerm, SMT
<1>election. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
    BY <1>base, <1>barrier, CurrentLeaderHasElectionCertificate, SMT
<1>votes.
        /\ VoteSupport(voteHistory, certificate.leader, currentTerm[leader], certificate.election)
        /\ VoteSupport(voteHistory, leader, currentTerm[leader], support)
        /\ certificate.election \cap support # {}
        /\ certificate.leader \in Server
    BY <1>certificate, <1>same_term, <1>election, SMT
    DEF RetainedCommitCertificate, RetainedElectionCertificate,
        CurrentElectionCertificate, CommitElectionIntersections
<1>owner. certificate.leader = leader
    BY <1>base, <1>barrier, <1>votes, IntersectingVoteSupportsUnique, SMT
<1>full_prefix.
        /\ certificate.entries \in Seq(LogEntry)
        /\ IsPrefix(certificate.entries, log[leader])
        /\ certificate.index \in 1..Len(certificate.entries)
        /\ commitIndex[leader] \in 1..certificate.index
        /\ LastConfigChangeIndex(log[leader]) <= Len(certificate.entries)
    BY <1>barrier, <1>certificate, <1>same_term, <1>owner,
       ConfigurationIndexProperties, LenProperties, SMT
    DEF RetainedCommitCertificate, OwnerPrefix
<1>configuration.
        certificate.configuration = LatestConfigurationOccurrence(log[leader])
    BY <1>barrier, <1>certificate, <1>full_prefix,
       ConfigurationOccurrenceOnContainingPrefix, SMT DEF RetainedCommitCertificate
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ Len(CommitTarget(certificate)) = certificate.index
        /\ IsPrefix(CommitTarget(certificate), log[leader])
        /\ LastConfigChangeIndex(log[leader]) \in 0..certificate.index
        /\ certificate.configuration.index <= certificate.index
    BY <1>certificate, <1>barrier, <1>full_prefix, <1>configuration,
       CommitCertificateTargetProperties, ConfigurationIndexProperties, SMT
    DEF LatestConfigurationOccurrence
<1>covered.
        /\ IsPrefix(certificate.configuration.prefix, CommitTarget(certificate))
        /\ IsPrefix(Committed(leader), CommitTarget(certificate))
    BY <1>barrier, <1>full_prefix, <1>configuration, <1>target,
       PrefixContainsInitialSegment, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF LatestConfigurationOccurrence, Committed, IsPrefix
<1> QED BY <1>certificate, <1>same_term, <1>owner, <1>full_prefix,
    <1>configuration, <1>target, <1>covered, SMT DEF CurrentBarrierCertificate

LEMMA ConfigurationAppendHasEarlierCertifiedBarrier ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, SendInvariant, NEW leader \in Server,
           NEW payload \in ClientPayload, payload.members # Nil,
           NEW certificate, CurrentBarrierCertificate(voteHistory, leader, certificate),
           ClientRequest(leader, payload)
    PROVE /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
          /\ IsPrefix(CommitTarget(certificate), log'[leader])
          /\ certificate.index < LatestConfigurationOccurrence(log'[leader]).index
          /\ LatestConfigurationOccurrence(log'[leader]).index = Len(log[leader]) + 1
          /\ LatestConfigurationOccurrence(log'[leader]).members = payload.members
          /\ SingleChange(certificate.configuration.members, payload.members)
          /\ leader \in payload.members
<1>types.
        /\ log[leader] \in Seq(LogEntry)
        /\ Len(log[leader]) \in Nat
        /\ currentTerm[leader] \in Nat
    BY LenProperties, SMT DEF TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>entry. PICK entry \in LogEntry:
        /\ log'[leader] = Append(log[leader], entry)
        /\ entry.members # Nil
        /\ entry.members = payload.members
    BY ClientRequestAppendsCurrentTerm, SMT
<1>last. LastConfigChangeIndex(log'[leader]) = Len(log[leader]) + 1
    BY <1>types, <1>entry, ConfigurationIndexesOnAppend,
       ConfigurationIndexProperties, MaxOrZeroAddingLastIndex, SMT
    DEF LastConfigChangeIndex
<1>members. ConfigOf(log'[leader]) = payload.members
    BY <1>types, <1>entry, ConfigurationOnAppend, SMT
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ IsPrefix(CommitTarget(certificate), log[leader])
        /\ certificate.index <= Len(log[leader])
        /\ certificate.index \in Nat
    BY <1>types, CommitCertificateTargetProperties, LenProperties, SMT
    DEF CurrentBarrierCertificate, RetainedCommitCertificate, IsPrefix
<1>prefix. IsPrefix(CommitTarget(certificate), log'[leader])
    BY <1>types, <1>entry, <1>target, PrefixOnAppend, SMT
<1>retained. RetainedCommitCertificate(nextVoteHistory, certificate)'
    BY RetainedCommitCertificateNext, SMT DEF CurrentBarrierCertificate, Next
<1>change.
        /\ SingleChange(certificate.configuration.members, payload.members)
        /\ leader \in payload.members
    BY SMT DEF CurrentBarrierCertificate, LatestConfigurationOccurrence,
        LastConfiguration, ClientRequest, CanReconfigure
<1> QED BY <1>types, <1>last, <1>members, <1>target,
    <1>prefix, <1>retained, <1>change, SMT DEF LatestConfigurationOccurrence

LEMMA PrefixEntryEdgesEqual ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry),
           IsPrefix(prefix, entries), NEW index \in DOMAIN prefix
    PROVE LogEntryEdge(prefix, index) = LogEntryEdge(entries, index)
    BY PrefixEntryEqual, LenProperties, SMT DEF LogEntryEdge

LEMMA CurrentLogPrefixCovered ==
    ASSUME NEW family, CoversEntryEdges(family, HistoricalEntryEdges),
           NEW server \in Server, NEW prefix \in Seq(LogEntry),
           log[server] \in Seq(LogEntry), IsPrefix(prefix, log[server])
    PROVE CoveredPrefix(family, prefix)
<1> SUFFICES ASSUME NEW index \in DOMAIN prefix
             PROVE \E witness \in family: witness.edge = LogEntryEdge(prefix, index)
    BY SMT DEF CoveredPrefix
<1>edge. LogEntryEdge(prefix, index) = LogEntryEdge(log[server], index)
    BY PrefixEntryEdgesEqual, SMT
<1>index. index \in DOMAIN log[server]
    BY LenProperties, SMT DEF IsPrefix
<1>member. LogEntryEdge(log[server], index) \in HistoricalEntryEdges
    BY <1>index, SMT DEF HistoricalEntryEdges, LogEntryEdge
<1> QED BY <1>edge, <1>member, SMT DEF CoversEntryEdges

LEMMA CoveredPrefixFamilyExtension ==
    \A family, larger, prefix:
        CoveredPrefix(family, prefix) /\ family \subseteq larger
        => CoveredPrefix(larger, prefix)
    BY SMT DEF CoveredPrefix

LEMMA RequestCampaignBoundaryRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, SendInvariant, [Next]_vars, NEW request, NEW prefix,
           RequestCampaignBoundary(voteHistory, request, prefix)
    PROVE RequestCampaignBoundary(nextVoteHistory, request, prefix)'
    BY RetainedElectionCertificateNext, SMT DEF RequestCampaignBoundary

LEMMA AncestralRequestPrefixRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, SendInvariant, [Next]_vars, NEW family, NEW request,
           AncestralRequestPrefix(voteHistory, family, request)
    PROVE AncestralRequestPrefix(nextVoteHistory, family, request)'
    BY OwnerPrefixNext, RequestCampaignBoundaryRetained, SMT DEF AncestralRequestPrefix

LEMMA NewAppendRequestHasAncestralPrefix ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationEvidenceInv(voteHistory), NEW family,
           CoversEntryEdges(family, HistoricalEntryEdges),
           NEW leader \in Server, NEW peer \in Server,
           AppendEntries(leader, peer), NEW request,
           request = AppendEntriesMessage(leader, peer)
    PROVE AncestralRequestPrefix(nextVoteHistory, family, request)'
<1>base.
        /\ TypeOK /\ EntryEdgeBase /\ SendInvariant /\ MembershipCampaignsInv(voteHistory)
        /\ TermsOrdered(log[leader])
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase,
        MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>prefix. PICK prefix \in Seq(LogEntry):
        /\ RequestPrefixData(request, prefix)
        /\ OwnerPrefix(request.msource, request.mterm, prefix)'
    BY NewRequestPrefixEvidence, SMT DEF RequestPrefixEvidence
<1>source.
        /\ request.msource = leader /\ request.mterm = currentTerm[leader]
        /\ request.mterm \in Nat
        /\ log[leader] \in Seq(LogEntry)
        /\ IsPrefix(prefix, log[leader])
    BY <1>base, <1>prefix, SMT
    DEF AppendEntriesMessage, AppendEntries, OwnerPrefix,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>covered. CoveredPrefix(family, prefix)
    BY <1>source, CurrentLogPrefixCovered, SMT
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, request.mterm, snapshot, occurrence, support)
    BY <1>base, <1>source, CurrentLeaderHasElectionCertificate, SMT DEF AppendEntries
<1>cut. Len(snapshot) = CampaignPrefixIndex(log[leader], request.mterm)
    BY <1>base, <1>source, <1>campaign, CampaignPrefixProperties, SMT
    DEF CurrentElectionCertificate
<1>snapshot_prefix. IsPrefix(snapshot, log[leader])
    BY <1>base, <1>source, <1>campaign, CampaignPrefixProperties,
       PreTermIndexProperties, WholeSequencePrefix, LenProperties, SMT
    DEF CurrentElectionCertificate, CampaignPrefix, IsPrefix
<1>comparable. IsPrefix(snapshot, prefix) \/ IsPrefix(prefix, snapshot)
    BY <1>source, <1>campaign, <1>snapshot_prefix, PrefixesWithBoundedLength
<1>boundary. \A index \in DOMAIN prefix:
        prefix[index].term < request.mterm => index <= Len(snapshot)
    <2> SUFFICES ASSUME NEW index \in DOMAIN prefix, prefix[index].term < request.mterm
                 PROVE index <= Len(snapshot)
        BY SMT
    <2>entry. index \in DOMAIN log[leader] /\ prefix[index] = log[leader][index]
        BY <1>source, PrefixEntryEqual, LenProperties, SMT DEF IsPrefix
    <2>old. index \in PreTermIndexes(log[leader], request.mterm)
        BY <2>entry, SMT DEF PreTermIndexes
    <2> QED BY <1>source, <1>cut, <2>old, PreTermIndexProperties, SMT
<1>captured. RetainedElectionCertificate(voteHistory, leader, request.mterm, snapshot, occurrence, support)
    BY <1>source, <1>campaign, CaptureCurrentElectionCertificate, SMT
<1>next. [Next]_vars BY SMT DEF Next
<1>retained. RetainedElectionCertificate(nextVoteHistory, leader, request.mterm, snapshot, occurrence, support)'
    BY <1>base, <1>source, <1>campaign, <1>captured, <1>next,
       RetainedElectionCertificateNext, SMT
<1>campaign_after. RequestCampaignBoundary(nextVoteHistory, request, prefix)'
    BY <1>source, <1>campaign, <1>comparable, <1>boundary, <1>retained, SMT DEF RequestCampaignBoundary
<1>small. Len(request.mentries) <= 1
    <2>shape.
            /\ AppendEntriesEntries(leader, peer) \in Seq(LogEntry)
            /\ Len(AppendEntriesEntries(leader, peer)) \in Nat
            /\ \A offset \in DOMAIN AppendEntriesEntries(leader, peer): offset = 1
        BY <1>base, AppendSendEntryOffsetSnapshot, AppendEntriesEntriesTypeOK,
           LenProperties, SMT
    <2>last. Len(AppendEntriesEntries(leader, peer)) > 0 =>
            Len(AppendEntriesEntries(leader, peer)) \in DOMAIN AppendEntriesEntries(leader, peer)
        BY <2>shape, LenProperties, SMT
    <2> QED BY <2>shape, <2>last, SMT DEF AppendEntriesMessage
<1> QED BY <1>prefix, <1>source, <1>covered, <1>campaign_after, <1>small, SMT
    DEF AncestralRequestPrefix

LEMMA RequestPrefixAncestryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationEvidenceInv(voteHistory), NEW family,
           CoversEntryEdges(family, HistoricalEntryEdges),
           RequestPrefixAncestry(voteHistory, family), [Next]_vars
    PROVE RequestPrefixAncestry(nextVoteHistory, family)'
<1>base. TypeOK /\ EntryEdgeBase /\ SendInvariant
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1> SUFFICES ASSUME NEW request \in AppendRequests'
             PROVE AncestralRequestPrefix(nextVoteHistory, family, request)'
    BY SMT DEF RequestPrefixAncestry
<1>old. CASE request \in messages
    BY <1>base, <1>old, AncestralRequestPrefixRetained, SMT
    DEF RequestPrefixAncestry, AppendRequests
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2> QED BY <2>origin, NewAppendRequestHasAncestralPrefix, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA CoveredPrefixesMatch ==
    ASSUME NEW family, WitnessEdgeConsistency(family),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           CoveredPrefix(family, left), CoveredPrefix(family, right)
    PROVE \A index \in (DOMAIN left) \cap (DOMAIN right):
              left[index].term = right[index].term
              => SubSeq(left, 1, index) = SubSeq(right, 1, index)
<1>boundary. \A index \in (DOMAIN left) \cap (DOMAIN right):
        left[index].term = right[index].term =>
            /\ left[index] = right[index]
            /\ index > 1 => left[index - 1].term = right[index - 1].term
    <2> SUFFICES ASSUME NEW index \in (DOMAIN left) \cap (DOMAIN right),
                          left[index].term = right[index].term
                 PROVE /\ left[index] = right[index]
                       /\ index > 1 => left[index - 1].term = right[index - 1].term
        BY SMT
    <2>witnesses. PICK first, second:
            /\ first \in family /\ second \in family
            /\ first.edge = LogEntryEdge(left, index)
            /\ second.edge = LogEntryEdge(right, index)
        BY SMT DEF CoveredPrefix
    <2>edges.
            /\ first.edge.entry = second.edge.entry
            /\ first.edge.previous = second.edge.previous
        BY <2>witnesses, SMT DEF WitnessEdgeConsistency, LogEntryEdge
    <2> QED BY <2>witnesses, <2>edges, SMT DEF LogEntryEdge
<1> QED BY <1>boundary, ConsistentLogEdgesPrefixEqual, SMT

LEMMA SequencePrefixWithLastEntry ==
    ASSUME NEW entries \in Seq(LogEntry), NEW cut \in 0..Len(entries),
           cut < Len(entries)
    PROVE Append(SubSeq(entries, 1, cut), entries[cut + 1]) = SubSeq(entries, 1, cut + 1)
<1>prefix.
        /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, 1, cut)) = cut
        /\ \A index \in 1..cut: SubSeq(entries, 1, cut)[index] = entries[index]
        /\ entries[cut + 1] \in LogEntry
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT
<1>append.
        /\ Append(SubSeq(entries, 1, cut), entries[cut + 1]) \in Seq(LogEntry)
        /\ Len(Append(SubSeq(entries, 1, cut), entries[cut + 1])) = cut + 1
        /\ \A index \in 1..cut:
               Append(SubSeq(entries, 1, cut), entries[cut + 1])[index] = entries[index]
        /\ Append(SubSeq(entries, 1, cut), entries[cut + 1])[cut + 1] = entries[cut + 1]
    BY <1>prefix, AppendProperties, LenProperties, SMT
<1>segment.
        /\ SubSeq(entries, 1, cut + 1) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, 1, cut + 1)) = cut + 1
        /\ \A index \in 1..(cut + 1): SubSeq(entries, 1, cut + 1)[index] = entries[index]
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT
<1>cells. \A index \in 1..(cut + 1):
        Append(SubSeq(entries, 1, cut), entries[cut + 1])[index] =
            SubSeq(entries, 1, cut + 1)[index]
    BY <1>append, <1>segment, SMT
<1> QED BY <1>append, <1>segment, <1>cells, SeqEqual, SMT

\* Unlike the earlier repair lemma, this covers every accepted request and
\* pointer position, including a delayed heartbeat. Consistency is a pre-state
\* joint premise; ancestry coverage itself is already an invariant.
LEMMA AcceptedAppendHasExactPrefix ==
    ASSUME TypeOK, NEW family, WitnessEdgeConsistency(family),
           CoversEntryEdges(family, HistoricalEntryEdges),
           NEW peer \in Server, NEW request \in AppendRequests,
           NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix),
           CoveredPrefix(family, prefix), Len(request.mentries) <= 1,
           currentTerm[peer] = request.mterm, state[peer] # Leader,
           AppendAnchorMatches(request, peer),
           HandleAppendEntriesRequest(peer, request.msource, request)
    PROVE IsPrefix(prefix, log'[peer])
<1>types.
        /\ log[peer] \in Seq(LogEntry)
        /\ request.mentries \in Seq(LogEntry)
        /\ request.mprevLogIndex \in 0..Len(log[peer])
        /\ request.mprevLogIndex \in 0..Len(prefix)
        /\ Len(prefix) = request.mprevLogIndex + Len(request.mentries)
    BY MessageFieldsTypeOK, LenProperties, SMT
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK, AppendRequests, RequestPrefixData,
        AppendAnchorMatches
<1>covered. CoveredPrefix(family, log[peer])
    BY <1>types, CurrentLogPrefixCovered, WholeSequencePrefix, SMT DEF IsPrefix
<1>matching. \A index \in (DOMAIN prefix) \cap (DOMAIN log[peer]):
        prefix[index].term = log[peer][index].term
        => SubSeq(prefix, 1, index) = SubSeq(log[peer], 1, index)
    BY <1>types, <1>covered, CoveredPrefixesMatch, SMT
<1>anchor. SubSeq(prefix, 1, request.mprevLogIndex) =
               SubSeq(log[peer], 1, request.mprevLogIndex)
    BY <1>types, <1>matching, SubSeqEmpty, LenProperties, SMT
    DEF RequestPrefixData, AppendAnchorMatches
<1>empty. CASE request.mentries = << >>
    BY <1>types, <1>anchor, <1>empty, WholeSequencePrefix, EmptySeq, LenProperties, SMT
    DEF HandleAppendEntriesRequest, AppendAnchorMatches, TypeOK, LogVarsTypeOK, IsPrefix
<1>nonempty. CASE request.mentries # << >>
    <2>payload.
            /\ Len(request.mentries) = 1
            /\ Len(prefix) = request.mprevLogIndex + 1
            /\ prefix[request.mprevLogIndex + 1] = request.mentries[1]
        BY <1>types, <1>nonempty, EmptySeq, LenProperties, SMT DEF RequestPrefixData
    <2>replace. CASE
            \/ Len(log[peer]) = request.mprevLogIndex
            \/ log[peer][request.mprevLogIndex + 1].term # request.mentries[1].term
        <3>rpc. prefix = Append(SubSeq(prefix, 1, request.mprevLogIndex), request.mentries[1])
            BY <1>types, <2>payload, SequencePrefixWithLastEntry, WholeSequencePrefix, SMT
        <3>updated. log'[peer] = prefix
            BY <1>types, <1>anchor, <1>nonempty, <2>replace, <3>rpc, SMT
            DEF HandleAppendEntriesRequest, AppendAnchorMatches, TypeOK, LogVarsTypeOK
        <3> QED BY <3>updated, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
    <2>present. CASE
            /\ Len(log[peer]) # request.mprevLogIndex
            /\ log[peer][request.mprevLogIndex + 1].term = request.mentries[1].term
        <3>matching. SubSeq(prefix, 1, Len(prefix)) = SubSeq(log[peer], 1, Len(prefix))
            BY <1>types, <1>matching, <2>payload, <2>present, LenProperties, SMT
        <3> QED BY <1>types, <1>nonempty, <2>payload, <2>present, <3>matching,
            WholeSequencePrefix, LenProperties, SMT
            DEF HandleAppendEntriesRequest, AppendAnchorMatches, TypeOK, LogVarsTypeOK, IsPrefix
    <2> QED BY <2>replace, <2>present, SMT
<1> QED BY <1>empty, <1>nonempty, SMT

LEMMA AppendRequestPreservesProtectedPrefix ==
    ASSUME TypeOK, NEW target \in Seq(LogEntry), NEW term \in Nat,
           NEW peer \in Server, NEW source \in Server,
           NEW request \in AppendRequests,
           currentTerm[peer] >= term, IsPrefix(target, log[peer]),
           request.mterm >= term => RequestRespectsPrefix(request, target),
           HandleAppendEntriesRequest(peer, source, request)
    PROVE IsPrefix(target, log'[peer])
<1>types.
        /\ log[peer] \in Seq(LogEntry)
        /\ Len(log[peer]) \in Nat /\ Len(target) \in Nat
        /\ request.mprevLogIndex \in Nat
        /\ request.mentries \in Seq(LogEntry)
        /\ request.mterm \in Nat /\ currentTerm[peer] \in Nat
    BY MessageFieldsTypeOK, LenProperties, SMT
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK, ServerVarsTypeOK, AppendRequests
<1>same. CASE log'[peer] = log[peer]
    BY <1>same, SMT
<1>changed. CASE log'[peer] # log[peer]
    <2>update.
            /\ request.mterm = currentTerm[peer]
            /\ request.mentries # << >>
            /\ request.mprevLogIndex <= Len(log[peer])
            /\ \/ Len(log[peer]) = request.mprevLogIndex
               \/ log[peer][request.mprevLogIndex + 1].term # request.mentries[1].term
            /\ log'[peer] = Append(SubSeq(log[peer], 1, request.mprevLogIndex), request.mentries[1])
        BY <1>types, <1>changed, SMT
        DEF HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
    <2>respects. RequestRespectsPrefix(request, target)
        BY <2>update, SMT
    <2>payload.
            /\ 1 \in DOMAIN request.mentries
            /\ request.mentries[1] \in LogEntry
        BY <1>types, <2>update, EmptySeq, ElementOfSeq, LenProperties, SMT
    <2>outside. request.mprevLogIndex >= Len(target)
        <3> SUFFICES ASSUME request.mprevLogIndex < Len(target) PROVE FALSE
            BY <1>types, SMT
        <3>index.
                /\ request.mprevLogIndex + 1 \in DOMAIN target
                /\ request.mprevLogIndex + 1 \in 1..Len(target)
                /\ Len(log[peer]) # request.mprevLogIndex
            BY <1>types, LenProperties, SMT DEF IsPrefix
        <3>entry.
                request.mentries[1] = log[peer][request.mprevLogIndex + 1]
            BY <1>types, <2>payload, <2>respects, <3>index, PrefixEntryEqual, SMT
            DEF RequestRespectsPrefix
        <3> QED BY <2>update, <3>index, <3>entry, SMT
    <2>retained.
            /\ SubSeq(log[peer], 1, request.mprevLogIndex) \in Seq(LogEntry)
            /\ Len(SubSeq(log[peer], 1, request.mprevLogIndex)) = request.mprevLogIndex
            /\ IsPrefix(SubSeq(log[peer], 1, request.mprevLogIndex), log[peer])
        BY <1>types, <2>update, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
    <2>prefix. IsPrefix(target, SubSeq(log[peer], 1, request.mprevLogIndex))
        BY <1>types, <2>outside, <2>retained, PrefixesWithBoundedLength, SMT
    <2> QED BY <2>update, <2>payload, <2>retained, <2>prefix, PrefixOnAppend, SMT
<1> QED BY <1>same, <1>changed, SMT

LEMMA ProtectedPeerLogNext ==
    ASSUME EntryEdgeBase, [Next]_vars, NEW target \in Seq(LogEntry), NEW term \in Nat,
           ProtectedAppendRequests(target, term), NEW peer \in Server,
           ProtectedPeer(target, term, peer)
    PROVE IsPrefix(target, log'[peer])
<1>types. TypeOK /\ log[peer] \in Seq(LogEntry)
    BY SMT DEF EntryEdgeBase, TypeOK, LogVarsTypeOK
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>types, <1>client, ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF ProtectedPeer, ClientRequest, TypeOK, LogVarsTypeOK
<1>receive. CASE \E request \in messages:
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    <2>request. PICK request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        BY <1>receive, SMT
    <2>fields.
            /\ request \in AppendRequests
            /\ request.msource \in Server /\ request.mdest \in Server
        BY <1>types, <2>request, MessageFieldsTypeOK, SMT
        DEF AppendRequests, TypeOK, MsgTypeOK
    <2>recipient. CASE peer = request.mdest
        BY <1>types, <2>request, <2>fields, <2>recipient,
           AppendRequestPreservesProtectedPrefix, SMT
        DEF ProtectedPeer, ProtectedAppendRequests
    <2>other. CASE peer # request.mdest
        BY <1>types, <2>request, <2>other, SMT
        DEF ProtectedPeer, HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
    <2> QED BY <2>recipient, <2>other, SMT
<1>same. CASE log' = log
    BY <1>same, SMT DEF ProtectedPeer
<1> QED BY <1>client, <1>receive, <1>same, LogChangingActionNext, SMT

LEMMA ProtectedPeerNext ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), [Next]_vars, NEW target \in Seq(LogEntry), NEW term \in Nat,
           ProtectedAppendRequests(target, term), NEW peer \in Server,
           ProtectedPeer(target, term, peer)
    PROVE ProtectedPeer(target, term, peer)'
<1>base. TypeOK /\ EntryEdgeBase
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>terms.
        /\ currentTerm[peer] \in Nat /\ currentTerm'[peer] \in Nat
        /\ currentTerm[peer] <= currentTerm'[peer]
    BY <1>base, TypeOKNext, ReplicationPrefixInvNext, CurrentTermsMonotonicNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, TypeOK, ServerVarsTypeOK
<1>prefix. IsPrefix(target, log'[peer])
    BY <1>base, ProtectedPeerLogNext, SMT
<1> QED BY <1>terms, <1>prefix, SMT DEF ProtectedPeer

LEMMA CurrentLeaderRequestRespectsPrefix ==
    ASSUME EntryEdgeBase, NEW leader \in Server, NEW peer \in Server,
           NEW target \in Seq(LogEntry), IsPrefix(target, log[leader]),
           NEW request, request = AppendEntriesMessage(leader, peer)
    PROVE RequestRespectsPrefix(request, target)
<1>types. TypeOK /\ log[leader] \in Seq(LogEntry)
    BY SMT DEF EntryEdgeBase, TypeOK, LogVarsTypeOK
<1> SUFFICES ASSUME NEW offset \in DOMAIN request.mentries,
                      request.mprevLogIndex + offset \in DOMAIN target
             PROVE request.mentries[offset] = target[request.mprevLogIndex + offset]
    BY SMT DEF RequestRespectsPrefix
<1>entry.
        /\ offset = 1
        /\ request.mprevLogIndex + offset = nextIndex[leader][peer]
        /\ request.mentries[offset] = log[leader][nextIndex[leader][peer]]
        /\ request.mprevLogIndex + offset \in 1..Len(target)
    BY <1>types, AppendSendEntryOffsetSnapshot, LenProperties, SMT
    DEF AppendEntriesMessage
<1> QED BY <1>types, <1>entry, PrefixEntryEqual, SMT

LEMMA ProtectedAppendRequestsNext ==
    ASSUME EntryEdgeBase, [Next]_vars, NEW target \in Seq(LogEntry), NEW term \in Nat,
           ProtectedLeaders(target, term), ProtectedAppendRequests(target, term)
    PROVE ProtectedAppendRequests(target, term)'
<1> SUFFICES ASSUME NEW request \in AppendRequests', request.mterm >= term
             PROVE RequestRespectsPrefix(request, target)
    BY SMT DEF ProtectedAppendRequests
<1>old. CASE request \in messages
    BY <1>old, SMT DEF AppendRequests, ProtectedAppendRequests
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>protected. IsPrefix(target, log[leader])
        BY <2>origin, SMT DEF ProtectedLeaders, AppendEntries, AppendEntriesMessage
    <2> QED BY <2>origin, <2>protected, CurrentLeaderRequestRespectsPrefix, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA OrderedTermPrefixesAreEdgeConsistent ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family)
    PROVE WitnessEdgeConsistency(family)
<1> SUFFICES ASSUME NEW left \in family, NEW right \in family,
                      left.edge.index = right.edge.index,
                      left.edge.term = right.edge.term
             PROVE /\ left.edge.entry = right.edge.entry
                   /\ left.edge.previous = right.edge.previous
    BY SMT DEF WitnessEdgeConsistency
<1>data.
        /\ left.prefix \in Seq(LogEntry) /\ right.prefix \in Seq(LogEntry)
        /\ left.edge.index \in DOMAIN left.prefix
        /\ left.edge.index \in Nat
        /\ left.edge = LogEntryEdge(left.prefix, left.edge.index)
        /\ right.edge = LogEntryEdge(right.prefix, right.edge.index)
    BY LenProperties, SMT DEF CertificateFamily, CertificateWitness, WitnessPrefixData
<1>prefix. IsPrefix(left.prefix, right.prefix)
    BY <1>data, SMT DEF TermPrefixOrder
<1>equal. left.edge = right.edge
    BY <1>data, <1>prefix, PrefixEntryEdgesEqual, SMT
<1> QED BY <1>equal, SMT

LEMMA FamilyWitnessPrefixCovered ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), NEW witness \in family
    PROVE CoveredPrefix(family, witness.prefix)
    BY SMT DEF CertificateFamily, CoveredPrefix

LEMMA CoveredSequenceHasLastWitness ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), WitnessEdgeConsistency(family),
           NEW entries \in Seq(LogEntry), Len(entries) > 0,
           CoveredPrefix(family, entries)
    PROVE \E witness \in family:
              /\ witness.prefix = entries
              /\ witness.edge.index = Len(entries)
              /\ witness.edge.term = LastTerm(entries)
<1>last. Len(entries) \in DOMAIN entries
    BY LenProperties, SMT
<1>witness. PICK witness \in family:
        witness.edge = LogEntryEdge(entries, Len(entries))
    BY <1>last, SMT DEF CoveredPrefix
<1>data.
        /\ witness.prefix \in Seq(LogEntry)
        /\ Len(witness.prefix) = Len(entries)
        /\ Len(entries) \in DOMAIN witness.prefix
        /\ witness.prefix[Len(entries)].term = entries[Len(entries)].term
        /\ witness.edge.index = Len(entries)
        /\ witness.edge.term = LastTerm(entries)
    BY <1>last, <1>witness, LenProperties, SMT
    DEF CertificateFamily, CertificateWitness, WitnessPrefixData, LogEntryEdge, LastTerm
<1>covered. CoveredPrefix(family, witness.prefix)
    BY <1>witness, FamilyWitnessPrefixCovered, SMT
<1>matching. SubSeq(witness.prefix, 1, Len(entries)) = SubSeq(entries, 1, Len(entries))
    BY <1>last, <1>data, <1>covered, CoveredPrefixesMatch, SMT
<1>equal. witness.prefix = entries
    BY <1>data, <1>matching, WholeSequencePrefix, SMT
<1> QED BY <1>witness, <1>data, <1>equal, SMT

LEMMA CoveredSequencesWithSameLastTermAreOrdered ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           CoveredPrefix(family, left), CoveredPrefix(family, right),
           Len(left) > 0, Len(right) > 0,
           LastTerm(left) = LastTerm(right), Len(left) <= Len(right)
    PROVE IsPrefix(left, right)
<1>consistent. WitnessEdgeConsistency(family)
    BY OrderedTermPrefixesAreEdgeConsistent, SMT
<1>left. PICK first \in family:
        /\ first.prefix = left
        /\ first.edge.index = Len(left)
        /\ first.edge.term = LastTerm(left)
    BY <1>consistent, CoveredSequenceHasLastWitness, SMT
<1>right. PICK second \in family:
        /\ second.prefix = right
        /\ second.edge.index = Len(right)
        /\ second.edge.term = LastTerm(right)
    BY <1>consistent, CoveredSequenceHasLastWitness, SMT
<1> QED BY <1>left, <1>right, SMT DEF TermPrefixOrder

LEMMA ExtendOrderedTermPrefixes ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family), NEW fresh,
           fresh.prefix \in Seq(LogEntry), fresh.edge.index \in Nat,
           \A old \in family:
               old.edge.term = fresh.edge.term =>
                   /\ old.edge.index < fresh.edge.index
                   /\ IsPrefix(old.prefix, fresh.prefix)
    PROVE TermPrefixOrder(family \cup {fresh})
    BY WholeSequencePrefix, LenProperties, SMT
    DEF TermPrefixOrder, IsPrefix, CertificateFamily, CertificateWitness, WitnessPrefixData

\* The old family and current campaign supply the intersections. No post-state
\* agreement or exclusion fact is assumed to order a new creator prefix.
LEMMA CurrentCertificateAdmitsOrderedPrefix ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), NEW family, CertificateFamily(voteHistory, family),
           TermPrefixOrder(family), NEW actor \in Server,
           NEW payload \in ClientPayload, ClientRequest(actor, payload),
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           CurrentElectionCertificate(voteHistory, actor, term, snapshot, occurrence, support),
           NEW fresh, fresh.prefix = log'[actor],
           fresh.edge.index = Len(log[actor]) + 1, fresh.edge.term = term,
           \A old \in family: old.edge.term = term => old.support \cap support # {}
    PROVE TermPrefixOrder(family \cup {fresh})
<1>base. TypeOK /\ VoteRecordInv(voteHistory)
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv
<1>append. PICK entry \in LogEntry:
        log'[actor] = Append(log[actor], entry)
    BY <1>base, ClientRequestAppendsCurrentTerm, SMT
<1>fresh.
        /\ fresh.prefix \in Seq(LogEntry)
        /\ fresh.edge.index \in Nat
        /\ log[actor] \in Seq(LogEntry)
    BY <1>base, <1>append, AppendProperties, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK
<1>old. \A old \in family:
        old.edge.term = fresh.edge.term =>
            /\ old.edge.index < fresh.edge.index
            /\ IsPrefix(old.prefix, fresh.prefix)
    <2> SUFFICES ASSUME NEW old \in family, old.edge.term = fresh.edge.term
                 PROVE /\ old.edge.index < fresh.edge.index
                       /\ IsPrefix(old.prefix, fresh.prefix)
        BY SMT
    <2>votes.
            /\ old.owner \in Server
            /\ VoteSupport(voteHistory, old.owner, term, old.support)
            /\ VoteSupport(voteHistory, actor, term, support)
            /\ old.support \cap support # {}
        BY SMT DEF CertificateFamily, CertificateWitness, WitnessPrefixData,
            RetainedElectionCertificate, CurrentElectionCertificate
    <2>owner. old.owner = actor
        BY <1>base, <2>votes, IntersectingVoteSupportsUnique, SMT
    <2>prefix.
            /\ old.prefix \in Seq(LogEntry)
            /\ IsPrefix(old.prefix, log[actor])
            /\ old.edge.index = Len(old.prefix)
        BY <2>owner, SMT
        DEF CertificateFamily, CertificateWitness, WitnessPrefixData,
            OwnerPrefix, CurrentElectionCertificate
    <2> QED BY <1>append, <1>fresh, <2>prefix, PrefixOnAppend, LenProperties, SMT DEF IsPrefix
<1> QED BY <1>fresh, <1>old, ExtendOrderedTermPrefixes, SMT

LEMMA ClientAppendPreservesLaterTermBoundary ==
    ASSUME TypeOK, NEW family, NEW target \in Seq(LogEntry), NEW term \in Nat,
           LaterTermPrefixProtection(family, target, term), ProtectedLeaders(target, term),
           NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW fresh,
           fresh.prefix = log'[actor], fresh.edge.term = currentTerm[actor]
    PROVE LaterTermPrefixProtection(family \cup {fresh}, target, term)
    BY ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF LaterTermPrefixProtection, ProtectedLeaders, ClientRequest,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK

=======================================================================
