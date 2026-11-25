------------------------------ MODULE proof_configuration_history ------------------------------
\* proof_configuration_history.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_log_history
CandidateAppendFree ==
    \A candidate \in Server:
        state[candidate] = Candidate => \A request \in AppendRequests:
            request.msource = candidate => request.mterm # currentTerm[candidate]

ProtectedVoters(target) ==
    {voter \in Server: IsPrefix(target, log[voter])}

\* The target extends the sender's frozen campaign snapshot. This is evidence
\* about a selected target, not an assertion that every such target is agreed.
TargetCampaignEvidence(voteHistory, leader, term, target) ==
    \E snapshot \in Seq(LogEntry): \E occurrence, support:
        /\ RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
        /\ Len(snapshot) < Len(target)

\* Only a current leader and actual retained same-term RPCs are compared.
\* The joint intersection argument must supply these selected certificate pairs.
CurrentRequestCertificateIntersections(voteHistory) ==
    \A leader \in Server: \A request \in AppendRequests:
        state[leader] = Leader /\ request.mterm = currentTerm[leader] =>
            \E leaderSnapshot, requestSnapshot \in Seq(LogEntry):
            \E leaderOccurrence, requestOccurrence, leaderSupport, requestSupport:
                /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader],
                        leaderSnapshot, leaderOccurrence, leaderSupport)
                /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                        requestSnapshot, requestOccurrence, requestSupport)
                /\ leaderSupport \cap requestSupport # {}

CurrentRequestSendersUnique ==
    \A leader \in Server:
        state[leader] = Leader => \A request \in AppendRequests:
            request.mterm = currentTerm[leader] => request.msource = leader

\* An old match may outlive the peer's eligibility. Physical justification
\* here applies while both the live leader and the acknowledging peer remain
\* in the response term, and includes undelivered successful responses.
SameTermAcknowledgmentPrefixes ==
    \A response \in messages:
        /\ SuccessfulAppendResponse(response)
        /\ state[response.mdest] = Leader
        /\ currentTerm[response.mdest] = response.mterm
        /\ currentTerm[response.msource] = response.mterm
        => \E prefix \in Seq(LogEntry):
               /\ Len(prefix) = response.mmatchIndex
               /\ IsPrefix(prefix, log[response.mdest])
               /\ IsPrefix(prefix, log[response.msource])

RecordedCampaignVoters(voteHistory, candidate, term) ==
    {voter \in Server: RecordedCampaignVote(voteHistory, voter, candidate, term)}

RecordedAcknowledgersProtected(leader, term, target) ==
    RecordedReplicationSupport(leader, term, Len(target)) \subseteq ProtectedVoters(target)

\* These history premises are supplied by the unfinished joint induction.
\* Bundling them does not assert their admission for arbitrary new targets.
TargetHistory(voteHistory, family, target, term) ==
    /\ CertificateFamily(voteHistory, family) /\ TermPrefixOrder(family)
    /\ CoversEntryEdges(family, HistoricalEntryEdges)
    /\ target \in Seq(LogEntry) /\ term \in Nat
    /\ Len(target) > 0 /\ LastTerm(target) = term
    /\ LaterTermPrefixProtection(family, target, term)

\* A present target with its configuration inside the certified prefix. This
\* predicate reads logs and retained evidence, independently of commitIndex.
\* Coverage of all global agreement remains part of the joint argument.
SupportedAgreementTarget(voteHistory, target) ==
    /\ target \in Seq(LogEntry)
    /\ \E certificate:
           /\ RetainedCommitCertificate(voteHistory, certificate)
           /\ certificate.entries = target
           /\ certificate.index = Len(target)
           /\ IsPrefix(target, log[certificate.leader])

LogPrefixSet(logs) ==
    UNION {{SubSeq(logs[server], 1, cut): cut \in 0..Len(logs[server])}: server \in Server}

EvidenceAgreementTargets(voteHistory) ==
    {target \in LogPrefixSet(log): SupportedAgreementTarget(voteHistory, target)}

InitialConfigurationOccurrence ==
    [index |-> 0, prefix |-> << >>, members |-> InitialConfig]

ConfigurationHistory(targets) ==
    {InitialConfigurationOccurrence}
        \cup {LatestConfigurationOccurrence(target): target \in targets}

ConfigurationOccurrenceData(occurrence) ==
    /\ occurrence.prefix \in Seq(LogEntry)
    /\ occurrence.index = Len(occurrence.prefix)
    /\ occurrence.members = ConfigOf(occurrence.prefix)
    /\ occurrence = [index |-> occurrence.index, prefix |-> occurrence.prefix,
                     members |-> occurrence.members]

ConfigurationHistoryData(history) ==
    /\ IsFiniteSet(history) /\ history # {}
    /\ \A occurrence \in history: ConfigurationOccurrenceData(occurrence)

ConfigurationHistoryCompatible(history) ==
    \A left, right \in history:
        IsPrefix(left.prefix, right.prefix) \/ IsPrefix(right.prefix, left.prefix)

LatestEvidenceOccurrence(history) ==
    CHOOSE occurrence \in history:
        \A earlier \in history: earlier.index <= occurrence.index

EvidenceConfigurationHistory(voteHistory) == ConfigurationHistory(EvidenceAgreementTargets(voteHistory))

\* A state-derived candidate for the working configuration, with no local CI
\* or added history variable. Global agreement coverage and compatible admission
\* remain obligations; finiteness, selection, and retention are proved below.
EvidenceWorkingConfiguration(voteHistory) == LatestEvidenceOccurrence(EvidenceConfigurationHistory(voteHistory))

\* These are the historical boundaries to be supplied by the joint induction.
\* The admission lemma below uses them only for existing targets, not for the
\* targets whose new evidence is being admitted.
AgreementTargetBoundaries(family, targets) ==
    /\ targets \subseteq Seq(LogEntry)
    /\ \A target \in targets:
           /\ Len(target) > 0
           /\ CoveredPrefix(family, target)
           /\ LaterTermPrefixProtection(family, target, LastTerm(target))

LEMMA RecordedCampaignVoteTermBound ==
    ASSUME NEW voteHistory, TypeOK, SendInvariant, NEW voter \in Server, NEW candidate \in Server,
           NEW term \in Nat, RecordedCampaignVote(voteHistory, voter, candidate, term)
    PROVE term <= currentTerm[voter]
    BY SMT DEF RecordedCampaignVote, Grant, Started, SendInvariant

LEMMA RecordedCampaignVotersRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), [Next]_vars, NEW candidate \in Server, NEW term \in Nat
    PROVE RecordedCampaignVoters(voteHistory, candidate, term) \subseteq RecordedCampaignVoters(nextVoteHistory, candidate, term)'
    BY CampaignHistoryContextMonotone, MessagesMonotonicNext, SMT
    DEF RecordedCampaignVoters, RecordedCampaignVote, Grant, Started,
        CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord

LEMMA RecordedCampaignVoteRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), [Next]_vars,
           NEW voter \in Server, NEW candidate \in Server, NEW term \in Nat,
           RecordedCampaignVote(voteHistory, voter, candidate, term)
    PROVE RecordedCampaignVote(nextVoteHistory, voter, candidate, term)'
    BY RecordedCampaignVotersRetained, SMT DEF RecordedCampaignVoters

LEMMA VoteSupportWithinRecordedCampaignVoters ==
    ASSUME NEW voteHistory, NEW candidate \in Server, NEW term \in Nat, NEW support,
           VoteSupport(voteHistory, candidate, term, support)
    PROVE support \subseteq RecordedCampaignVoters(voteHistory, candidate, term)
    BY SMT DEF VoteSupport, VoteFor, RecordedCampaignVoters, RecordedCampaignVote

LEMMA NewAcknowledgmentUsesPostTerm ==
    ASSUME TypeOK, [Next]_vars, NEW response \in messages' \ messages,
           SuccessfulAppendResponse(response)
    PROVE response.mterm = currentTerm'[response.msource]
    BY NewAcknowledgmentReceiveOrigin, SMT
    DEF ResponseMatchesRequest, HandleAppendEntriesRequest

\* This also covers a vote and acknowledgment both alleged to be new in one
\* step. A new success leaves its peer in the response term, while a recorded
\* higher vote requires the peer's post-state term to be at least that high.
LEMMA HigherPostVoteForcesOldAcknowledgmentPreexisting ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, TypeOK', SendInvariant', [Next]_vars,
           NEW voter \in Server, NEW candidate \in Server, NEW leader \in Server,
           NEW earlier \in Nat, NEW later \in Nat, NEW index \in Nat,
           earlier < later, RecordedCampaignVote(nextVoteHistory, voter, candidate, later)',
           RecordedAcknowledgment(voter, leader, earlier, index)'
    PROVE RecordedAcknowledgment(voter, leader, earlier, index)
<1>term.
        /\ currentTerm'[voter] \in Nat
        /\ later <= currentTerm'[voter]
    BY SMT
    DEF TypeOK, ServerVarsTypeOK, RecordedCampaignVote, Grant, Started, SendInvariant
<1>response. PICK response \in messages':
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = voter /\ response.mdest = leader
        /\ response.mterm = earlier /\ response.mmatchIndex >= index
    BY SMT DEF RecordedAcknowledgment
<1>old. CASE response \in messages
    BY <1>response, <1>old, SMT DEF RecordedAcknowledgment
<1>new. CASE response \notin messages
    BY <1>term, <1>response, <1>new, NewAcknowledgmentUsesPostTerm, SMT
<1> QED BY <1>old, <1>new, SMT

\* Replication bounds prevent old responses from acknowledging a fresh index.
\* These admission facts concern a new local entry, before claiming agreement.
LEMMA ClientAppendHasOnlySelfRecordedSupport ==
    ASSUME ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW term \in Nat, term = currentTerm[actor],
           NEW index \in Nat, index = Len(log[actor]) + 1
    PROVE RecordedReplicationSupport(actor, term, index)' = {actor}
<1>types. TypeOK /\ Len(log[actor]) \in Nat
    BY LenProperties, SMT DEF ReplicationBoundsInv, TypeOK, LogVarsTypeOK
<1>no_ack. \A peer \in Server: ~RecordedAcknowledgment(peer, actor, term, index)'
    BY <1>types, MessageFieldsTypeOK, SMT
    DEF ReplicationBoundsInv, ResponseIndexBound, ClientRequest,
        RecordedAcknowledgment, SuccessfulAppendResponse, TypeOK, MsgTypeOK
<1> QED BY <1>no_ack, SMT DEF RecordedReplicationSupport

LEMMA CandidateContinuesOrTimesOut ==
    ASSUME TypeOK, [Next]_vars, NEW candidate \in Server, state'[candidate] = Candidate
    PROVE \/ /\ state[candidate] = Candidate
             /\ currentTerm'[candidate] = currentTerm[candidate]
          \/ Timeout(candidate)
<1> DEFINE P ==
        \/ /\ state[candidate] = Candidate
           /\ currentTerm'[candidate] = currentTerm[candidate]
        \/ Timeout(candidate)
<1>unchanged. UNCHANGED <<state, currentTerm>> => P BY SMT DEF P
<1>timeout. \A actor \in Server: Timeout(actor) => P
    BY SMT DEF P, Timeout, TypeOK, ServerVarsTypeOK
<1>leader. \A actor \in Server: BecomeLeader(actor) => P
    BY ServerStatesDistinct, SMT DEF P, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>retirement. \A actor \in Server: Restart(actor) \/ LeaderStepDown(actor) => P
    BY ServerStatesDistinct, SMT DEF P, Restart, LeaderStepDown, TypeOK, ServerVarsTypeOK
<1>update. \A message \in messages:
        UpdateTerm(message.mdest, message.msource, message) => P
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
    DEF P, UpdateTerm, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>append_request. \A message \in messages:
        HandleAppendEntriesRequest(message.mdest, message.msource, message) => P
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
    DEF P, HandleAppendEntriesRequest, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>frames.
        /\ \A actor \in Server, payload \in ClientPayload:
               ClientRequest(actor, payload) => UNCHANGED <<state, currentTerm>>
        /\ \A actor \in Server:
               AdvanceCommitIndex(actor) => UNCHANGED <<state, currentTerm>>
        /\ \A actor, peer \in Server:
               AppendEntries(actor, peer) => UNCHANGED <<state, currentTerm>>
        /\ \A message \in messages:
               HandleRequestVoteRequest(message.mdest, message.msource, message)
                   \/ HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED <<state, currentTerm>>
    BY Zenon
    DEF ClientRequest, AdvanceCommitIndex, AppendEntries, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>timeout, <1>leader, <1>retirement, <1>update,
    <1>append_request, <1>frames, SMT DEF Next, vars, Receive, HandleMsg, P

LEMMA CandidateAppendFreeNext ==
    ASSUME EntryEdgeBase, SendInvariant, CandidateAppendFree, [Next]_vars
    PROVE CandidateAppendFree'
<1>base. TypeOK
    BY SMT DEF EntryEdgeBase
<1> SUFFICES ASSUME NEW candidate \in Server, state'[candidate] = Candidate,
                      NEW request \in AppendRequests', request.msource = candidate,
                      request.mterm = currentTerm'[candidate]
             PROVE FALSE
    BY SMT DEF CandidateAppendFree
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer)
            /\ request = AppendEntriesMessage(leader, peer)
        BY <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2> QED BY <2>origin, ServerStatesDistinct, SMT
        DEF AppendEntries, AppendEntriesMessage, TypeOK, ServerVarsTypeOK
<1>old. CASE request \in messages
    <2>fields.
            /\ request.mterm \in Nat
            /\ currentTerm[candidate] \in Nat
            /\ request.mterm <= currentTerm[candidate]
        BY <1>base, <1>old, MessageFieldsTypeOK, SMT
        DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, SendInvariant
    <2>continues. CASE
            /\ state[candidate] = Candidate
            /\ currentTerm'[candidate] = currentTerm[candidate]
        BY <1>old, <2>continues, SMT DEF CandidateAppendFree, AppendRequests
    <2>timeout. CASE Timeout(candidate)
        BY <1>base, <2>fields, <2>timeout, SMT
        DEF Timeout, TypeOK, ServerVarsTypeOK
    <2> QED BY <1>base, <2>continues, <2>timeout, CandidateContinuesOrTimesOut, SMT
<1> QED BY <1>new, <1>old, SMT

LEMMA CandidateAppendFreeInit == Init => CandidateAppendFree
    BY SMT DEF Init, CandidateAppendFree, AppendRequests

LEMMA CandidateHasNoCurrentAppendResponses ==
    ASSUME TypeOK, SuccessfulResponseOriginInv, CandidateAppendFree,
           NEW candidate \in Server, state[candidate] = Candidate
    PROVE ~\E response \in messages:
              /\ SuccessfulAppendResponse(response)
              /\ response.mdest = candidate
              /\ response.mterm = currentTerm[candidate]
    BY SMT
    DEF SuccessfulResponseOriginInv, ResponseMatchesRequest, CandidateAppendFree, AppendRequests

LEMMA OrderedPrefixLastTermBound ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry),
           Len(prefix) > 0, IsPrefix(prefix, entries), TermsOrdered(entries)
    PROVE LastTerm(prefix) <= LastTerm(entries)
<1>bounds.
        /\ Len(prefix) \in 1..Len(entries)
        /\ Len(prefix) \in DOMAIN prefix
        /\ Len(prefix) \in DOMAIN entries
        /\ Len(entries) \in DOMAIN entries
        /\ Len(entries) > 0
    BY LenProperties, SMT DEF IsPrefix
<1>entry. prefix[Len(prefix)] = entries[Len(prefix)]
    BY <1>bounds, PrefixEntryEqual, SMT
<1> QED BY <1>bounds, <1>entry, SMT DEF TermsOrdered, LastTerm

LEMMA RetainedCampaignSnapshotLengthsEqual ==
    ASSUME NEW voteHistory, NEW leader \in Server, NEW term \in Nat,
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           NEW leftOccurrence, NEW rightOccurrence, NEW leftSupport, NEW rightSupport,
           RetainedElectionCertificate(voteHistory, leader, term, left, leftOccurrence, leftSupport),
           RetainedElectionCertificate(voteHistory, leader, term, right, rightOccurrence, rightSupport)
    PROVE Len(left) = Len(right)
    BY HistorySnapshotIsUnique, SMT DEF RetainedElectionCertificate

LEMMA EntryWitnessSuppliesTargetCampaignEvidence ==
    ASSUME NEW voteHistory
    PROVE \A witness:
        CertificateWitness(voteHistory, witness)
        => TargetCampaignEvidence(voteHistory, witness.owner, witness.edge.term, witness.prefix)
    BY SMT DEF CertificateWitness, WitnessPrefixData, TargetCampaignEvidence

LEMMA CommitCertificateSuppliesTargetCampaignEvidence ==
    ASSUME NEW voteHistory
    PROVE \A certificate:
        RetainedCommitCertificate(voteHistory, certificate)
        => TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
    BY CommitCertificateTargetProperties, SMT
    DEF RetainedCommitCertificate, TargetCampaignEvidence

\* A long-enough request from this sender/term cannot be an older snapshot:
\* its campaign boundary forces a current-term last entry. Ordered term
\* ancestry then identifies the target, even when the sender is now inactive.
LEMMA FrozenRequestPrefixContainsTarget ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(family, target),
           TargetCampaignEvidence(voteHistory, leader, term, target), NEW request,
           request.msource = leader, request.mterm = term,
           NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix),
           RequestCampaignBoundary(voteHistory, request, prefix), CoveredPrefix(family, prefix),
           Len(target) <= Len(prefix)
    PROVE IsPrefix(target, prefix)
<1>target_campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
        /\ Len(snapshot) < Len(target)
    BY SMT DEF TargetCampaignEvidence
<1>request_campaign. PICK requestSnapshot, requestOccurrence, requestSupport:
        /\ requestSnapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, leader, term, requestSnapshot, requestOccurrence, requestSupport)
        /\ \A index \in DOMAIN prefix:
               prefix[index].term < term => index <= Len(requestSnapshot)
    BY SMT DEF RequestCampaignBoundary
<1>same_length. Len(snapshot) = Len(requestSnapshot)
    BY <1>target_campaign, <1>request_campaign, RetainedCampaignSnapshotLengthsEqual, SMT
<1>types.
        /\ Len(prefix) \in Nat /\ Len(target) \in Nat
        /\ Len(snapshot) \in Nat /\ Len(requestSnapshot) \in Nat
        /\ Len(prefix) > 0 /\ Len(prefix) \in DOMAIN prefix
        /\ LastTerm(prefix) \in Nat
    BY <1>target_campaign, <1>request_campaign, LastTermTypeOK, LenProperties, SMT
<1>last.
        /\ LastTerm(prefix) <= term
        /\ (LastTerm(prefix) < term => Len(prefix) <= Len(requestSnapshot))
    BY <1>types, <1>request_campaign, SMT DEF RequestPrefixData, EntryStructure, LastTerm
<1>term. LastTerm(prefix) = term
    BY <1>target_campaign, <1>same_length, <1>types, <1>last, SMT
<1> QED BY <1>types, <1>term, CoveredSequencesWithSameLastTermAreOrdered, SMT

\* Existing holders persist under protected requests. A new acknowledgment
\* gains its physical prefix from the actual receive and the frozen campaign
\* boundary above; no current leadership assumption is made about its sender.
LEMMA RecordedAcknowledgersProtectedNext ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), NEW family, NEW target, NEW term,
           TargetHistory(voteHistory, family, target, term), RequestPrefixAncestry(voteHistory, family),
           NEW leader \in Server, TargetCampaignEvidence(voteHistory, leader, term, target),
           ProtectedAppendRequests(target, term), RecordedAcknowledgersProtected(leader, term, target),
           [Next]_vars
    PROVE RecordedAcknowledgersProtected(leader, term, target)'
<1>base. TypeOK /\ SendInvariant
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>types. target \in Seq(LogEntry) /\ term \in Nat /\ Len(target) \in Nat
    BY LenProperties, SMT DEF TargetHistory
<1>consistent. WitnessEdgeConsistency(family)
    BY OrderedTermPrefixesAreEdgeConsistent, SMT DEF TargetHistory
<1>self. leader \in ProtectedVoters(target)
    BY SMT DEF RecordedAcknowledgersProtected, RecordedReplicationSupport
<1>target. CoveredPrefix(family, target)
    BY <1>base, <1>types, <1>self, CurrentLogPrefixCovered, SMT
    DEF TargetHistory, ProtectedVoters, TypeOK, LogVarsTypeOK
<1>post_type. TypeOK'
    BY TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW peer \in RecordedReplicationSupport(leader, term, Len(target))'
             PROVE peer \in ProtectedVoters(target)'
    BY SMT DEF RecordedAcknowledgersProtected
<1>peer. peer \in Server
    BY SMT DEF RecordedReplicationSupport
<1>old. CASE peer \in RecordedReplicationSupport(leader, term, Len(target))
    <2>prefix. IsPrefix(target, log[peer])
        BY <1>old, SMT DEF RecordedAcknowledgersProtected, ProtectedVoters
    <2>term. term <= currentTerm[peer]
        BY <1>base, <1>old, SMT
        DEF RecordedReplicationSupport, RecordedAcknowledgment, TargetCampaignEvidence,
            RetainedElectionCertificate, VoteSupport, Started, SendInvariant
    <2>holder. ProtectedPeer(target, term, peer)'
        BY <1>types, <1>peer, <2>prefix, <2>term, ProtectedPeerNext, SMT DEF ProtectedPeer
    <2> QED BY <1>peer, <2>holder, SMT DEF ProtectedPeer, ProtectedVoters
<1>new. CASE peer \notin RecordedReplicationSupport(leader, term, Len(target))
    <2>response. PICK response \in messages' \ messages:
            /\ SuccessfulAppendResponse(response)
            /\ response.msource = peer /\ response.mdest = leader
            /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        BY <1>new, SMT DEF RecordedReplicationSupport, RecordedAcknowledgment
    <2>origin. PICK request \in AppendRequests:
            /\ ResponseMatchesRequest(response, request)
            /\ HandleAppendEntriesRequest(peer, leader, request)
            /\ currentTerm[peer] = request.mterm /\ state[peer] # Leader
            /\ AppendAnchorMatches(request, peer)
        BY <1>base, <2>response, NewAcknowledgmentReceiveOrigin, SMT
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(family, prefix)
            /\ RequestCampaignBoundary(voteHistory, request, prefix)
            /\ Len(request.mentries) <= 1
        BY <2>origin, SMT DEF RequestPrefixAncestry, AncestralRequestPrefix
    <2>contains. IsPrefix(target, prefix)
        BY <1>types, <1>target, <2>response, <2>origin, <2>prefix,
           FrozenRequestPrefixContainsTarget, SMT
        DEF TargetHistory, ResponseMatchesRequest, RequestPrefixData
    <2>received. IsPrefix(prefix, log'[peer])
        BY <1>base, <1>consistent, <1>peer, <2>response, <2>origin, <2>prefix,
           AcceptedAppendHasExactPrefix, SMT DEF TargetHistory, ResponseMatchesRequest
    <2> QED BY <1>types, <1>peer, <1>post_type, <2>prefix, <2>contains, <2>received,
        SequencePrefixTransitive, SMT DEF ProtectedVoters, TypeOK, LogVarsTypeOK
<1> QED BY <1>old, <1>new, SMT

\* The consistency premise is still part of the joint induction. This states
\* what a new success proves at its creation; persistence is handled separately
\* by protected requests, since uncommitted acknowledged entries may be lost.
LEMMA NewAcknowledgmentHasPhysicalPrefix ==
    ASSUME NEW voteHistory, TypeOK, [Next]_vars, NEW family,
           CoversEntryEdges(family, HistoricalEntryEdges),
           WitnessEdgeConsistency(family), RequestPrefixAncestry(voteHistory, family),
           NEW response \in messages' \ messages, SuccessfulAppendResponse(response)
    PROVE \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
              /\ ResponseMatchesRequest(response, request)
              /\ RequestPrefixData(request, prefix)
              /\ CoveredPrefix(family, prefix)
              /\ OwnerPrefix(request.msource, request.mterm, prefix)
              /\ response.mmatchIndex = Len(prefix)
              /\ currentTerm'[response.msource] = response.mterm
              /\ IsPrefix(prefix, log'[response.msource])
<1>origin. PICK request \in AppendRequests:
        /\ ResponseMatchesRequest(response, request)
        /\ HandleAppendEntriesRequest(response.msource, response.mdest, request)
        /\ currentTerm[response.msource] = request.mterm
        /\ state[response.msource] # Leader
        /\ AppendAnchorMatches(request, response.msource)
    BY NewAcknowledgmentReceiveOrigin, SMT
<1>fields.
        /\ response.msource \in Server /\ response.mdest \in Server
        /\ request.msource = response.mdest
        /\ request.mdest = response.msource
        /\ request.mterm = response.mterm
    BY <1>origin, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ResponseMatchesRequest, AppendRequests
<1>prefix. PICK prefix \in Seq(LogEntry):
        /\ RequestPrefixData(request, prefix)
        /\ CoveredPrefix(family, prefix)
        /\ OwnerPrefix(request.msource, request.mterm, prefix)
        /\ Len(request.mentries) <= 1
    BY <1>origin, SMT DEF RequestPrefixAncestry, AncestralRequestPrefix
<1>received. IsPrefix(prefix, log'[response.msource])
    BY <1>origin, <1>fields, <1>prefix, AcceptedAppendHasExactPrefix, SMT
<1>term. currentTerm'[response.msource] = response.mterm
    BY <1>origin, <1>fields, SMT DEF HandleAppendEntriesRequest
<1>length. response.mmatchIndex = Len(prefix)
    BY <1>origin, <1>prefix, SMT DEF ResponseMatchesRequest, RequestPrefixData
<1> QED BY <1>origin, <1>prefix, <1>received, <1>term, <1>length, SMT

LEMMA IntersectingRequestCertificatesIdentifySenders ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), CurrentRequestCertificateIntersections(voteHistory)
    PROVE CurrentRequestSendersUnique
<1> SUFFICES ASSUME NEW leader \in Server, state[leader] = Leader,
                      NEW request \in AppendRequests, request.mterm = currentTerm[leader]
             PROVE request.msource = leader
    BY SMT DEF CurrentRequestSendersUnique
<1>base. TypeOK /\ VoteRecordInv(voteHistory)
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>fields. request.msource \in Server /\ currentTerm[leader] \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, AppendRequests
<1>pair. PICK leaderSnapshot, requestSnapshot, leaderOccurrence, requestOccurrence,
              leaderSupport, requestSupport:
        /\ leaderSnapshot \in Seq(LogEntry) /\ requestSnapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader],
                leaderSnapshot, leaderOccurrence, leaderSupport)
        /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                requestSnapshot, requestOccurrence, requestSupport)
        /\ leaderSupport \cap requestSupport # {}
    BY SMT DEF CurrentRequestCertificateIntersections
<1> QED BY <1>base, <1>fields, <1>pair, IntersectingVoteSupportsUnique, SMT
    DEF CurrentElectionCertificate, RetainedElectionCertificate

LEMMA ContinuingLeaderTermNext ==
    ASSUME TypeOK, [Next]_vars, NEW leader \in Server,
           state[leader] = Leader, state'[leader] = Leader
    PROVE currentTerm'[leader] = currentTerm[leader]
    BY ContinuingLeaderFrameExceptClientRequest, SMT DEF Next, ClientRequest

LEMMA ContinuingLeaderPrefixNext ==
    ASSUME TypeOK, [Next]_vars, NEW leader \in Server, NEW target \in Seq(LogEntry),
           state[leader] = Leader, state'[leader] = Leader, IsPrefix(target, log[leader])
    PROVE /\ currentTerm'[leader] = currentTerm[leader]
          /\ IsPrefix(target, log'[leader])
<1>term. currentTerm'[leader] = currentTerm[leader]
    BY ContinuingLeaderTermNext, SMT
<1>epoch. PICK term \in Nat: term = currentTerm[leader]
    BY SMT DEF TypeOK, ServerVarsTypeOK
<1>owner. OwnerPrefix(leader, term, target)
    BY <1>epoch, SMT DEF OwnerPrefix
<1>after. OwnerPrefix(leader, term, target)'
    BY <1>epoch, <1>owner, OwnerPrefixNext, SMT
<1> QED BY <1>term, <1>epoch, <1>after, SMT DEF OwnerPrefix

LEMMA SameTermRequestRespectsLeaderPrefix ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CurrentRequestSendersUnique,
           NEW leader \in Server, state[leader] = Leader,
           NEW target \in Seq(LogEntry), IsPrefix(target, log[leader]),
           NEW request \in AppendRequests, request.mterm = currentTerm[leader]
    PROVE RequestRespectsPrefix(request, target)
<1>base. TypeOK /\ log[leader] \in Seq(LogEntry)
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        EntryEdgeBase, TypeOK, LogVarsTypeOK
<1>source. request.msource = leader
    BY SMT DEF CurrentRequestSendersUnique
<1>prefix. PICK prefix \in Seq(LogEntry):
        /\ RequestPrefixData(request, prefix)
        /\ OwnerPrefix(request.msource, request.mterm, prefix)
    BY SMT DEF ReplicationPrefixInv, RequestPrefixEvidenceInv, RequestPrefixEvidence
<1>owned. IsPrefix(prefix, log[leader])
    BY <1>source, <1>prefix, SMT DEF OwnerPrefix
<1> SUFFICES ASSUME NEW offset \in DOMAIN request.mentries,
                      request.mprevLogIndex + offset \in DOMAIN target
             PROVE request.mentries[offset] = target[request.mprevLogIndex + offset]
    BY SMT DEF RequestRespectsPrefix
<1>index.
        /\ request.mprevLogIndex + offset \in 1..Len(prefix)
        /\ request.mprevLogIndex + offset \in 1..Len(target)
    BY <1>base, <1>prefix, MessageFieldsTypeOK, LenProperties, SMT
    DEF RequestPrefixData, AppendRequests, TypeOK, MsgTypeOK
<1> QED BY <1>base, <1>prefix, <1>owned, <1>index, PrefixEntryEqual, SMT
    DEF RequestPrefixData

LEMMA SameTermPeerPrefixNext ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CurrentRequestSendersUnique, [Next]_vars,
           NEW leader \in Server, NEW peer \in Server, NEW term \in Nat,
           NEW target \in Seq(LogEntry), state[leader] = Leader, state'[leader] = Leader,
           currentTerm[leader] = term, currentTerm[peer] = term,
           IsPrefix(target, log[leader]), IsPrefix(target, log[peer])
    PROVE /\ currentTerm'[leader] = term
          /\ IsPrefix(target, log'[leader]) /\ IsPrefix(target, log'[peer])
<1>base. TypeOK /\ EntryEdgeBase /\ log[peer] \in Seq(LogEntry)
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        EntryEdgeBase, TypeOK, LogVarsTypeOK
<1>leader. currentTerm'[leader] = term /\ IsPrefix(target, log'[leader])
    BY <1>base, ContinuingLeaderPrefixNext, SMT
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>base, <1>leader, <1>client, ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF ClientRequest, TypeOK, LogVarsTypeOK
<1>receive. CASE \E request \in messages:
        /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    <2>request. PICK request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        BY <1>receive, SMT
    <2>fields.
            /\ request \in AppendRequests /\ request.mterm \in Nat
            /\ request.msource \in Server /\ request.mdest \in Server
        BY <1>base, <2>request, MessageFieldsTypeOK, SMT
        DEF AppendRequests, TypeOK, MsgTypeOK
    <2>recipient. CASE peer = request.mdest
        <3>respects. request.mterm >= term => RequestRespectsPrefix(request, target)
            <4> SUFFICES ASSUME request.mterm >= term PROVE RequestRespectsPrefix(request, target)
                BY SMT
            <4>term. request.mterm = term
                BY <2>request, <2>fields, <2>recipient, SMT DEF HandleAppendEntriesRequest
            <4> QED BY <2>fields, <4>term, SameTermRequestRespectsLeaderPrefix, SMT
        <3> QED BY <1>base, <1>leader, <2>request, <2>fields, <2>recipient,
            <3>respects, AppendRequestPreservesProtectedPrefix, SMT
    <2>other. CASE peer # request.mdest
        BY <1>base, <1>leader, <2>request, <2>other, SMT
        DEF HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
    <2> QED BY <2>recipient, <2>other, SMT
<1>same. CASE log' = log
    BY <1>leader, <1>same, SMT
<1> QED BY <1>base, <1>client, <1>receive, <1>same, LogChangingActionNext, SMT

LEMMA SameTermAcknowledgmentPrefixesNext ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CandidateAppendFree, SameTermAcknowledgmentPrefixes,
           CurrentRequestSendersUnique, NEW family,
           CoversEntryEdges(family, HistoricalEntryEdges), WitnessEdgeConsistency(family),
           RequestPrefixAncestry(voteHistory, family), [Next]_vars
    PROVE SameTermAcknowledgmentPrefixes'
<1>base. TypeOK /\ SendInvariant /\ SuccessfulResponseOriginInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>post_type. TypeOK'
    BY TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response),
                      state'[response.mdest] = Leader,
                      currentTerm'[response.mdest] = response.mterm,
                      currentTerm'[response.msource] = response.mterm
             PROVE \E prefix \in Seq(LogEntry):
                       /\ Len(prefix) = response.mmatchIndex
                       /\ IsPrefix(prefix, log'[response.mdest])
                       /\ IsPrefix(prefix, log'[response.msource])
    BY SMT DEF SameTermAcknowledgmentPrefixes
<1>fields.
        /\ response.msource \in Server /\ response.mdest \in Server
        /\ response.mterm \in Nat
    BY <1>post_type, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>old. CASE response \in messages
    <2>continues. CASE state[response.mdest] = Leader
        <3>terms.
                /\ currentTerm[response.mdest] = response.mterm
                /\ currentTerm[response.msource] = response.mterm
            BY <1>base, <1>fields, <1>old, <2>continues,
               ContinuingLeaderTermNext, CurrentTermsMonotonicNext, SMT
            DEF TypeOK, ServerVarsTypeOK, SendInvariant
        <3>prefix. PICK prefix \in Seq(LogEntry):
                /\ Len(prefix) = response.mmatchIndex
                /\ IsPrefix(prefix, log[response.mdest])
                /\ IsPrefix(prefix, log[response.msource])
            BY <1>old, <2>continues, <3>terms, SMT DEF SameTermAcknowledgmentPrefixes
        <3>after.
                /\ IsPrefix(prefix, log'[response.mdest])
                /\ IsPrefix(prefix, log'[response.msource])
            BY <1>fields, <2>continues, <3>terms, <3>prefix, SameTermPeerPrefixNext, SMT
        <3> QED BY <3>prefix, <3>after, SMT
    <2>promoted. CASE state[response.mdest] # Leader
        <3>action. BecomeLeader(response.mdest)
            BY <1>base, <1>fields, <2>promoted, NewLeaderUsesBecomeLeader, SMT
        <3>candidate.
                /\ state[response.mdest] = Candidate
                /\ currentTerm[response.mdest] = response.mterm
            BY <3>action, SMT DEF BecomeLeader
        <3> QED BY <1>base, <1>fields, <1>old, <3>candidate,
            CandidateHasNoCurrentAppendResponses, SMT
    <2> QED BY <2>continues, <2>promoted, SMT
<1>new. CASE response \notin messages
    <2>prefix. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request)
            /\ OwnerPrefix(request.msource, request.mterm, prefix)
            /\ Len(prefix) = response.mmatchIndex
            /\ IsPrefix(prefix, log'[response.msource])
        BY <1>base, <1>new, NewAcknowledgmentHasPhysicalPrefix, SMT
    <2>fields. request.msource \in Server /\ request.mterm \in Nat
        BY <1>base, <2>prefix, MessageFieldsTypeOK, SMT
        DEF TypeOK, MsgTypeOK, AppendRequests
    <2>owner. OwnerPrefix(request.msource, request.mterm, prefix)'
        BY <1>base, <2>prefix, <2>fields, OwnerPrefixNext, SMT
    <2>leader. IsPrefix(prefix, log'[response.mdest])
        BY <2>prefix, <2>owner, SMT DEF ResponseMatchesRequest, OwnerPrefix
    <2> QED BY <2>prefix, <2>leader, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA RequestIntersectionsPreserveAcknowledgmentPrefixes ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CandidateAppendFree, SameTermAcknowledgmentPrefixes,
           CurrentRequestCertificateIntersections(voteHistory), NEW family,
           CoversEntryEdges(family, HistoricalEntryEdges), WitnessEdgeConsistency(family),
           RequestPrefixAncestry(voteHistory, family), [Next]_vars
    PROVE SameTermAcknowledgmentPrefixes'
<1>campaigns. MembershipCampaignsInv(voteHistory)
    BY SMT DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv
<1>owners. CurrentRequestSendersUnique
    BY <1>campaigns, IntersectingRequestCertificatesIdentifySenders, SMT
<1> QED BY <1>owners, SameTermAcknowledgmentPrefixesNext, SMT

LEMMA SameTermAcknowledgmentPrefixesInit == Init => SameTermAcknowledgmentPrefixes
    BY SMT DEF Init, SameTermAcknowledgmentPrefixes

LEMMA CertificateTargetWithConfigurationCanBeTrimmed ==
    ASSUME NEW voteHistory, TypeOK, NEW certificate, RetainedCommitCertificate(voteHistory, certificate),
           certificate.configuration.index <= certificate.index
    PROVE \E reduced:
              /\ RetainedCommitCertificate(voteHistory, reduced)
              /\ reduced.leader = certificate.leader
              /\ reduced.entries = CommitTarget(certificate)
              /\ reduced.index = Len(CommitTarget(certificate))
              /\ reduced.configuration = certificate.configuration
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ Len(CommitTarget(certificate)) = certificate.index
        /\ IsPrefix(CommitTarget(certificate), certificate.entries)
        /\ CommitTarget(certificate)[certificate.index].term = certificate.term
    BY CommitCertificateTargetProperties, SMT
<1>data.
        /\ certificate.entries \in Seq(LogEntry)
        /\ certificate.snapshot \in Seq(LogEntry)
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.index \in 1..Len(certificate.entries)
        /\ TermsOrdered(CommitTarget(certificate))
        /\ EntryStructure(CommitTarget(certificate), certificate.term)
    BY TermsOrderedOnPrefix, EntryStructureOnSubSeq, SMT
    DEF RetainedCommitCertificate, CommitTarget
<1>snapshot. IsPrefix(certificate.snapshot, CommitTarget(certificate))
    BY <1>target, <1>data, PrefixesWithBoundedLength, SMT DEF RetainedCommitCertificate
<1>configuration. LatestConfigurationOccurrence(CommitTarget(certificate)) = certificate.configuration
    BY <1>target, <1>data, ConfigurationOccurrenceOnContainingPrefix, SMT
    DEF RetainedCommitCertificate, LatestConfigurationOccurrence
<1>owner. OwnerPrefix(certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>target, <1>data, SequencePrefixTransitive, SMT
    DEF RetainedCommitCertificate, OwnerPrefix, TypeOK, LogVarsTypeOK
<1> DEFINE reduced ==
        [leader |-> certificate.leader, term |-> certificate.term,
         entries |-> CommitTarget(certificate), index |-> certificate.index,
         snapshot |-> certificate.snapshot, electionOccurrence |-> certificate.electionOccurrence,
         election |-> certificate.election, configuration |-> certificate.configuration,
         replication |-> certificate.replication]
<1>same_target. CommitTarget(reduced) = CommitTarget(certificate)
    BY <1>target, WholeSequencePrefix, SMT DEF reduced, CommitTarget
<1>valid. RetainedCommitCertificate(voteHistory, reduced)
    BY <1>target, <1>data, <1>snapshot, <1>configuration, <1>owner, <1>same_target, SMT
    DEF RetainedCommitCertificate, reduced
<1> QED BY <1>valid, <1>target, SMT DEF reduced

LEMMA SupportedAgreementTargetClientRequest ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, SendInvariant, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW target \in Seq(LogEntry), SupportedAgreementTarget(voteHistory, target)
    PROVE SupportedAgreementTarget(nextVoteHistory, target)'
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(voteHistory, certificate)
        /\ certificate.entries = target /\ certificate.index = Len(target)
        /\ IsPrefix(target, log[certificate.leader])
    BY SMT DEF SupportedAgreementTarget
<1>source. certificate.leader \in Server /\ log[certificate.leader] \in Seq(LogEntry)
    BY <1>certificate, SMT DEF RetainedCommitCertificate, TypeOK, LogVarsTypeOK
<1>next. [Next]_vars BY SMT DEF Next
<1>retained. RetainedCommitCertificate(nextVoteHistory, certificate)'
    BY <1>certificate, <1>next, RetainedCommitCertificateNext, SMT
<1>prefix. IsPrefix(target, log'[certificate.leader])
    BY <1>certificate, <1>source, ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF ClientRequest, TypeOK, LogVarsTypeOK
<1> QED BY <1>certificate, <1>retained, <1>prefix, SMT DEF SupportedAgreementTarget

LEMMA LogPrefixSetProperties ==
    ASSUME NEW logs \in [Server -> Seq(LogEntry)]
    PROVE IsFiniteSet(LogPrefixSet(logs)) /\ LogPrefixSet(logs) \subseteq Seq(LogEntry)
<1>intervals. \A server \in Server: IsFiniteSet(0..Len(logs[server]))
    BY FS_Interval, LenProperties, SMT
<1>each. \A server \in Server:
        IsFiniteSet({SubSeq(logs[server], 1, cut): cut \in 0..Len(logs[server])})
    BY <1>intervals, FS_Image, Isa
<1>outer. IsFiniteSet(
        {{SubSeq(logs[server], 1, cut): cut \in 0..Len(logs[server])}: server \in Server})
    BY ServerOK, FS_Image, Isa
<1>finite. IsFiniteSet(LogPrefixSet(logs))
    BY <1>each, <1>outer, FS_UNION, SMT DEF LogPrefixSet
<1>typed. LogPrefixSet(logs) \subseteq Seq(LogEntry)
    BY SubSeqTypeOK, LenProperties, SMT DEF LogPrefixSet
<1> QED BY <1>finite, <1>typed, SMT

LEMMA PresentPrefixInLogPrefixSet ==
    ASSUME NEW logs \in [Server -> Seq(LogEntry)], NEW server \in Server,
           NEW prefix \in Seq(LogEntry), IsPrefix(prefix, logs[server])
    PROVE prefix \in LogPrefixSet(logs)
    BY LenProperties, SMT DEF LogPrefixSet, IsPrefix

LEMMA LatestConfigurationOccurrenceData ==
    ASSUME NEW entries \in Seq(LogEntry)
    PROVE ConfigurationOccurrenceData(LatestConfigurationOccurrence(entries))
<1>index. LastConfigChangeIndex(entries) \in 0..Len(entries)
    BY ConfigurationIndexProperties, SMT
<1>prefix.
        /\ SubSeq(entries, 1, LastConfigChangeIndex(entries)) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, 1, LastConfigChangeIndex(entries))) = LastConfigChangeIndex(entries)
        /\ IsPrefix(SubSeq(entries, 1, LastConfigChangeIndex(entries)), entries)
    BY <1>index, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1>same. LatestConfigurationOccurrence(SubSeq(entries, 1, LastConfigChangeIndex(entries))) =
               LatestConfigurationOccurrence(entries)
    BY <1>index, <1>prefix, ConfigurationOccurrenceOnContainingPrefix, SMT
<1> QED BY <1>prefix, <1>same, SMT
    DEF ConfigurationOccurrenceData, LatestConfigurationOccurrence

LEMMA InitialConfigurationOccurrenceData ==
    ConfigurationOccurrenceData(InitialConfigurationOccurrence)
<1>empty. LatestConfigurationOccurrence(<< >>) = InitialConfigurationOccurrence
    BY EmptySeq, ConfigurationIndexProperties, SubSeqEmpty, LenProperties, SMT
    DEF LatestConfigurationOccurrence, InitialConfigurationOccurrence, ConfigOf,
        LastConfigChangeIndex, ConfigChangeIndexes, MaxOrZero
<1> QED BY <1>empty, LatestConfigurationOccurrenceData, EmptySeq, SMT

LEMMA ConfigurationHistoryWellFormed ==
    ASSUME NEW targets \in SUBSET Seq(LogEntry), IsFiniteSet(targets)
    PROVE ConfigurationHistoryData(ConfigurationHistory(targets))
<1>image. IsFiniteSet({LatestConfigurationOccurrence(target): target \in targets})
    BY FS_Image, Isa
<1>finite. IsFiniteSet({LatestConfigurationOccurrence(target): target \in targets}
                          \cup {InitialConfigurationOccurrence})
    BY <1>image, FS_AddElement, SMT
<1>data. \A occurrence \in ConfigurationHistory(targets): ConfigurationOccurrenceData(occurrence)
    BY InitialConfigurationOccurrenceData, LatestConfigurationOccurrenceData, SMT
    DEF ConfigurationHistory
<1>same. ConfigurationHistory(targets) =
        {LatestConfigurationOccurrence(target): target \in targets} \cup {InitialConfigurationOccurrence}
    BY SMT DEF ConfigurationHistory
<1>nonempty. ConfigurationHistory(targets) # {}
    BY SMT DEF ConfigurationHistory
<1> QED BY <1>finite, <1>data, <1>same, <1>nonempty, SMT DEF ConfigurationHistoryData

LEMMA CompatibleOccurrenceOrder ==
    ASSUME NEW left, NEW right, ConfigurationOccurrenceData(left), ConfigurationOccurrenceData(right),
           left.index <= right.index,
           IsPrefix(left.prefix, right.prefix) \/ IsPrefix(right.prefix, left.prefix)
    PROVE IsPrefix(left.prefix, right.prefix)
    BY WholeSequencePrefix, PrefixesWithBoundedLength, LenProperties, SMT
    DEF ConfigurationOccurrenceData, IsPrefix

LEMMA CompatibleOccurrenceAtSameIndexEqual ==
    ASSUME NEW left, NEW right, ConfigurationOccurrenceData(left), ConfigurationOccurrenceData(right),
           left.index = right.index,
           IsPrefix(left.prefix, right.prefix) \/ IsPrefix(right.prefix, left.prefix)
    PROVE left = right
<1>prefix. IsPrefix(left.prefix, right.prefix)
    BY CompatibleOccurrenceOrder, LenProperties, SMT DEF ConfigurationOccurrenceData
<1>same. left.prefix = right.prefix
    BY <1>prefix, WholeSequencePrefix, LenProperties, SMT DEF ConfigurationOccurrenceData, IsPrefix
<1> QED BY <1>same, SMT DEF ConfigurationOccurrenceData

LEMMA LatestEvidenceOccurrenceProperties ==
    ASSUME NEW history, ConfigurationHistoryData(history)
    PROVE /\ LatestEvidenceOccurrence(history) \in history
          /\ ConfigurationOccurrenceData(LatestEvidenceOccurrence(history))
          /\ \A occurrence \in history:
                 occurrence.index <= LatestEvidenceOccurrence(history).index
<1>indexes.
        /\ IsFiniteSet({occurrence.index: occurrence \in history})
        /\ {occurrence.index: occurrence \in history} \subseteq Nat
        /\ {occurrence.index: occurrence \in history} # {}
    <2>finite. IsFiniteSet({occurrence.index: occurrence \in history})
        BY FS_Image, Isa DEF ConfigurationHistoryData
    <2>typed. {occurrence.index: occurrence \in history} \subseteq Nat
        BY LenProperties, SMT DEF ConfigurationHistoryData, ConfigurationOccurrenceData
    <2>nonempty. {occurrence.index: occurrence \in history} # {}
        BY SMT DEF ConfigurationHistoryData
    <2> QED BY <2>finite, <2>typed, <2>nonempty, SMT
<1>maximum. PICK maximum \in {occurrence.index: occurrence \in history}:
        \A index \in {occurrence.index: occurrence \in history}: index <= maximum
    BY <1>indexes, FiniteNaturalSetHasMaximum, SMT
<1>latest. PICK latest \in history: latest.index = maximum
    BY <1>maximum, SMT
<1>exists. \A occurrence \in history: occurrence.index <= latest.index
    BY <1>maximum, <1>latest, SMT
<1> QED BY <1>exists, SMT DEF LatestEvidenceOccurrence, ConfigurationHistoryData

LEMMA LatestCompatibleOccurrenceProperties ==
    ASSUME NEW history, ConfigurationHistoryData(history), ConfigurationHistoryCompatible(history)
    PROVE /\ \A occurrence \in history:
                 IsPrefix(occurrence.prefix, LatestEvidenceOccurrence(history).prefix)
          /\ \A occurrence \in history:
                 (\A other \in history: other.index <= occurrence.index)
                 => occurrence = LatestEvidenceOccurrence(history)
<1>latest.
        /\ LatestEvidenceOccurrence(history) \in history
        /\ ConfigurationOccurrenceData(LatestEvidenceOccurrence(history))
        /\ \A occurrence \in history: occurrence.index <= LatestEvidenceOccurrence(history).index
    BY LatestEvidenceOccurrenceProperties, SMT
<1>prefixes. \A occurrence \in history:
        IsPrefix(occurrence.prefix, LatestEvidenceOccurrence(history).prefix)
    BY <1>latest, CompatibleOccurrenceOrder, SMT
    DEF ConfigurationHistoryData, ConfigurationHistoryCompatible
<1>unique. \A occurrence \in history:
        (\A other \in history: other.index <= occurrence.index)
        => occurrence = LatestEvidenceOccurrence(history)
    <2> SUFFICES ASSUME NEW occurrence \in history,
                          \A other \in history: other.index <= occurrence.index
                 PROVE occurrence = LatestEvidenceOccurrence(history)
        BY SMT
    <2>index. occurrence.index = LatestEvidenceOccurrence(history).index
        BY <1>latest, LenProperties, SMT DEF ConfigurationHistoryData, ConfigurationOccurrenceData
    <2> QED BY <1>latest, <2>index, CompatibleOccurrenceAtSameIndexEqual, SMT
        DEF ConfigurationHistoryData, ConfigurationHistoryCompatible
<1> QED BY <1>prefixes, <1>unique, SMT

LEMMA EvidenceConfigurationHistoryWellFormed ==
    ASSUME NEW voteHistory
    PROVE TypeOK => ConfigurationHistoryData(EvidenceConfigurationHistory(voteHistory))
<1> SUFFICES ASSUME TypeOK PROVE ConfigurationHistoryData(EvidenceConfigurationHistory(voteHistory))
    BY SMT
<1>targets. IsFiniteSet(EvidenceAgreementTargets(voteHistory)) /\ EvidenceAgreementTargets(voteHistory) \subseteq Seq(LogEntry)
    BY LogPrefixSetProperties, FS_Subset, SMT
    DEF EvidenceAgreementTargets, TypeOK, LogVarsTypeOK
<1> QED BY <1>targets, ConfigurationHistoryWellFormed, SMT DEF EvidenceConfigurationHistory

LEMMA PrefixConfigurationIndexMonotonic ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry), IsPrefix(prefix, entries)
    PROVE LastConfigChangeIndex(prefix) <= LastConfigChangeIndex(entries)
BY PrefixEntryEqual, ConfigurationIndexProperties, LenProperties, PositiveIndexMaxOrZeroSubsetMonotone
DEF IsPrefix, ConfigChangeIndexes, LastConfigChangeIndex

LEMMA ConfigurationOccurrencePrefixIndex ==
    ASSUME NEW entries \in Seq(LogEntry)
    PROVE LastConfigChangeIndex(LatestConfigurationOccurrence(entries).prefix) =
              LatestConfigurationOccurrence(entries).index
<1>prefix.
        /\ LatestConfigurationOccurrence(entries).prefix \in Seq(LogEntry)
        /\ Len(LatestConfigurationOccurrence(entries).prefix) = LastConfigChangeIndex(entries)
        /\ IsPrefix(LatestConfigurationOccurrence(entries).prefix, entries)
    BY LatestConfigurationOccurrenceData, ConfigurationIndexProperties,
       SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF LatestConfigurationOccurrence, ConfigurationOccurrenceData, IsPrefix
<1>same. LatestConfigurationOccurrence(LatestConfigurationOccurrence(entries).prefix) =
               LatestConfigurationOccurrence(entries)
    BY <1>prefix, ConfigurationOccurrenceOnContainingPrefix, LenProperties, SMT
<1> QED BY <1>same, SMT DEF LatestConfigurationOccurrence

LEMMA EvidenceOccurrencePrefixIndex ==
    ASSUME NEW voteHistory, TypeOK, NEW occurrence \in EvidenceConfigurationHistory(voteHistory)
    PROVE LastConfigChangeIndex(occurrence.prefix) = occurrence.index
<1>initial. CASE occurrence = InitialConfigurationOccurrence
    BY <1>initial, EmptySeq, ConfigurationIndexProperties, LenProperties, SMT
    DEF InitialConfigurationOccurrence
<1>supported. CASE occurrence # InitialConfigurationOccurrence
    <2>target. PICK target \in EvidenceAgreementTargets(voteHistory):
            occurrence = LatestConfigurationOccurrence(target)
        BY <1>supported, SMT DEF EvidenceConfigurationHistory, ConfigurationHistory
    <2>typed. target \in Seq(LogEntry)
        BY <2>target, SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2> QED BY <2>target, <2>typed, ConfigurationOccurrencePrefixIndex, SMT
<1> QED BY <1>initial, <1>supported, SMT

LEMMA ConfigurationPrefixesOnPrefix ==
    ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry), IsPrefix(left, right)
    PROVE IsPrefix(LatestConfigurationOccurrence(left).prefix,
                   LatestConfigurationOccurrence(right).prefix)
<1>data.
        /\ ConfigurationOccurrenceData(LatestConfigurationOccurrence(left))
        /\ ConfigurationOccurrenceData(LatestConfigurationOccurrence(right))
        /\ LastConfigChangeIndex(left) <= LastConfigChangeIndex(right)
    BY LatestConfigurationOccurrenceData, PrefixConfigurationIndexMonotonic, SMT
<1>own.
        /\ IsPrefix(LatestConfigurationOccurrence(left).prefix, left)
        /\ IsPrefix(LatestConfigurationOccurrence(right).prefix, right)
    BY ConfigurationIndexProperties, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF LatestConfigurationOccurrence, IsPrefix
<1>both. IsPrefix(LatestConfigurationOccurrence(left).prefix, right)
    BY <1>data, <1>own, SequencePrefixTransitive, SMT DEF ConfigurationOccurrenceData
<1> QED BY <1>data, <1>own, <1>both, PrefixesWithBoundedLength, SMT
    DEF ConfigurationOccurrenceData, LatestConfigurationOccurrence

LEMMA ComparableTargetsGiveCompatibleConfigurations ==
    ASSUME NEW targets \in SUBSET Seq(LogEntry),
           \A left, right \in targets: IsPrefix(left, right) \/ IsPrefix(right, left)
    PROVE ConfigurationHistoryCompatible(ConfigurationHistory(targets))
<1>empty. \A occurrence \in ConfigurationHistory(targets):
        IsPrefix(InitialConfigurationOccurrence.prefix, occurrence.prefix)
    BY InitialConfigurationOccurrenceData, LatestConfigurationOccurrenceData,
       EmptySeq, SubSeqEmpty, LenProperties, SMT
    DEF ConfigurationHistory, InitialConfigurationOccurrence, ConfigurationOccurrenceData, IsPrefix
<1> SUFFICES ASSUME NEW left \in ConfigurationHistory(targets),
                      NEW right \in ConfigurationHistory(targets)
             PROVE IsPrefix(left.prefix, right.prefix) \/ IsPrefix(right.prefix, left.prefix)
    BY SMT DEF ConfigurationHistoryCompatible
<1>initial. CASE left = InitialConfigurationOccurrence \/ right = InitialConfigurationOccurrence
    BY <1>initial, <1>empty, SMT
<1>targets. CASE left # InitialConfigurationOccurrence /\ right # InitialConfigurationOccurrence
    <2>chosen. PICK first \in targets, second \in targets:
            /\ left = LatestConfigurationOccurrence(first)
            /\ right = LatestConfigurationOccurrence(second)
        BY <1>targets, SMT DEF ConfigurationHistory
    <2> QED BY <2>chosen, ConfigurationPrefixesOnPrefix, SMT
<1> QED BY <1>initial, <1>targets, SMT

\* A higher-term tip is an ancestry witness to containment. For equal terms,
\* ordered creator prefixes supply comparability in either length direction.
LEMMA ExistingBoundaryComparesNewerPrefix ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           NEW target \in Seq(LogEntry), NEW entries \in Seq(LogEntry),
           Len(target) > 0, Len(entries) > 0,
           CoveredPrefix(family, target), CoveredPrefix(family, entries),
           LaterTermPrefixProtection(family, target, LastTerm(target)),
           LastTerm(target) <= LastTerm(entries)
    PROVE /\ IsPrefix(target, entries) \/ IsPrefix(entries, target)
          /\ (LastTerm(target) < LastTerm(entries) => IsPrefix(target, entries))
<1>types.
        /\ LastTerm(target) \in Nat /\ LastTerm(entries) \in Nat
        /\ Len(target) \in Nat /\ Len(entries) \in Nat
    BY LastTermTypeOK, LenProperties, SMT
<1>equal. CASE LastTerm(target) = LastTerm(entries)
    BY <1>equal, <1>types, CoveredSequencesWithSameLastTermAreOrdered, SMT
<1>higher. CASE LastTerm(target) < LastTerm(entries)
    <2>consistent. WitnessEdgeConsistency(family)
        BY OrderedTermPrefixesAreEdgeConsistent, SMT
    <2>tip. PICK witness \in family:
            /\ witness.prefix = entries
            /\ witness.edge.index = Len(entries)
            /\ witness.edge.term = LastTerm(entries)
        BY <2>consistent, CoveredSequenceHasLastWitness, SMT
    <2> QED BY <1>higher, <2>tip, SMT DEF LaterTermPrefixProtection
<1> QED BY <1>types, <1>equal, <1>higher, SMT

LEMMA HistoricalAgreementTargetsAreComparable ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           NEW targets, AgreementTargetBoundaries(family, targets)
    PROVE \A left, right \in targets: IsPrefix(left, right) \/ IsPrefix(right, left)
    BY ExistingBoundaryComparesNewerPrefix, LastTermTypeOK, SMT DEF AgreementTargetBoundaries

LEMMA HistoricalAgreementConfigurationsAreCompatible ==
    ASSUME NEW voteHistory, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           NEW targets, AgreementTargetBoundaries(family, targets)
    PROVE ConfigurationHistoryCompatible(ConfigurationHistory(targets))
    BY HistoricalAgreementTargetsAreComparable, ComparableTargetsGiveCompatibleConfigurations, SMT
    DEF AgreementTargetBoundaries

LEMMA EvidenceTargetsAreCovered ==
    ASSUME NEW voteHistory, TypeOK, NEW family, CoversEntryEdges(family, HistoricalEntryEdges)
    PROVE \A target \in EvidenceAgreementTargets(voteHistory):
              /\ target \in Seq(LogEntry) /\ Len(target) > 0
              /\ CoveredPrefix(family, target)
<1> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory)
             PROVE /\ target \in Seq(LogEntry) /\ Len(target) > 0
                   /\ CoveredPrefix(family, target)
    BY SMT
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(voteHistory, certificate)
        /\ certificate.entries = target /\ certificate.index = Len(target)
        /\ IsPrefix(target, log[certificate.leader])
    BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
<1>data.
        /\ target \in Seq(LogEntry) /\ Len(target) > 0
        /\ certificate.leader \in Server
        /\ log[certificate.leader] \in Seq(LogEntry)
    BY <1>certificate, LenProperties, SMT DEF RetainedCommitCertificate, TypeOK, LogVarsTypeOK
<1> QED BY <1>certificate, <1>data, CurrentLogPrefixCovered, SMT

LEMMA EvidenceHistoryCompatibleFromHistoricalBoundaries ==
    ASSUME NEW voteHistory, TypeOK, NEW family, CertificateFamily(voteHistory, family), TermPrefixOrder(family),
           CoversEntryEdges(family, HistoricalEntryEdges),
           \A target \in EvidenceAgreementTargets(voteHistory):
               LaterTermPrefixProtection(family, target, LastTerm(target))
    PROVE ConfigurationHistoryCompatible(EvidenceConfigurationHistory(voteHistory))
<1>boundaries. AgreementTargetBoundaries(family, EvidenceAgreementTargets(voteHistory))
    BY EvidenceTargetsAreCovered, SMT DEF AgreementTargetBoundaries
<1> QED BY <1>boundaries, HistoricalAgreementConfigurationsAreCompatible, SMT
    DEF EvidenceConfigurationHistory

LEMMA BoundedPrefixOnAppendReverse ==
    ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
           NEW prefix \in Seq(LogEntry), IsPrefix(prefix, Append(entries, entry)),
           Len(prefix) <= Len(entries)
    PROVE IsPrefix(prefix, entries)
    BY AppendPreservesSequencePrefix, LenProperties, SMT DEF IsPrefix

LEMMA PresentPrefixBeforeClientAppend ==
    ASSUME TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW leader \in Server,
           NEW prefix \in Seq(LogEntry), IsPrefix(prefix, log'[leader]),
           leader = actor => Len(prefix) <= Len(log[actor])
    PROVE IsPrefix(prefix, log[leader])
<1>same. CASE leader = actor
    <2>entry. PICK entry \in LogEntry: log'[actor] = Append(log[actor], entry)
        BY ClientRequestAppendsCurrentTerm, SMT
    <2> QED BY <1>same, <2>entry, BoundedPrefixOnAppendReverse, SMT
        DEF TypeOK, LogVarsTypeOK
<1>other. CASE leader # actor
    BY <1>other, SMT DEF ClientRequest, TypeOK, LogVarsTypeOK
<1> QED BY <1>same, <1>other, SMT

LEMMA BoundedOwnerPrefixBeforeClientAppend ==
    ASSUME TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW leader \in Server, NEW term \in Nat,
           NEW prefix \in Seq(LogEntry), OwnerPrefix(leader, term, prefix)',
           leader = actor => Len(prefix) <= Len(log[actor])
    PROVE OwnerPrefix(leader, term, prefix)
<1>bound. term <= currentTerm[leader]
    BY SMT DEF OwnerPrefix, ClientRequest
<1> SUFFICES ASSUME currentTerm[leader] = term, state[leader] \in {Candidate, Leader}
             PROVE IsPrefix(prefix, log[leader])
    BY <1>bound, SMT DEF OwnerPrefix
<1>post. IsPrefix(prefix, log'[leader])
    BY SMT DEF OwnerPrefix, ClientRequest
<1> QED BY <1>post, PresentPrefixBeforeClientAppend, SMT

\* Request index bounds prevent appending a fresh entry from making an old,
\* longer RPC prefix newly valid in the sender's current term.
LEMMA RequestOwnerPrefixBeforeClientAppend ==
    ASSUME ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW request \in AppendRequests,
           NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix),
           OwnerPrefix(request.msource, request.mterm, prefix)'
    PROVE OwnerPrefix(request.msource, request.mterm, prefix)
<1>base.
        /\ TypeOK /\ request.msource \in Server /\ request.mterm \in Nat
        /\ log[actor] \in Seq(LogEntry)
    BY MessageFieldsTypeOK, SMT
    DEF ReplicationBoundsInv, TypeOK, MsgTypeOK, LogVarsTypeOK, AppendRequests
<1>bound. request.mterm <= currentTerm[request.msource]
    BY SMT DEF OwnerPrefix, ClientRequest
<1> SUFFICES ASSUME currentTerm[request.msource] = request.mterm,
                      state[request.msource] \in {Candidate, Leader}
             PROVE IsPrefix(prefix, log[request.msource])
    BY <1>bound, SMT DEF OwnerPrefix
<1>post. IsPrefix(prefix, log'[request.msource])
    BY SMT DEF OwnerPrefix, ClientRequest
<1>length. request.msource = actor => Len(prefix) <= Len(log[actor])
    BY SMT DEF ReplicationBoundsInv, RequestIndexBound, RequestPrefixData, AppendRequests
<1> QED BY <1>base, <1>post, <1>length, PresentPrefixBeforeClientAppend, SMT

LEMMA PrefixAcknowledgmentBeforeClientAppend ==
    ASSUME ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW peer \in Server, NEW leader \in Server,
           NEW term \in Nat, NEW target \in Seq(LogEntry),
           RecordedPrefixAcknowledgment(peer, leader, term, target)'
    PROVE RecordedPrefixAcknowledgment(peer, leader, term, target)
<1>prefix. PICK response, request, prefix:
        /\ response \in messages /\ request \in messages /\ prefix \in Seq(LogEntry)
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = peer /\ response.mdest = leader
        /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        /\ ResponseMatchesRequest(response, request)
        /\ RequestPrefixData(request, prefix)
        /\ OwnerPrefix(leader, term, prefix)'
        /\ IsPrefix(target, prefix)
    BY SMT DEF RecordedPrefixAcknowledgment, ClientRequest
<1>owner. OwnerPrefix(leader, term, prefix)
    BY <1>prefix, RequestOwnerPrefixBeforeClientAppend, SMT
    DEF ResponseMatchesRequest, AppendRequests
<1> QED BY <1>prefix, <1>owner, SMT DEF RecordedPrefixAcknowledgment

LEMMA ElectionCertificateMessagesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), CampaignView(nextVoteHistory) = CampaignView(voteHistory), UNCHANGED messages, NEW leader, NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
<1>histories. CampaignHistory(voteHistory) /\ CampaignHistory(nextVoteHistory)'
    BY SMT DEF CampaignHistoryContextStep
<1>snapshots. HistoryCampaignSnapshot(nextVoteHistory, leader, term, snapshot)
        <=> HistoryCampaignSnapshot(voteHistory, leader, term, snapshot)
    BY CampaignSnapshotInView, SMT
<1>started. Started(nextVoteHistory, leader, term)' <=> Started(voteHistory, leader, term)
    BY CampaignViewFramesStarted, Zenon
<1> QED BY <1>histories, <1>snapshots, <1>started, SMT
    DEF RetainedElectionCertificate, RecordedCampaignRequests, VoteSupport, VoteFor, Grant

LEMMA ElectionCertificateMessagesRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           UNCHANGED messages, NEW leader, NEW term, NEW snapshot, NEW occurrence, NEW support,
           RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    PROVE RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
<1>history. CampaignHistory(nextVoteHistory)'
    BY SMT DEF CampaignHistoryContextStep
<1>snapshot. HistoryCampaignSnapshot(nextVoteHistory, leader, term, snapshot)
    BY CampaignHistoryContextMonotone, SMT
    DEF RetainedElectionCertificate, HistoryCampaignSnapshot
<1>start. HistoryStarted(nextVoteHistory, leader, term)
    BY <1>snapshot, SMT DEF HistoryStarted, HistoryCampaignSnapshot
<1>rule. CampaignHistoryStartConsequence'
    BY CampaignHistoryStartRule, PTL
<1>started. Started(nextVoteHistory, leader, term)'
    BY <1>history, <1>start, <1>rule, SMT DEF CampaignHistoryStartConsequence
<1> QED BY <1>history, <1>snapshot, <1>started, SMT
    DEF RetainedElectionCertificate, RecordedCampaignRequests, VoteSupport, VoteFor, Grant

LEMMA ExistingTermElectionCertificateMessagesFrame ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), UNCHANGED messages,
           NEW leader \in Server, NEW term \in Nat, term <= currentTerm[leader],
           NEW snapshot, NEW occurrence, NEW support
    PROVE RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
<1>before. HistoryCampaignSnapshot(nextVoteHistory, leader, term, snapshot)
    => HistoryCampaignSnapshot(voteHistory, leader, term, snapshot)
    BY ExistingTermCampaignSnapshotBeforeStep, SMT
<1>after. HistoryCampaignSnapshot(voteHistory, leader, term, snapshot)
    => HistoryCampaignSnapshot(nextVoteHistory, leader, term, snapshot)
    BY CampaignHistoryContextMonotone, SMT DEF HistoryCampaignSnapshot
<1> QED BY <1>before, <1>after, SMT
    DEF RetainedElectionCertificate, RecordedCampaignRequests, VoteSupport, VoteFor, Grant,
        Started, HistoryCampaignSnapshot, CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord

LEMMA CommitCertificateBeforeClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)',
           certificate.leader = actor => Len(certificate.entries) <= Len(log[actor])
    PROVE RetainedCommitCertificate(voteHistory, certificate)
<1>base. TypeOK
    BY SMT DEF ReplicationBoundsInv
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry) /\ certificate.snapshot \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>owner. OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    BY <1>base, <1>data, BoundedOwnerPrefixBeforeClientAppend, SMT DEF RetainedCommitCertificate
<1>election. RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
        certificate.snapshot, certificate.electionOccurrence, certificate.election)
    BY <1>base, ClientRequestKeepsSelectedCampaignHistory, ElectionCertificateMessagesFrame, SMT DEF RetainedCommitCertificate, ClientRequest
<1>target. /\ CommitTarget(certificate) \in Seq(LogEntry)
           /\ Len(CommitTarget(certificate)) = certificate.index
           /\ certificate.index \in DOMAIN CommitTarget(certificate)
           /\ CommitTarget(certificate)[certificate.index].term = certificate.term
           /\ IsPrefix(CommitTarget(certificate), certificate.entries)
    BY <1>data, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF RetainedCommitCertificate, CommitTarget, IsPrefix
<1>acks. \A peer \in certificate.replication \ {certificate.leader}:
        RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>data, <1>target, PrefixAcknowledgmentBeforeClientAppend, SMT
    DEF RetainedCommitCertificate, Quorums
<1>origin. certificate.replication \subseteq {certificate.leader} =>
        LocalAppendOrigin(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
    <2> SUFFICES ASSUME certificate.replication \subseteq {certificate.leader}
                 PROVE LocalAppendOrigin(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
        BY SMT
    <2>record. PICK record \in nextVoteHistory:
            /\ LocalAppendRecord(record) /\ record.candidate = certificate.leader
            /\ record.term = certificate.term /\ record.prefix \in Seq(LogEntry)
            /\ IsPrefix(CommitTarget(certificate), record.prefix)
        BY SMT DEF RetainedCommitCertificate, LocalAppendOrigin
    <2>old. CASE record \in voteHistory
        BY <2>old, <2>record, SMT DEF LocalAppendOrigin
    <2>new. CASE record \notin voteHistory
        <3>actor. certificate.leader = actor /\ certificate.term = currentTerm[actor]
            BY <2>record, <2>new, SMT DEF CampaignHistoryContextStep, CampaignHistoryStep
        <3>held. IsPrefix(CommitTarget(certificate), log[actor])
            BY <1>base, <1>target, <1>owner, <3>actor, CommitCertificateTargetProperties,
               SequencePrefixTransitive, SMT
            DEF OwnerPrefix, RetainedCommitCertificate, ClientRequest, TypeOK, LogVarsTypeOK
        <3>entry. certificate.index \in DOMAIN log[actor] /\ log[actor][certificate.index].term = currentTerm[actor]
            BY <1>base, <1>target, <3>actor, <3>held, PrefixEntryEqual, LenProperties, SMT
            DEF IsPrefix, TypeOK, LogVarsTypeOK
        <3>whole. LocalAppendOrigin(voteHistory, actor, currentTerm[actor], log[actor])
            BY <3>entry, SMT
            DEF CampaignHistoryContextStep, CampaignHistory, LocalAppendCoverage, ClientRequest
        <3> QED BY <1>base, <1>target, <3>actor, <3>held, <3>whole, SequencePrefixTransitive
            DEF TypeOK, LogVarsTypeOK, LocalAppendOrigin
    <2> QED BY <2>old, <2>new, SMT
<1> QED BY <1>owner, <1>election, <1>acks, <1>origin, SMT DEF RetainedCommitCertificate

LEMMA QuorumContainedInSelfIsSingleton ==
    ASSUME NEW config \in SUBSET Server, NEW actor \in Server,
           NEW support \in Quorums(config), support \subseteq {actor}
    PROVE config = {actor} /\ support = {actor}
<1>support. support = {actor}
    BY ConfigurationQuorumNonempty, SMT
<1>sizes. IsFiniteSet(config) /\ support \subseteq config /\ Cardinality(config) \in Nat
          /\ Cardinality(config) < 2 /\ Cardinality(config) >= 1 /\ Cardinality(support) = 1
    BY <1>support, ConfigurationQuorumProperties, ServerOK, FiniteSetSubsetsAreFinite,
       FS_Singleton, FS_Subset, SMT
<1> QED BY <1>support, <1>sizes, FS_Subset, SMT

LEMMA FreshAppendAgreementRequiresSingleton ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW target \in Seq(LogEntry), NEW certificate,
           RetainedCommitCertificate(nextVoteHistory, certificate)', certificate.leader = actor,
           certificate.entries = target, certificate.index = Len(target),
           IsPrefix(target, log'[actor]), Len(target) > Len(log[actor])
    PROVE ConfigOf(log'[actor]) = {actor} /\ target = log'[actor]
<1>base.
        /\ TypeOK /\ log[actor] \in Seq(LogEntry)
        /\ Len(log[actor]) \in Nat /\ Len(target) \in Nat
        /\ currentTerm[actor] \in Nat
    BY LenProperties, SMT DEF ReplicationBoundsInv, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>entry. PICK entry \in LogEntry:
        /\ log'[actor] = Append(log[actor], entry)
        /\ entry.term = currentTerm[actor]
    BY <1>base, ClientRequestAppendsCurrentTerm, SMT
<1>post_log.
        /\ log'[actor] \in Seq(LogEntry)
        /\ Len(log'[actor]) = Len(log[actor]) + 1
    BY <1>base, <1>entry, AppendProperties, LenProperties, SMT
<1>length. Len(target) = Len(log[actor]) + 1 /\ target = log'[actor]
    BY <1>base, <1>post_log, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
<1>term. certificate.term = currentTerm[actor]
    BY <1>base, <1>entry, <1>length, AppendProperties, LenProperties, SMT
    DEF RetainedCommitCertificate
<1>support. RecordedReplicationSupport(actor, certificate.term, certificate.index)' = {actor}
    BY <1>base, <1>length, <1>term, ClientAppendHasOnlySelfRecordedSupport, SMT
<1>recorded. CommitCertificateRecordedSupport'
    BY CommitCertificateSuppliesRecordedSupport, PTL
<1>configuration.
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>replication. certificate.replication \subseteq {actor}
    BY <1>support, <1>recorded, SMT DEF CommitCertificateRecordedSupport
<1>singleton. certificate.configuration.members = {actor}
    BY <1>configuration, <1>replication, QuorumContainedInSelfIsSingleton, SMT
<1> QED BY <1>length, <1>singleton, SMT DEF RetainedCommitCertificate, LatestConfigurationOccurrence

LEMMA SupportedAgreementTargetBeforeOrFresh ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW target \in Seq(LogEntry), SupportedAgreementTarget(nextVoteHistory, target)'
    PROVE SupportedAgreementTarget(voteHistory, target)
          \/ (target = log'[actor] /\ ConfigOf(log'[actor]) = {actor})
<1>base. TypeOK /\ Len(target) \in Nat /\ Len(log[actor]) \in Nat
    BY LenProperties, SMT DEF ReplicationBoundsInv, TypeOK, LogVarsTypeOK
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
        /\ certificate.entries = target /\ certificate.index = Len(target)
        /\ IsPrefix(target, log'[certificate.leader])
    BY SMT DEF SupportedAgreementTarget
<1>source. certificate.leader \in Server
    BY <1>certificate, SMT DEF RetainedCommitCertificate
<1>fresh. CASE certificate.leader = actor /\ Len(target) > Len(log[actor])
    BY <1>certificate, <1>fresh, FreshAppendAgreementRequiresSingleton, SMT
<1>old. CASE ~(certificate.leader = actor /\ Len(target) > Len(log[actor]))
    <2>bound. certificate.leader = actor => Len(target) <= Len(log[actor])
        BY <1>base, <1>old, SMT
    <2>before. RetainedCommitCertificate(voteHistory, certificate)
        BY <1>certificate, <2>bound, CommitCertificateBeforeClientAppend, SMT
    <2>prefix. IsPrefix(target, log[certificate.leader])
        BY <1>base, <1>source, <1>certificate, <2>bound, PresentPrefixBeforeClientAppend, SMT
    <2> QED BY <1>certificate, <2>before, <2>prefix, SMT DEF SupportedAgreementTarget
<1> QED BY <1>fresh, <1>old, SMT

LEMMA SupportedAgreementTargetBeforeClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           ReplicationBoundsInv, NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload),
           ConfigOf(log'[actor]) # {actor}, NEW target \in Seq(LogEntry), SupportedAgreementTarget(nextVoteHistory, target)'
    PROVE SupportedAgreementTarget(voteHistory, target)
    BY SupportedAgreementTargetBeforeOrFresh, SMT

LEMMA SupportedTargetInEvidenceSet ==
    ASSUME NEW voteHistory, TypeOK, NEW target \in Seq(LogEntry), SupportedAgreementTarget(voteHistory, target)
    PROVE target \in EvidenceAgreementTargets(voteHistory)
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(voteHistory, certificate)
        /\ IsPrefix(target, log[certificate.leader])
    BY SMT DEF SupportedAgreementTarget
<1>present. target \in LogPrefixSet(log)
    BY <1>certificate, PresentPrefixInLogPrefixSet, SMT
    DEF RetainedCommitCertificate, TypeOK, LogVarsTypeOK
<1> QED BY <1>present, SMT DEF EvidenceAgreementTargets

\* Outside the singleton branch, a fresh index still needs a peer's support.
LEMMA ClientAppendPreservesEvidenceTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), ConfigOf(log'[actor]) # {actor}
    PROVE EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
<1>base. TypeOK /\ SendInvariant /\ ReplicationBoundsInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, EntryEdgeBase
<1>next. [Next]_vars BY SMT DEF Next
<1>post. TypeOK'
    BY <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>forward. EvidenceAgreementTargets(voteHistory) \subseteq EvidenceAgreementTargets(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory) PROVE target \in EvidenceAgreementTargets(nextVoteHistory)'
        BY SMT
    <2>target. target \in Seq(LogEntry) /\ SupportedAgreementTarget(voteHistory, target)
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>supported. SupportedAgreementTarget(nextVoteHistory, target)'
        BY <1>base, <2>target, SupportedAgreementTargetClientRequest, SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
            /\ IsPrefix(target, log'[certificate.leader])
        BY <2>supported, SMT DEF SupportedAgreementTarget
    <2>present. target \in LogPrefixSet(log')
        BY <1>post, <2>target, <2>certificate, PresentPrefixInLogPrefixSet, SMT
        DEF RetainedCommitCertificate, TypeOK, LogVarsTypeOK
    <2> QED BY <2>supported, <2>present, SMT DEF EvidenceAgreementTargets
<1>reverse. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory)
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)' PROVE target \in EvidenceAgreementTargets(voteHistory)
        BY SMT
    <2>target. target \in Seq(LogEntry) /\ SupportedAgreementTarget(nextVoteHistory, target)'
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>supported. SupportedAgreementTarget(voteHistory, target)
        BY <1>base, <2>target, SupportedAgreementTargetBeforeClientAppend, SMT
    <2> QED BY <1>base, <2>target, <2>supported, SupportedTargetInEvidenceSet, SMT
<1> QED BY <1>forward, <1>reverse, SMT

LEMMA ClientAppendEvidenceTargetsGrowOnlyAtFreshPrefix ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
    PROVE /\ EvidenceAgreementTargets(voteHistory) \subseteq EvidenceAgreementTargets(nextVoteHistory)'
          /\ EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory) \cup {log'[actor]}
<1>base. TypeOK /\ SendInvariant /\ ReplicationBoundsInv /\ TypeOK'
    BY CampaignsSupplyEntryBounds, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, MembershipCampaignsInv,
        MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv, EntryEdgeBase, Next
<1>before. EvidenceAgreementTargets(voteHistory) \subseteq EvidenceAgreementTargets(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory)
                 PROVE target \in EvidenceAgreementTargets(nextVoteHistory)' BY SMT
    <2>supported. target \in Seq(LogEntry) /\ SupportedAgreementTarget(nextVoteHistory, target)'
        BY <1>base, SupportedAgreementTargetClientRequest, SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>certificate. PICK certificate: RetainedCommitCertificate(nextVoteHistory, certificate)' /\ IsPrefix(target, log'[certificate.leader])
        BY <2>supported, SMT DEF SupportedAgreementTarget
    <2>present. target \in LogPrefixSet(log')
        BY <1>base, <2>supported, <2>certificate, PresentPrefixInLogPrefixSet, SMT
        DEF RetainedCommitCertificate, TypeOK, LogVarsTypeOK
    <2> QED BY <2>supported, <2>present, SMT DEF EvidenceAgreementTargets
<1>after. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory) \cup {log'[actor]}
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)'
                 PROVE target \in EvidenceAgreementTargets(voteHistory) \cup {log'[actor]} BY SMT
    <2>origin. target \in Seq(LogEntry) /\ (SupportedAgreementTarget(voteHistory, target) \/ target = log'[actor])
        BY <1>base, SupportedAgreementTargetBeforeOrFresh, SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2> QED BY <1>base, <2>origin, SupportedTargetInEvidenceSet, SMT
<1> QED BY <1>before, <1>after, SMT

LEMMA SingletonAppendAddsFreshEvidenceTarget ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), ConfigOf(log'[actor]) = {actor}
    PROVE log'[actor] \in EvidenceAgreementTargets(nextVoteHistory)'
<1>base. TypeOK /\ TypeOK' /\ MembershipCampaignsInv(voteHistory)
    BY CampaignsSupplyEntryBounds, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, MembershipCampaignsInv,
        MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv, EntryEdgeBase, Next
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(nextVoteHistory, certificate)' /\ certificate.leader = actor
        /\ certificate.entries = log'[actor] /\ certificate.index = Len(log'[actor])
    BY <1>base, SingletonAppendCreatesRetainedCommitCertificate, SMT
<1>target. PICK target \in Seq(LogEntry): target = log'[actor]
    BY <1>base, SMT DEF TypeOK, LogVarsTypeOK
<1>supported. SupportedAgreementTarget(nextVoteHistory, target)'
    BY <1>certificate, <1>target, WholeSequencePrefix, LenProperties, SMT DEF SupportedAgreementTarget, IsPrefix
<1>present. target \in LogPrefixSet(log')
    BY <1>base, <1>target, PresentPrefixInLogPrefixSet, WholeSequencePrefix, LenProperties, SMT
    DEF IsPrefix, TypeOK, LogVarsTypeOK
<1> QED BY <1>supported, <1>present, <1>target, SMT DEF EvidenceAgreementTargets

LEMMA ClientAppendEvidenceTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
    PROVE EvidenceAgreementTargets(nextVoteHistory)' =
              EvidenceAgreementTargets(voteHistory) \cup (IF ConfigOf(log'[actor]) = {actor} THEN {log'[actor]} ELSE {})
    BY ClientAppendEvidenceTargetsGrowOnlyAtFreshPrefix, SingletonAppendAddsFreshEvidenceTarget,
       ClientAppendPreservesEvidenceTargets, SMT

=======================================================================
