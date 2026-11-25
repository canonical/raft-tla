------------------------------ MODULE proof_evidence_admission ------------------------------
\* proof_evidence_admission.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_joint_core, proof_exclusion

LOCAL INSTANCE NaturalsInduction

CausalCampaignRecords(voteHistory, ancestry, campaigns) ==
    \A campaign \in campaigns: CausalCampaignData(voteHistory, ancestry, campaign)

TargetWireEvidence(voteHistory, ancestry, leader, term, target) ==
    \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
        /\ request.msource = leader /\ request.mterm = term
        /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ RequestCampaignBoundary(voteHistory, request, prefix) /\ Len(target) <= Len(prefix)

TargetLocalEvidence(voteHistory, ancestry, leader, term, target) ==
    /\ LocalAppendRequestOwnersUnique(voteHistory)
    /\ \E record \in voteHistory: \E witness \in ancestry:
           /\ LocalAppendRecord(record) /\ record.candidate = leader /\ record.term = term
           /\ record.prefix \in Seq(LogEntry) /\ IsPrefix(target, record.prefix)
           /\ CoveredPrefix(ancestry, record.prefix)
           /\ witness.prefix = record.prefix /\ witness.owner = leader /\ witness.edge.term = term
           /\ witness.snapshot = record.snapshot

TargetRequestEvidence(voteHistory, ancestry, leader, term, target) ==
    TargetWireEvidence(voteHistory, ancestry, leader, term, target)
    \/ TargetLocalEvidence(voteHistory, ancestry, leader, term, target)

CampaignTargetVotingCuts(target, term, support, campaigns) ==
    \A campaign \in campaigns:
        /\ term < campaign.term /\ support \cap campaign.support # {}
        => SnapshotCoversPrefix(campaign.snapshot, target)
           \/ \E peer \in Server: EarlierConflictingRequest(peer, term, campaign.term, target)

MixedRecordedTargetCampaignIntersections(leader, term, target, support, campaigns) ==
    \A campaign \in campaigns: term < campaign.term =>
        \A peer \in support \cap campaign.support: peer # leader =>
            \E response \in messages:
                /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
                /\ response.mterm = term /\ response.mmatchIndex >= Len(target)

SameTermEstablishedPrefix(commits, target, term) ==
    \E certificate \in commits: certificate.term = term /\ IsPrefix(target, CommitTarget(certificate))

ReadyTargetPrefix(voteHistory, target, term) ==
    \A candidate \in Server: \A later \in Nat: \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ ReadyElectionCertificate(voteHistory, candidate, later, snapshot, occurrence, support) /\ term <= later
        => IsPrefix(target, log[candidate])

\* Agreement ready for local commitment is derived from retained replication
\* responses. Fresh potential support is a separate, still open blocking family.
\* Neither this support nor the target predicate reads local commitIndex.
RecordedAgreementSupport(leader, term, target) ==
    {peer \in Server:
        \/ peer = leader /\ IsPrefix(target, log[leader])
        \/ RecordedPrefixAcknowledgment(peer, leader, term, target)}

PendingAgreement(leader, term, target) ==
    /\ leader \in Server /\ term \in Nat /\ target \in Seq(LogEntry)
    /\ state[leader] = Leader /\ term = currentTerm[leader]
    /\ Len(target) > 0 /\ LastTerm(target) = term
    /\ IsPrefix(target, log[leader])
    /\ ConfigOf(log[leader]) \in (SUBSET Server) \ { {} }
    /\ \E support \in Quorums(ConfigOf(log[leader])):
           support \subseteq RecordedAgreementSupport(leader, term, target)

EligibleCampaignsProtectTarget(voteHistory, target, term) ==
    \A candidate \in Server: \A campaignTerm \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        /\ OpportunityCertificate(voteHistory, candidate, campaignTerm, snapshot, occurrence, support)
        /\ term <= campaignTerm
        => IsPrefix(target, log[candidate])

PendingTargetProtection(voteHistory, ancestry, leader, term, target) ==
    /\ LaterTermPrefixProtection(ancestry, target, term)
    /\ ProtectedAppendRequests(target, term) /\ ProtectedLeaders(target, term)
    /\ RecordedAcknowledgersProtected(leader, term, target)
    /\ EligibleCampaignsProtectTarget(voteHistory, target, term)

JointPendingProtection(voteHistory, ancestry) ==
    \A leader \in Server: \A term \in Nat: \A target \in Seq(LogEntry):
        PendingAgreement(leader, term, target)
        => PendingTargetProtection(voteHistory, ancestry, leader, term, target)

\* Fixed logs and election evidence can only lose eligibility when epochs
\* advance. Future snapshots already include servers that can step down.
OpportunityRetirementFrame ==
    /\ UNCHANGED log /\ ElectionMessagesFrame /\ ActiveCampaignsRetire
    /\ \A server \in Server:
           /\ currentTerm[server] <= currentTerm'[server]
           /\ (currentTerm'[server] = currentTerm[server]
               => votedFor'[server] = votedFor[server])

AllLogsExtend == \A server \in Server: IsPrefix(log[server], log'[server])


ReplicationMessagesFrame ==
    /\ AppendRequests' = AppendRequests
    /\ {response \in messages': SuccessfulAppendResponse(response)}
         = {response \in messages: SuccessfulAppendResponse(response)}

PendingEvidenceFrame ==
    /\ UNCHANGED log /\ ReplicationMessagesFrame /\ ContinuingLeadersKeepLogs
    /\ \A server \in Server: currentTerm[server] <= currentTerm'[server]

CurrentCausalCampaigns(campaigns) ==
    \A leader \in Server: state[leader] = Leader => \E campaign \in campaigns:
        /\ campaign.candidate = leader /\ campaign.term = currentTerm[leader]
        /\ campaign.snapshot = CampaignPrefix(log[leader], currentTerm[leader])

CampaignPendingPrefixes(campaigns) ==
    \A leader \in Server: \A term \in Nat: \A target \in Seq(LogEntry):
        PendingAgreement(leader, term, target) =>
            \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)

CausalHistoryData(voteHistory, ancestry, commits, campaigns) ==
    /\ IsFiniteSet(campaigns)
    /\ AppendRequestOwnersUnique
    /\ LocalAppendRequestOwnersUnique(voteHistory)
    /\ LocalAppendPrefixHistory(voteHistory) /\ LocalAppendVoteCutHistory(voteHistory)
    /\ RequestSourcePrefixHistory(ancestry) /\ RequestSourceVoteCutHistory(voteHistory, ancestry)
    /\ FrozenRequestPrefixesAgree(ancestry)
    /\ FrozenAcknowledgmentPrefixHistory(ancestry)
    /\ FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry)
    /\ CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns)
    /\ CurrentCausalCampaigns(campaigns)

CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns) ==
    /\ IsFiniteSet(campaigns)
    /\ AppendRequestOwnersUnique
    /\ LocalAppendRecordsCovered(voteHistory, ancestry) /\ LocalAppendRequestOwnersUnique(voteHistory)
    /\ LocalAppendPrefixHistory(voteHistory) /\ LocalAppendVoteCutHistory(voteHistory)
    /\ RequestSourcePrefixHistory(ancestry) /\ RequestSourceVoteCutHistory(voteHistory, ancestry)
    /\ FrozenRequestPrefixesAgree(ancestry)
    /\ FrozenAcknowledgmentPrefixHistory(ancestry)
    /\ FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry)
    /\ CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns)
    /\ CurrentCausalCampaigns(campaigns)

LEMMA OwnedCommitCertificateIsPending ==
    ASSUME NEW voteHistory, NEW certificate, RetainedCommitCertificate(voteHistory, certificate),
           NEW owner \in Server, state[owner] = Leader, certificate.leader = owner,
           certificate.term = currentTerm[owner], certificate.entries = log[owner]
    PROVE PendingAgreement(owner, certificate.term, CommitTarget(certificate))
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ Len(CommitTarget(certificate)) = certificate.index
        /\ IsPrefix(CommitTarget(certificate), log[owner])
        /\ Len(CommitTarget(certificate)) > 0
        /\ LastTerm(CommitTarget(certificate)) = certificate.term
    BY CommitCertificateTargetProperties, LenProperties, SMT DEF RetainedCommitCertificate, LastTerm
<1>quorum.
        /\ certificate.replication \in Quorums(ConfigOf(log[owner]))
        /\ certificate.replication \subseteq RecordedAgreementSupport(owner, certificate.term, CommitTarget(certificate))
    BY <1>target, SMT
    DEF RetainedCommitCertificate, LatestConfigurationOccurrence, RecordedAgreementSupport, Quorums
<1> QED BY <1>target, <1>quorum, SMT
    DEF PendingAgreement, RetainedCommitCertificate, LatestConfigurationOccurrence

LEMMA PendingTargetCommitAdvanceFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW owner \in Server, AdvanceCommitIndex(owner), NEW ancestry,
           NEW leader, NEW term, NEW target, PendingTargetProtection(voteHistory, ancestry, leader, term, target)
    PROVE PendingTargetProtection(nextVoteHistory, ancestry, leader, term, target)'
    BY UnchangedLogsAndTermsKeepSelectedHistory, SMT DEF PendingTargetProtection, ProtectedAppendRequests, ProtectedLeaders,
        RecordedAcknowledgersProtected, RecordedReplicationSupport, RecordedAcknowledgment,
        ProtectedVoters, AppendRequests, EligibleCampaignsProtectTarget, OpportunityCertificate,
        CampaignOpportunity, OpportunityVoters, RecordedCampaignVote, NewPeerVoteEligible,
        SnapshotFreshFor, Grant, Started, RecordedCampaignRequests, AdvanceCommitIndex

LEMMA CommitAdvanceCurrentCertificatesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW owner \in Server, AdvanceCommitIndex(owner),
           NEW leader, NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    BY UnchangedLogsAndTermsKeepSelectedHistory, SMT DEF CampaignHistoryContextStep, HistoryCampaignSnapshot,
        CurrentElectionCertificate, RecordedCampaignRequests,
        VoteSupport, VoteFor, Grant, Started, AdvanceCommitIndex

LEMMA OpportunityNonRequestRelationsTransport ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry, NEW commits, OpportunityRelations(voteHistory, ancestry, commits),
           NoNewOpportunityCertificates(voteHistory, nextVoteHistory), ((<<log, EvidenceAgreementTargets(nextVoteHistory)>>)' = <<log, EvidenceAgreementTargets(voteHistory)>>)
    PROVE /\ OpportunityElectionIntersections(nextVoteHistory)'
          /\ OpportunityAncestryIntersections(nextVoteHistory, ancestry)' /\ OpportunityCommitIntersections(nextVoteHistory, commits)'
          /\ OpportunityCommitPrefixes(nextVoteHistory, commits)' /\ OpportunityEvidencePrefixes(nextVoteHistory)'
    BY SMT DEF OpportunityRelations, NoNewOpportunityCertificates,
        OpportunityElectionIntersections, OpportunityAncestryIntersections,
        OpportunityCommitIntersections, OpportunityCommitPrefixes, OpportunityEvidencePrefixes

LEMMA OpportunityRequestRelationsTransport ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NoNewOpportunityCertificates(voteHistory, nextVoteHistory),
           AppendRequests' = AppendRequests, NEW ancestry, NEW commits,
           OpportunityRelations(voteHistory, ancestry, commits)
    PROVE OpportunityRequestIntersections(nextVoteHistory)'
<1>base. TypeOK /\ SendInvariant BY JointCoreBase, SMT
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support,
                      OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)',
                      NEW request \in AppendRequests', request.mterm = term
             PROVE \E requestSnapshot \in Seq(LogEntry): \E requestOccurrence, requestSupport:
                       /\ RetainedElectionCertificate(nextVoteHistory, request.msource, term,
                               requestSnapshot, requestOccurrence, requestSupport)'
                       /\ support \cap requestSupport # {}
    BY SMT DEF OpportunityRequestIntersections
<1>before. OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY SMT DEF NoNewOpportunityCertificates
<1>pair. PICK requestSnapshot, requestOccurrence, requestSupport:
        /\ requestSnapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, request.msource, term,
                requestSnapshot, requestOccurrence, requestSupport)
        /\ support \cap requestSupport # {}
    BY <1>before, SMT DEF OpportunityRelations, OpportunityRequestIntersections
<1>typed. request.msource \in Server BY <1>pair, SMT DEF RetainedElectionCertificate
<1>after. RetainedElectionCertificate(nextVoteHistory, request.msource, term,
                                     requestSnapshot, requestOccurrence, requestSupport)'
    BY <1>base, <1>pair, <1>typed, RetainedElectionCertificateNext, SMT
<1> QED BY <1>pair, <1>after, SMT

LEMMA OpportunityRelationsTransport ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           OpportunityRelations(voteHistory, ancestry, commits), NoNewOpportunityCertificates(voteHistory, nextVoteHistory),
           ((<<log, EvidenceAgreementTargets(nextVoteHistory)>>)' = <<log, EvidenceAgreementTargets(voteHistory)>>), AppendRequests' = AppendRequests
    PROVE OpportunityRelations(nextVoteHistory, ancestry, commits)'
    BY OpportunityNonRequestRelationsTransport, OpportunityRequestRelationsTransport, SMT
    DEF OpportunityRelations

LEMMA AdvancingEpochCannotEnablePeerEligibility ==
    ASSUME TypeOK, TypeOK', OpportunityRetirementFrame,
           NEW peer \in Server, NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), NewPeerVoteEligible(peer, candidate, term, snapshot)'
    PROVE NewPeerVoteEligible(peer, candidate, term, snapshot)
    BY SMT DEF OpportunityRetirementFrame, NewPeerVoteEligible, SnapshotFreshFor,
        TypeOK, ServerVarsTypeOK

LEMMA OpportunityCertificatesRetirementFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, TypeOK', OpportunityRetirementFrame
    PROVE NoNewOpportunityCertificates(voteHistory, nextVoteHistory)
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support,
                      OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
             PROVE OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY SMT DEF NoNewOpportunityCertificates
<1>campaign. CampaignOpportunity(candidate, term, snapshot)
    BY SMT DEF OpportunityCertificate, CampaignOpportunity, OpportunityRetirementFrame,
        ActiveCampaignsRetire, ElectionMessagesFrame, RecordedCampaignRequests,
        TypeOK, ServerVarsTypeOK
<1>recorded. \A voter \in Server:
        RecordedCampaignVote(nextVoteHistory, voter, candidate, term)' <=> RecordedCampaignVote(voteHistory, voter, candidate, term)
    BY ElectionMessagesFactsFrame, SMT DEF OpportunityRetirementFrame
<1>voters. support \subseteq OpportunityVoters(voteHistory, candidate, term, snapshot, occurrence.members)
    BY <1>recorded, AdvancingEpochCannotEnablePeerEligibility, SMT
    DEF OpportunityCertificate, OpportunityVoters, OpportunityRetirementFrame,
        TypeOK, ServerVarsTypeOK
<1> QED BY <1>campaign, <1>voters, SMT DEF OpportunityCertificate

\* A present owner's physically anchored certificate supplies an opportunity
\* using its own recorded quorum, including an alternative retained quorum.
LEMMA OwnedCommitElectionIsOpportunity ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), NEW certificate, RetainedCommitCertificate(voteHistory, certificate),
           NEW owner \in Server, state[owner] = Leader,
           certificate.leader = owner, certificate.term = currentTerm[owner]
    PROVE OpportunityCertificate(voteHistory, owner, certificate.term, certificate.snapshot,
                                 certificate.electionOccurrence, certificate.election)
<1>data.
        /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry) /\ certificate.snapshot \in Seq(LogEntry)
        /\ OwnerPrefix(owner, certificate.term, certificate.entries)
        /\ IsPrefix(certificate.snapshot, certificate.entries)
        /\ RetainedElectionCertificate(voteHistory, owner, certificate.term, certificate.snapshot,
                certificate.electionOccurrence, certificate.election)
    BY SMT DEF RetainedCommitCertificate
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, owner, certificate.term, snapshot, occurrence, support)
    BY CurrentLeaderHasElectionCertificate, SMT
<1>canonical. certificate.snapshot = snapshot /\ certificate.electionOccurrence = occurrence
    BY <1>data, <1>campaign, OwnedElectionSnapshotMatchesCurrent, SMT
<1>ready. ReadyElectionCertificate(voteHistory, owner, certificate.term, certificate.snapshot,
                                 certificate.electionOccurrence, certificate.election)
    BY <1>data, <1>campaign, <1>canonical, SMT
    DEF ReadyElectionCertificate, CurrentElectionCertificate
<1> QED BY <1>data, <1>ready, ReadyCertificateUsesOpportunity, SMT

LEMMA OwnedCommitIntersectsOpportunity ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), OpportunityElectionIntersections(voteHistory),
           NEW certificate, RetainedCommitCertificate(voteHistory, certificate), NEW owner \in Server,
           state[owner] = Leader, certificate.leader = owner,
           certificate.term = currentTerm[owner], NEW candidate \in Server,
           NEW term \in Nat, certificate.term = term, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE certificate.election \cap support # {}
<1>base. MembershipCampaignsInv(voteHistory) BY JointCoreBase, SMT
<1>owned. OpportunityCertificate(voteHistory, owner, term, certificate.snapshot,
                                certificate.electionOccurrence, certificate.election)
    BY <1>base, OwnedCommitElectionIsOpportunity, SMT
<1>typed. certificate.snapshot \in Seq(LogEntry) BY SMT DEF RetainedCommitCertificate
<1> QED BY <1>owned, <1>typed, SMT DEF OpportunityElectionIntersections

LEMMA CommitAdvanceHasOpportunityFrame ==
    ASSUME TypeOK, NEW owner \in Server, AdvanceCommitIndex(owner)
    PROVE OpportunityRetirementFrame /\ UNCHANGED log /\ AppendRequests' = AppendRequests
    BY UnchangedTermsExcludeTimeout, SMT DEF OpportunityRetirementFrame, ElectionMessagesFrame, ActiveCampaignsRetire,
        AdvanceCommitIndex, AppendRequests, TypeOK, ServerVarsTypeOK

LEMMA CommitAdvancePreservesOldOpportunities ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), TypeOK', NEW ancestry, NEW commits,
           OpportunityRelations(voteHistory, ancestry, commits), NEW owner \in Server, AdvanceCommitIndex(owner)
    PROVE NoNewOpportunityCertificates(voteHistory, nextVoteHistory) /\ OpportunityRelations(nextVoteHistory, ancestry, commits)'
<1>base. TypeOK BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next
<1>frame. OpportunityRetirementFrame /\ UNCHANGED log /\ AppendRequests' = AppendRequests
    BY <1>base, CommitAdvanceHasOpportunityFrame, SMT
<1>shrink. NoNewOpportunityCertificates(voteHistory, nextVoteHistory)
    BY <1>base, <1>frame, OpportunityCertificatesRetirementFrame, SMT
<1>targets. ((EvidenceAgreementTargets(nextVoteHistory))' = EvidenceAgreementTargets(voteHistory))
    BY <1>next, ConfigurationEvidenceUnchangedWithLogsAndMessages, SMT
    DEF MembershipJointCore, AdvanceCommitIndex
<1> QED BY <1>next, <1>frame, <1>shrink, <1>targets, OpportunityRelationsTransport, SMT

LEMMA CommitAdvanceOpportunityIntersections ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), TypeOK', NEW ancestry, NEW commits,
           OpportunityRelations(voteHistory, ancestry, commits), NEW owner \in Server, AdvanceCommitIndex(owner),
           NEW fresh, RetainedCommitCertificate(voteHistory, fresh), fresh.leader = owner,
           fresh.term = currentTerm[owner]
    PROVE OpportunityCommitIntersections(nextVoteHistory, commits \cup {fresh})'
<1>frame. NoNewOpportunityCertificates(voteHistory, nextVoteHistory) /\ OpportunityRelations(nextVoteHistory, ancestry, commits)'
    BY CommitAdvancePreservesOldOpportunities, SMT
<1> SUFFICES ASSUME NEW certificate \in commits \cup {fresh}, NEW candidate \in Server,
                      NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support,
                      OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)',
                      certificate.term = term
             PROVE certificate.election \cap support # {}
    BY SMT DEF OpportunityCommitIntersections
<1>old. CASE certificate \in commits
    BY <1>frame, <1>old, SMT DEF OpportunityRelations, OpportunityCommitIntersections
<1>fresh. CASE certificate = fresh
    <2>before. OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        BY <1>frame, SMT DEF NoNewOpportunityCertificates
    <2> QED BY <1>fresh, <2>before, OwnedCommitIntersectsOpportunity, SMT
        DEF OpportunityRelations, AdvanceCommitIndex
<1> QED BY <1>old, <1>fresh, SMT

LEMMA AppendLastTerm ==
    ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry
    PROVE LastTerm(Append(entries, entry)) = entry.term
<1>append.
        /\ Len(entries) \in Nat /\ Len(Append(entries, entry)) = Len(entries) + 1
        /\ Append(entries, entry)[Len(entries) + 1] = entry
    BY AppendProperties, LenProperties, SMT
<1> QED BY <1>append, SMT DEF LastTerm

LEMMA JointProtectionPendingEvidenceFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), PendingEvidenceFrame, ((EvidenceAgreementTargets(nextVoteHistory))' = EvidenceAgreementTargets(voteHistory)), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits)
    PROVE JointCommitProtection(ancestry, commits)' /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
    BY SMT DEF JointMembershipWitnesses, JointCommitProtection, JointEvidenceProtection,
        PendingEvidenceFrame, ReplicationMessagesFrame, ContinuingLeadersKeepLogs,
        ProtectedAppendRequests, ProtectedLeaders, AppendRequests,
        RecordedAcknowledgersProtected, RecordedReplicationSupport, RecordedAcknowledgment, ProtectedVoters

LEMMA VoteRequestHasPendingEvidenceFrame ==
    ASSUME TypeOK, NEW vote \in messages, vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote)
    PROVE PendingEvidenceFrame
    BY MessageTypesDistinct, SMT
    DEF PendingEvidenceFrame, ReplicationMessagesFrame, ContinuingLeadersKeepLogs,
        SuccessfulAppendResponse, AppendRequests, HandleRequestVoteRequest,
        Send, WithMessage, WithMessages, TypeOK, ServerVarsTypeOK

LEMMA ClientRequestAllLogsExtend ==
    ASSUME TypeOK, NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
    PROVE AllLogsExtend
    BY ClientRequestAppendsCurrentTerm, PrefixOnAppend, WholeSequencePrefix, LenProperties, SMT
    DEF AllLogsExtend, ClientRequest, IsPrefix, TypeOK, LogVarsTypeOK

LEMMA CausalCampaignsProtectTargetFromVotingCuts ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target),
           NEW configurationEntries,
           TermProtectedPrefix(ancestry, commits, term, configurationEntries),
           NEW support \in Quorums(ConfigOf(configurationEntries)),
           CampaignTargetVotingCuts(target, term, support, campaigns)
    PROVE \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
          /\ WitnessEdgeConsistency(ancestry) /\ TermsOrdered(target)
          /\ configurationEntries \in Seq(LogEntry) /\ ConfigOf(configurationEntries) \subseteq Server
    BY JointCoreBase, OrderedTermPrefixesAreEdgeConsistent, CoveredSequenceHasLastWitness,
       ConfigurationType, SMT
    DEF JointMembershipWitnesses, TermProtectedPrefix, CertificateFamily, CertificateWitness, WitnessPrefixData
<1> DEFINE P(bound) == \A campaign \in campaigns:
        term < campaign.term /\ campaign.term <= bound => IsPrefix(target, campaign.snapshot)
<1>initial. P(0) BY SMT DEF P, CausalCampaignWitnesses, CausalCampaignData
<1>step. \A bound \in Nat: P(bound) => P(bound + 1)
    <2> SUFFICES ASSUME NEW bound \in Nat, P(bound), NEW campaign \in campaigns,
                          term < campaign.term, campaign.term <= bound + 1,
                          ~IsPrefix(target, campaign.snapshot)
                 PROVE FALSE
        BY SMT DEF P
    <2>data. CausalCampaignData(voteHistory, ancestry, campaign) /\ campaign.term = bound + 1
        BY SMT DEF P, CausalCampaignWitnesses, CausalCampaignData
    <2>higher. CASE term < LastTerm(campaign.snapshot)
        <3>last. Len(campaign.snapshot) > 0
            BY <2>data, <2>higher, LenProperties, SMT DEF CausalCampaignData, LastTerm
        <3>witness. PICK witness \in ancestry:
                /\ witness.prefix = campaign.snapshot /\ witness.edge.term = LastTerm(campaign.snapshot)
            BY <1>base, <2>data, <3>last, CoveredSequenceHasLastWitness, SMT DEF CausalCampaignData
        <3>earlier. PICK earlier \in campaigns:
                /\ earlier.term = witness.edge.term /\ earlier.snapshot = witness.snapshot
            BY <3>witness, SMT DEF CausalCampaignWitnesses, CreatorCampaignCoverage
        <3>bound. term < earlier.term /\ earlier.term <= bound
            BY <2>data, <2>higher, <3>last, <3>witness, <3>earlier, LastTermTypeOK, LenProperties, SMT
            DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, LastTerm
        <3>contains. IsPrefix(target, earlier.snapshot)
            BY <3>earlier, <3>bound, SMT DEF P
        <3> QED BY <1>base, <2>data, <3>witness, <3>earlier, <3>contains,
            SequencePrefixTransitive, SMT DEF CertificateFamily, CertificateWitness, WitnessPrefixData, CausalCampaignData
    <2>bounded. CASE LastTerm(campaign.snapshot) <= term
        <3>profile. TermProtectedPrefix(ancestry, commits, term, campaign.snapshot)
            <4>snapshot.
                    /\ campaign.snapshot \in Seq(LogEntry) /\ TermsOrdered(campaign.snapshot)
                    /\ CoveredPrefix(ancestry, campaign.snapshot)
                BY <2>data, SMT DEF CausalCampaignData
            <4>bounds. \A index \in DOMAIN campaign.snapshot: campaign.snapshot[index].term <= term
                BY <4>snapshot, <2>bounded, OrderedEntriesBoundedByLastTerm, SMT
            <4>commits. \A certificate \in TermCommits(commits, term):
                    IsPrefix(CommitTarget(certificate), campaign.snapshot)
                <5> SUFFICES ASSUME NEW certificate \in TermCommits(commits, term)
                             PROVE IsPrefix(CommitTarget(certificate), campaign.snapshot) BY SMT
                <5>data. certificate \in commits /\ certificate.term \in Nat /\ certificate.term <= term
                    BY SMT DEF TermCommits, JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
                <5>earlier. certificate.term < campaign.term
                    BY <2>data, <5>data, SMT DEF CausalCampaignData
                <5> QED BY <5>data, <5>earlier, SMT DEF CausalCampaignWitnesses, CampaignCommitPrefixes
            <4> QED BY <4>snapshot, <4>bounds, <4>commits, SMT DEF TermProtectedPrefix
        <3>shape. EqualOrAdjacentConfigurations(ConfigOf(configurationEntries), ConfigOf(campaign.snapshot))
            BY <3>profile, TermProtectedConfigurationsAreEqualOrAdjacent, SMT
        <3>votes. campaign.support \in Quorums(ConfigOf(campaign.snapshot))
                  /\ ConfigOf(campaign.snapshot) \subseteq Server
            BY <2>data, ConfigurationType, SMT DEF CausalCampaignData, CausalElectionCertificate,
                RetainedElectionCertificate, LatestConfigurationOccurrence
        <3>intersection. support \cap campaign.support # {}
            BY <1>base, <3>shape, <3>votes, EqualOrAdjacentQuorumsIntersect, SMT
        <3>cut. SnapshotCoversPrefix(campaign.snapshot, target)
                \/ \E peer \in Server: EarlierConflictingRequest(peer, term, campaign.term, target)
            BY <3>intersection, SMT DEF CampaignTargetVotingCuts
        <3>fresh. CASE SnapshotCoversPrefix(campaign.snapshot, target)
            <4>contains. IsPrefix(target, campaign.snapshot)
                BY <1>base, <2>data, <2>bounded, <3>fresh, LastTermTypeOK, LenProperties,
                   CoveredSequencesWithSameLastTermAreOrdered, SMT
                DEF SnapshotCoversPrefix, CausalCampaignData, LastTerm
            <4> QED BY <4>contains, SMT
        <3>conflict. CASE \E peer \in Server: EarlierConflictingRequest(peer, term, campaign.term, target)
            <4>request. PICK conflicting \in AppendRequests:
                    /\ term < conflicting.mterm /\ conflicting.mterm < campaign.term
                    /\ ~RequestRespectsPrefix(conflicting, target)
                BY <3>conflict, SMT DEF EarlierConflictingRequest
            <4>earlier. PICK earlier, sent:
                    /\ earlier \in campaigns /\ sent \in Seq(LogEntry)
                    /\ earlier.term = conflicting.mterm /\ RequestPrefixData(conflicting, sent)
                    /\ CoveredPrefix(ancestry, sent)
                    /\ (IsPrefix(earlier.snapshot, sent) \/ IsPrefix(sent, earlier.snapshot))
                BY <4>request, SMT DEF CausalCampaignWitnesses, RequestCampaignCoverage
            <4>bound. term < earlier.term /\ earlier.term <= bound
                BY <2>data, <4>request, <4>earlier, SMT DEF CausalCampaignWitnesses, CausalCampaignData
            <4>contains. IsPrefix(target, earlier.snapshot)
                BY <4>earlier, <4>bound, SMT DEF P
            <4>respects. RequestRespectsPrefix(conflicting, target)
                <5>fields. conflicting.mentries \in Seq(LogEntry)
                    BY <1>base, <4>request, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
                <5>snapshot. earlier.snapshot \in Seq(LogEntry)
                    BY <4>earlier, SMT DEF CausalCampaignWitnesses, CausalCampaignData
                <5> QED BY <5>fields, <5>snapshot, <4>earlier, <4>contains,
                    ComparableRequestPrefixRespectsTarget, Zenon
            <4> QED BY <4>request, <4>respects, SMT
        <3> QED BY <3>cut, <3>fresh, <3>conflict, SMT
    <2> QED BY <2>data, <2>higher, <2>bounded, LastTermTypeOK, SMT DEF CausalCampaignData
<1>all. \A bound \in Nat: P(bound) BY <1>initial, <1>step, NatInduction, Isa
<1> QED BY <1>all, SMT DEF P, CausalCampaignWitnesses, CausalCampaignData

LEMMA RecordedLocalOriginSuppliesTargetEvidence ==
    ASSUME NEW voteHistory, NEW ancestry, CertificateFamily(voteHistory, ancestry),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory),
           NEW leader, NEW term, NEW target, LocalAppendOrigin(voteHistory, leader, term, target)
    PROVE TargetLocalEvidence(voteHistory, ancestry, leader, term, target)
    BY FamilyWitnessPrefixCovered, SMT
    DEF LocalAppendOrigin, LocalAppendRecordsCovered, TargetLocalEvidence

LEMMA TargetSourceEvidenceHasCapturedCampaign ==
    ASSUME NEW voteHistory, NEW ancestry, NEW commits, NEW campaigns,
           CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           NEW leader, NEW term, NEW target, TargetRequestEvidence(voteHistory, ancestry, leader, term, target)
    PROVE \E campaign \in campaigns: campaign.candidate = leader /\ campaign.term = term
    BY SMT DEF TargetRequestEvidence, TargetWireEvidence, TargetLocalEvidence,
        CausalCampaignWitnesses, RequestCampaignCoverage, CreatorCampaignCoverage

LEMMA TargetLocalAndRequestPrefixesAreComparable ==
    ASSUME NEW voteHistory, NEW ancestry, CertificateFamily(voteHistory, ancestry), TermPrefixOrder(ancestry),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           TargetLocalEvidence(voteHistory, ancestry, leader, term, target),
           NEW request \in AppendRequests, request.mterm = term,
           NEW sent \in Seq(LogEntry), RequestPrefixData(request, sent), CoveredPrefix(ancestry, sent),
           RequestCampaignBoundary(voteHistory, request, sent)
    PROVE \E prefix \in Seq(LogEntry):
        /\ IsPrefix(target, prefix) /\ (IsPrefix(sent, prefix) \/ IsPrefix(prefix, sent))
<1>local. PICK record \in voteHistory, witness \in ancestry:
        /\ LocalAppendRecord(record) /\ record.candidate = leader /\ record.term = term
        /\ record.prefix \in Seq(LogEntry) /\ IsPrefix(target, record.prefix)
        /\ CoveredPrefix(ancestry, record.prefix)
        /\ witness.prefix = record.prefix /\ witness.owner = leader /\ witness.edge.term = term
        /\ witness.snapshot = record.snapshot
    BY SMT DEF TargetLocalEvidence
<1>source. request.msource = leader
    BY <1>local, SMT DEF TargetLocalEvidence, LocalAppendRequestOwnersUnique
<1>boundary. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
        /\ (IsPrefix(snapshot, sent) \/ IsPrefix(sent, snapshot))
        /\ \A index \in DOMAIN sent: sent[index].term < term => index <= Len(snapshot)
    BY <1>source, SMT DEF RequestCampaignBoundary
<1>equal. snapshot = witness.snapshot
    BY <1>local, <1>boundary, HistorySnapshotIsUnique, SMT
    DEF CertificateFamily, CertificateWitness, RetainedElectionCertificate
<1>data. WitnessPrefixData(witness) /\ Len(record.prefix) > 0 /\ LastTerm(record.prefix) = term
    BY <1>local, LenProperties, SMT DEF CertificateFamily, CertificateWitness, WitnessPrefixData, LogEntryEdge, LastTerm
<1>empty. CASE Len(sent) = 0
    BY <1>local, <1>empty, LenProperties, SubSeqEmpty, SMT DEF IsPrefix
<1>nonempty. CASE Len(sent) > 0
    <2>bound. LastTerm(sent) <= term /\ LastTerm(sent) \in Nat
        BY <1>nonempty, LastTermTypeOK, LenProperties, SMT DEF RequestPrefixData, EntryStructure, LastTerm
    <2>same. CASE LastTerm(sent) = term
        <3>order. IsPrefix(sent, record.prefix) \/ IsPrefix(record.prefix, sent)
            BY <1>local, <1>data, <1>nonempty, <2>same, CoveredSequencesWithSameLastTermAreOrdered, LenProperties, SMT
        <3> QED BY <1>local, <3>order, SMT
    <2>older. CASE LastTerm(sent) < term
        <3>length. Len(sent) <= Len(snapshot)
            BY <1>boundary, <1>nonempty, <2>older, LenProperties, SMT DEF LastTerm
        <3>inside. IsPrefix(sent, snapshot)
            BY <1>boundary, <3>length, ComparablePrefixesWithOrderedLengths, SMT
        <3>order. IsPrefix(sent, record.prefix)
            BY <1>local, <1>data, <1>equal, <3>inside, SequencePrefixTransitive, SMT DEF WitnessPrefixData
        <3> QED BY <1>local, <3>order, SMT
    <2> QED BY <2>bound, <2>same, <2>older, SMT
<1> QED BY <1>empty, <1>nonempty, LenProperties, SMT

LEMMA CoveredRequestHasCampaignBoundary ==
    ASSUME NEW voteHistory, TypeOK, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW request \in AppendRequests, NEW prefix \in Seq(LogEntry),
           RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix)
    PROVE RequestCampaignBoundary(voteHistory, request, prefix)
<1>old. PICK old \in Seq(LogEntry):
        /\ RequestPrefixData(request, old) /\ CoveredPrefix(ancestry, old) /\ RequestCampaignBoundary(voteHistory, request, old)
    BY SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
<1>equal. old = prefix
    BY <1>old, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
    DEF JointMembershipWitnesses, TypeOK, MsgTypeOK, AppendRequests
<1> QED BY <1>old, <1>equal, SMT

LEMMA MixedSupportSuppliesTargetVotingCuts ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignRecords(voteHistory, ancestry, campaigns),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target),
           TargetCampaignEvidence(voteHistory, leader, term, target), TargetRequestEvidence(voteHistory, ancestry, leader, term, target),
           NEW support, MixedRecordedTargetCampaignIntersections(leader, term, target, support, campaigns)
    PROVE CampaignTargetVotingCuts(target, term, support, campaigns)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1> SUFFICES ASSUME NEW campaign \in campaigns, term < campaign.term, support \cap campaign.support # {}
             PROVE SnapshotCoversPrefix(campaign.snapshot, target)
                   \/ \E peer \in Server: EarlierConflictingRequest(peer, term, campaign.term, target)
    BY SMT DEF CampaignTargetVotingCuts
<1>data. CausalCampaignData(voteHistory, ancestry, campaign)
    BY SMT DEF CausalCampaignRecords
<1>peer. PICK peer \in support \cap campaign.support: TRUE BY SMT
<1>types. peer \in Server
    BY <1>data, <1>peer, SMT
    DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, Quorums
<1>self. CASE peer = leader
    <2>wire. CASE TargetWireEvidence(voteHistory, ancestry, leader, term, target)
        <3>original. PICK original, originalPrefix:
                /\ original \in AppendRequests /\ originalPrefix \in Seq(LogEntry)
                /\ original.msource = leader /\ original.mterm = term
                /\ RequestPrefixData(original, originalPrefix) /\ CoveredPrefix(ancestry, originalPrefix)
                /\ Len(target) <= Len(originalPrefix)
            BY <2>wire, SMT DEF TargetWireEvidence
        <3>frozen. PICK prefix \in Seq(LogEntry):
                /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
                /\ \A part \in Seq(LogEntry): IsPrefix(part, prefix) =>
                       SnapshotCoversPrefix(campaign.snapshot, part)
                       \/ EarlierConflictingRequest(leader, term, campaign.term, part)
            BY <1>data, <1>peer, <1>self, <3>original, SMT DEF CausalCampaignData, RequestSourceElectionCut
        <3>boundary. RequestCampaignBoundary(voteHistory, original, prefix)
            BY <1>base, <3>original, <3>frozen, CoveredRequestHasCampaignBoundary, SMT
        <3>length. Len(target) <= Len(prefix)
            BY <3>original, <3>frozen, SMT DEF RequestPrefixData
        <3>inside. IsPrefix(target, prefix)
            BY <1>base, <3>original, <3>frozen, <3>boundary, <3>length, FrozenRequestPrefixContainsTarget, SMT
        <3> QED BY <1>types, <1>self, <3>frozen, <3>inside, SMT
    <2>local. CASE TargetLocalEvidence(voteHistory, ancestry, leader, term, target)
        BY <1>data, <1>peer, <1>self, <2>local, SMT
        DEF TargetLocalEvidence, CausalCampaignData, LocalAppendElectionCut
    <2> QED BY <2>wire, <2>local, SMT DEF TargetRequestEvidence
<1>other. CASE peer # leader
    <2>response. PICK response \in messages:
            /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
            /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        BY <1>peer, <1>other, SMT DEF MixedRecordedTargetCampaignIntersections
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ \A part \in Seq(LogEntry): IsPrefix(part, prefix) =>
                   SnapshotCoversPrefix(campaign.snapshot, part)
                   \/ EarlierConflictingRequest(peer, term, campaign.term, part)
        BY <1>data, <1>peer, <2>response, SMT
        DEF CausalCampaignData, CausalElectionCertificate, FrozenElectionAcknowledgmentCut
    <2>boundary. RequestCampaignBoundary(voteHistory, request, prefix)
        BY <1>base, <2>frozen, CoveredRequestHasCampaignBoundary, SMT
    <2>inside. IsPrefix(target, prefix)
        BY <1>base, <2>response, <2>frozen, <2>boundary, FrozenRequestPrefixContainsTarget, SMT
        DEF ResponseMatchesRequest
    <2> QED BY <1>types, <2>frozen, <2>inside, SMT
<1> QED BY <1>self, <1>other, SMT

LEMMA AppendReceiveCertificateSuppliesMixedSupport ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignRecords(voteHistory, ancestry, campaigns),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory),
           NEW received \in messages, received.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(received.mdest, received.msource, received),
           NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)'
    PROVE /\ TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
          /\ MixedRecordedTargetCampaignIntersections(certificate.leader, certificate.term,
                    CommitTarget(certificate), certificate.replication, campaigns)
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>base. TypeOK /\ TypeOK' /\ SendInvariant' /\ SendInvariant
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>frame. ElectionMessagesFrame /\ AppendRequests' = AppendRequests
    BY <1>base, AppendReceiveElectionFrame, SMT
<1>fields. certificate.leader \in Server /\ certificate.term \in Nat /\ certificate.entries \in Seq(LogEntry)
           /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) = certificate.index
    BY CommitPrefixDataTargetProperties, SMT DEF RetainedCommitCertificate, CommitPrefixData
<1>request_evidence. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
    <2>wire. CASE certificate.replication \ {certificate.leader} # {}
        <3>peer. PICK peer \in certificate.replication \ {certificate.leader}: TRUE
            BY <2>wire, SMT
        <3>acknowledgment. RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))'
            BY <3>peer, SMT DEF RetainedCommitCertificate
        <3>origin. PICK response, request:
                /\ response \in messages' /\ request \in messages'
                /\ SuccessfulAppendResponse(response) /\ ResponseMatchesRequest(response, request)
                /\ response.msource = peer /\ response.mdest = certificate.leader /\ response.mterm = certificate.term
                /\ response.mmatchIndex >= Len(CommitTarget(certificate))
            BY <3>acknowledgment, Zenon DEF RecordedPrefixAcknowledgment
        <3>before. request \in AppendRequests /\ request.msource = certificate.leader /\ request.mterm = certificate.term
            BY <1>frame, <3>origin, SMT DEF AppendRequests, ResponseMatchesRequest
        <3>prefix. PICK prefix \in Seq(LogEntry):
                /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
                /\ RequestCampaignBoundary(voteHistory, request, prefix)
            BY <3>before, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
        <3>length. Len(CommitTarget(certificate)) <= Len(prefix)
            BY <3>prefix, <3>origin, SMT DEF RequestPrefixData, ResponseMatchesRequest
        <3> QED BY <3>before, <3>prefix, <3>length, SMT DEF TargetRequestEvidence, TargetWireEvidence
    <2>local. CASE certificate.replication \ {certificate.leader} = {}
        <3>no_client. ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
            BY <1>base, AppendReceiveElectionFrame, ContinuingLeadersExcludeClientAppend, SMT
        <3>old_origins. \A record \in nextVoteHistory: LocalAppendRecord(record) => record \in voteHistory
            BY <1>base, <3>no_client, NewLocalAppendRecordOrigin, SMT
        <3>origin. LocalAppendOrigin(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
            <4>self. certificate.replication \subseteq {certificate.leader}
                BY <2>local, Zenon
            <4>after. LocalAppendOrigin(nextVoteHistory, certificate.leader, certificate.term, CommitTarget(certificate))'
                BY <4>self, SMT DEF RetainedCommitCertificate
            <4>record. PICK record \in nextVoteHistory:
                    /\ LocalAppendRecord(record) /\ record.candidate = certificate.leader
                    /\ record.term = certificate.term /\ record.prefix \in Seq(LogEntry)
                    /\ IsPrefix(CommitTarget(certificate), record.prefix)
                BY <4>after, Zenon DEF LocalAppendOrigin
            <4>old. record \in voteHistory BY <3>old_origins, <4>record, SMT
            <4> QED BY <4>record, <4>old, SMT DEF LocalAppendOrigin
        <3> QED BY <3>origin, RecordedLocalOriginSuppliesTargetEvidence, SMT
            DEF JointMembershipWitnesses, TargetRequestEvidence
    <2> QED BY <2>wire, <2>local, SMT
<1>mixed. MixedRecordedTargetCampaignIntersections(certificate.leader, certificate.term,
                    CommitTarget(certificate), certificate.replication, campaigns)
    <2> SUFFICES ASSUME NEW campaign \in campaigns, certificate.term < campaign.term,
                          NEW peer \in certificate.replication \cap campaign.support, peer # certificate.leader
                 PROVE \E response \in messages:
                           /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = certificate.leader
                           /\ response.mterm = certificate.term /\ response.mmatchIndex >= Len(CommitTarget(certificate))
        BY SMT DEF MixedRecordedTargetCampaignIntersections
    <2>vote. peer \in Server /\ campaign.candidate \in Server /\ campaign.term \in Nat
              /\ RecordedCampaignVote(nextVoteHistory, peer, campaign.candidate, campaign.term)'
        <3>data. CausalCampaignData(voteHistory, ancestry, campaign)
            BY SMT DEF CausalCampaignRecords
        <3>support. VoteSupport(voteHistory, campaign.candidate, campaign.term, campaign.support)
            BY <3>data, SMT DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate
        <3>types. peer \in Server /\ campaign.candidate \in Server /\ campaign.term \in Nat
            BY <3>data, <3>support, SMT DEF CausalCampaignData, VoteSupport
        <3>before. RecordedCampaignVote(voteHistory, peer, campaign.candidate, campaign.term)
            BY <3>support, <3>types, VoteSupportWithinRecordedCampaignVoters, SMT DEF RecordedCampaignVoters
        <3> QED BY <1>next, <3>types, <3>before, RecordedCampaignVoteRetained, SMT
    <2>acknowledgment. RecordedAcknowledgment(peer, certificate.leader, certificate.term, Len(CommitTarget(certificate)))'
        <3>prefix. RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))'
            BY SMT DEF RetainedCommitCertificate
        <3> QED BY <3>prefix, Zenon DEF RecordedPrefixAcknowledgment, RecordedAcknowledgment
    <2>before. RecordedAcknowledgment(peer, certificate.leader, certificate.term, Len(CommitTarget(certificate)))
        BY <1>base, <1>fields, <1>next, <2>vote, <2>acknowledgment,
           HigherPostVoteForcesOldAcknowledgmentPreexisting, LenProperties, SMT
    <2> QED BY <2>before, SMT DEF RecordedAcknowledgment
<1> QED BY <1>request_evidence, <1>mixed, SMT

LEMMA RawTargetFitsTermFrontierOrEstablishedPrefix ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           CommitPrefixCoverage(ancestry, commits), NEW target \in Seq(LogEntry), NEW term \in Nat,
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target)
    PROVE TermProtectedPrefix(ancestry, commits, term, target) \/ SameTermEstablishedPrefix(commits, target, term)
<1>base. PrefixWitnessFamilyData(ancestry) /\ TermPrefixOrder(ancestry)
    BY SMT DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData
<1>witness. PICK witness \in ancestry: witness.prefix = target /\ witness.edge.term = term
    BY <1>base, DataCoveredWordHasLastWitness, SMT
<1>ordered. TermsOrdered(target)
    BY <1>witness, SMT DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, WitnessPrefixData
<1>established. CASE SameTermEstablishedPrefix(commits, target, term) BY <1>established, SMT
<1>new. CASE ~SameTermEstablishedPrefix(commits, target, term)
    <2>commits. \A certificate \in TermCommits(commits, term): IsPrefix(CommitTarget(certificate), target)
        <3> SUFFICES ASSUME NEW certificate \in TermCommits(commits, term)
                     PROVE IsPrefix(CommitTarget(certificate), target) BY SMT
        <3>certificate. RetainedCommitCertificate(voteHistory, certificate) /\ certificate \in commits /\ certificate.term <= term
            BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily, TermCommits
        <3>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
                  /\ LastTerm(CommitTarget(certificate)) = certificate.term
                  /\ CoveredPrefix(ancestry, CommitTarget(certificate))
            BY <3>certificate, CommitCertificateTargetProperties, CoveredPrefixRestriction, LenProperties, SMT
            DEF CommitPrefixCoverage, RetainedCommitCertificate, LastTerm
        <3>earlier. CASE certificate.term < term
            BY <1>witness, <3>certificate, <3>earlier, SMT
            DEF JointMembershipWitnesses, JointCommitProtection, LaterTermPrefixProtection
        <3>same. CASE certificate.term = term
            <4>length. Len(CommitTarget(certificate)) <= Len(target)
                <5> SUFFICES ASSUME Len(target) <= Len(CommitTarget(certificate)) PROVE FALSE
                    BY <3>target, LenProperties, SMT
                <5>inside. IsPrefix(target, CommitTarget(certificate))
                    BY <1>base, <3>same, <3>target, DataCoveredWordsWithSameLastTermAreOrdered, SMT
                <5> QED BY <1>new, <3>certificate, <3>same, <5>inside, SMT DEF SameTermEstablishedPrefix
            <4> QED BY <1>base, <3>same, <3>target, <4>length, DataCoveredWordsWithSameLastTermAreOrdered, SMT
        <3> QED BY <3>certificate, <3>earlier, <3>same, SMT DEF RetainedCommitCertificate
    <2>profile. TermProtectedPrefix(ancestry, commits, term, target)
        BY <1>ordered, <2>commits, OrderedEntriesBoundedByLastTerm, SMT DEF TermProtectedPrefix
    <2> QED BY <2>profile, SMT
<1> QED BY <1>established, <1>new, SMT

LEMMA ProtectedAppendRequestsOnPrefix ==
    ASSUME NEW target \in Seq(LogEntry), NEW longer \in Seq(LogEntry), IsPrefix(target, longer), NEW term,
           ProtectedAppendRequests(longer, term)
    PROVE ProtectedAppendRequests(target, term)
    BY PrefixEntryEqual, LenProperties, SMT DEF ProtectedAppendRequests, RequestRespectsPrefix, IsPrefix

LEMMA SameTermSourceEvidenceProtectsTarget ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), FrozenRequestPrefixesAgree(ancestry),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target),
           TargetCampaignEvidence(voteHistory, leader, term, target), TargetRequestEvidence(voteHistory, ancestry, leader, term, target),
           NEW request \in AppendRequests, request.mterm = term
    PROVE RequestRespectsPrefix(request, target)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>sent. PICK sent \in Seq(LogEntry):
        /\ RequestPrefixData(request, sent) /\ CoveredPrefix(ancestry, sent)
        /\ RequestCampaignBoundary(voteHistory, request, sent)
    BY SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
<1>fields. request.mentries \in Seq(LogEntry)
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
<1>wire. CASE TargetWireEvidence(voteHistory, ancestry, leader, term, target)
    <2>original. PICK original, prefix:
        /\ original \in AppendRequests /\ prefix \in Seq(LogEntry)
        /\ original.msource = leader /\ original.mterm = term
        /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ RequestCampaignBoundary(voteHistory, original, prefix) /\ Len(target) <= Len(prefix)
        BY <1>wire, SMT DEF TargetWireEvidence
    <2>inside. IsPrefix(target, prefix)
        BY <1>base, <2>original, FrozenRequestPrefixContainsTarget, SMT
    <2>order. IsPrefix(sent, prefix) \/ IsPrefix(prefix, sent)
        BY <1>sent, <2>original, SMT DEF FrozenRequestPrefixesAgree
    <2> QED BY <1>sent, <1>fields, <2>original, <2>inside, <2>order, ComparableRequestPrefixRespectsTarget, SMT
<1>local. CASE TargetLocalEvidence(voteHistory, ancestry, leader, term, target)
    <2>prefix. PICK prefix \in Seq(LogEntry):
        IsPrefix(target, prefix) /\ (IsPrefix(sent, prefix) \/ IsPrefix(prefix, sent))
        BY <1>base, <1>sent, <1>local, TargetLocalAndRequestPrefixesAreComparable, SMT
    <2> QED BY <1>sent, <1>fields, <2>prefix, ComparableRequestPrefixRespectsTarget, SMT
<1> QED BY <1>wire, <1>local, SMT DEF TargetRequestEvidence

LEMMA CampaignProtectedRawTargetHasBoundaryAndRequests ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenRequestPrefixesAgree(ancestry), NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target),
           TargetCampaignEvidence(voteHistory, leader, term, target), TargetRequestEvidence(voteHistory, ancestry, leader, term, target),
           \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
    PROVE LaterTermPrefixProtection(ancestry, target, term) /\ ProtectedAppendRequests(target, term)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>boundary. LaterTermPrefixProtection(ancestry, target, term)
    BY SequencePrefixTransitive, SMT
    DEF CausalCampaignWitnesses, CausalCampaignData, CreatorCampaignCoverage, LaterTermPrefixProtection,
        JointMembershipWitnesses, CertificateFamily, CertificateWitness, WitnessPrefixData
<1>requests. ProtectedAppendRequests(target, term)
    <2> SUFFICES ASSUME NEW request \in AppendRequests, request.mterm >= term
                 PROVE RequestRespectsPrefix(request, target) BY SMT DEF ProtectedAppendRequests
    <2>fields. request.mterm \in Nat /\ request.mentries \in Seq(LogEntry)
        BY <1>base, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
    <2>same. CASE request.mterm = term
        BY <2>same, SameTermSourceEvidenceProtectsTarget, SMT
    <2>higher. CASE term < request.mterm
        <3>campaign. PICK campaign, sent:
                /\ campaign \in campaigns /\ sent \in Seq(LogEntry)
                /\ campaign.term = request.mterm /\ RequestPrefixData(request, sent)
                /\ (IsPrefix(campaign.snapshot, sent) \/ IsPrefix(sent, campaign.snapshot))
            BY SMT DEF CausalCampaignWitnesses, RequestCampaignCoverage
        <3>target. IsPrefix(target, campaign.snapshot) BY <2>higher, <3>campaign, SMT
        <3> QED BY <2>fields, <3>campaign, <3>target, ComparableRequestPrefixRespectsTarget, SMT
            DEF CausalCampaignWitnesses, CausalCampaignData
    <2> QED BY <2>fields, <2>same, <2>higher, SMT
<1> QED BY <1>boundary, <1>requests, SMT

LEMMA CurrentLeaderTargetHasCampaignEvidence ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW leader \in Server,
           state[leader] = Leader, NEW term \in Nat, term = currentTerm[leader],
           NEW target \in Seq(LogEntry), Len(target) > 0, LastTerm(target) = term,
           IsPrefix(target, log[leader])
    PROVE TargetCampaignEvidence(voteHistory, leader, term, target)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ WitnessEdgeConsistency(ancestry)
    BY JointCoreBase, OrderedTermPrefixesAreEdgeConsistent, SMT DEF JointMembershipWitnesses
<1>covered. CoveredPrefix(ancestry, target)
    BY <1>base, CurrentLogPrefixCovered, SMT DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK
<1>tip. PICK witness \in ancestry:
        /\ witness.prefix = target /\ witness.edge.term = term
    BY <1>base, <1>covered, CoveredSequenceHasLastWitness, SMT
<1>owner. witness.owner = leader
    BY <1>tip, LiveAncestryIdentifiesCurrentOwners, SMT
<1> QED BY <1>base, <1>tip, <1>owner, EntryWitnessSuppliesTargetCampaignEvidence, SMT DEF CertificateFamily

LEMMA CurrentLeaderOpportunityIdentifiesCandidate ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), OpportunityElectionIntersections(voteHistory),
           NEW leader \in Server, state[leader] = Leader, NEW candidate \in Server,
           NEW term \in Nat, term = currentTerm[leader], NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE candidate = leader
<1>base. MembershipCampaignsInv(voteHistory) BY JointCoreBase, SMT
<1>campaign. PICK leaderSnapshot, leaderOccurrence, votes:
        /\ leaderSnapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, term, leaderSnapshot, leaderOccurrence, votes)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT
<1>opportunity. OpportunityCertificate(voteHistory, leader, term, leaderSnapshot, leaderOccurrence, votes)
    BY <1>campaign, CurrentCertificateIsReady, ReadyCertificateUsesOpportunity, SMT
<1>intersection. votes \cap support # {}
    BY <1>campaign, <1>opportunity, SMT DEF OpportunityElectionIntersections
<1> QED BY <1>campaign, <1>intersection, RecordedSupportMeetsOpportunityOnlyForOwner, SMT
    DEF CurrentElectionCertificate

LEMMA CausalHistoryMetadataInit ==
    Init => CausalHistoryMetadata({}, {}, {}, {})
    BY FrozenAcknowledgmentPrefixHistoryInit, FrozenAcknowledgmentVoteCutHistoryInit,
       AppendRequestOwnersUniqueInit, RequestSourceHistoriesInit, LocalAppendHistoriesInit, FS_EmptySet, ServerStatesDistinct, SMT
    DEF CausalHistoryMetadata, FrozenRequestPrefixesAgree, AppendRequests, CausalCampaignWitnesses,
        CreatorCampaignCoverage, RequestCampaignCoverage, CampaignCommitPrefixes, CommitPrefixCoverage,
        CurrentCausalCampaigns, CampaignPendingPrefixes, PendingAgreement, Init, InitServerVars

LEMMA FrozenRequestAgreementNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenRequestPrefixesAgree(ancestry), [Next]_vars
    PROVE FrozenRequestPrefixesAgree(ancestry)'
<1>base. TypeOK /\ EntryEdgeBase BY JointCoreBase, SMT DEF MembershipJointCore
<1>frame. CASE AppendRequests' = AppendRequests
    BY <1>frame, SMT DEF FrozenRequestPrefixesAgree, RequestPrefixData, CoveredPrefix
<1>new. CASE AppendRequests' # AppendRequests
    <2>request. PICK request \in AppendRequests' \ AppendRequests: TRUE
        BY <1>new, MessagesMonotonicNext, SMT DEF AppendRequests
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer) /\ request = AppendEntriesMessage(leader, peer)
        BY <1>base, <2>request, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2> QED BY <2>origin, AppendSendPreservesFrozenRequestAgreement, SMT
<1> QED BY <1>frame, <1>new, SMT

LEMMA CausalCampaignDataNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW campaign, CausalCampaignData(voteHistory, ancestry, campaign)
    PROVE CausalCampaignData(nextVoteHistory, ancestry, campaign)'
    BY CausalElectionCertificateNext, RequestSourceElectionCutNext, LocalAppendElectionCutNext, SMT
    DEF CausalCampaignData, CausalElectionCertificate, CoveredPrefix, TermsOrdered

LEMMA CausalCampaignWitnessesNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns), CurrentCausalCampaigns(campaigns)
    PROVE CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns)'
<1>base. TypeOK /\ EntryEdgeBase
    BY JointCoreBase, SMT DEF MembershipJointCore
<1>data. \A campaign \in campaigns: CausalCampaignData(nextVoteHistory, ancestry, campaign)'
    BY CausalCampaignDataNext, SMT DEF CausalCampaignWitnesses
<1>requests. RequestCampaignCoverage(ancestry, campaigns)'
    <2> SUFFICES ASSUME NEW request \in AppendRequests'
                 PROVE \E campaign \in campaigns: \E prefix \in Seq(LogEntry):
                           /\ campaign.candidate = request.msource /\ campaign.term = request.mterm
                           /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
                           /\ (IsPrefix(campaign.snapshot, prefix) \/ IsPrefix(prefix, campaign.snapshot))
        BY SMT DEF RequestCampaignCoverage, RequestPrefixData, CoveredPrefix
    <2>old. CASE request \in messages
        BY <2>old, SMT DEF CausalCampaignWitnesses, RequestCampaignCoverage, AppendRequests
    <2>new. CASE request \notin messages
        <3>origin. PICK leader, peer \in Server:
                /\ AppendEntries(leader, peer) /\ request = AppendEntriesMessage(leader, peer)
            BY <1>base, <2>new, NewAppendRequestOrigin, SMT DEF AppendRequests
        <3>campaign. PICK campaign \in campaigns:
                /\ campaign.candidate = leader /\ campaign.term = currentTerm[leader]
                /\ campaign.snapshot = CampaignPrefix(log[leader], currentTerm[leader])
            BY <3>origin, SMT DEF CurrentCausalCampaigns, AppendEntries
        <3>ancestry. AncestralRequestPrefix(nextVoteHistory, ancestry, request)'
            BY <3>origin, NewAppendRequestHasAncestralPrefix, SMT
            DEF JointMembershipWitnesses, MembershipJointCore, ReplicationPrefixInv
        <3>prefix. PICK prefix \in Seq(LogEntry):
                /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
                /\ OwnerPrefix(request.msource, request.mterm, prefix)'
            BY <3>ancestry, SMT DEF AncestralRequestPrefix, RequestPrefixData, CoveredPrefix
        <3>held. IsPrefix(prefix, log[leader])
            BY <3>origin, <3>prefix, SMT DEF OwnerPrefix, AppendEntries, AppendEntriesMessage
        <3>snapshot. campaign.snapshot \in Seq(LogEntry) /\ IsPrefix(campaign.snapshot, log[leader])
            BY <1>base, <3>origin, <3>campaign, PreTermIndexProperties, SubSeqTypeOK,
               SubSeqProperties, ElementOfSeq, LenProperties, SMT
            DEF CampaignPrefix, IsPrefix, CausalCampaignWitnesses, CausalCampaignData, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
        <3>order. IsPrefix(campaign.snapshot, prefix) \/ IsPrefix(prefix, campaign.snapshot)
            BY <1>base, <3>origin, <3>campaign, <3>held, <3>prefix, <3>snapshot,
               PrefixesWithBoundedLength, SMT DEF TypeOK, LogVarsTypeOK
        <3> QED BY <3>origin, <3>campaign, <3>prefix, <3>order, SMT DEF AppendEntriesMessage
    <2> QED BY <2>old, <2>new, SMT
<1> QED BY <1>data, <1>requests, SMT
    DEF CausalCampaignWitnesses, CreatorCampaignCoverage, CampaignCommitPrefixes, CommitPrefixCoverage, CoveredPrefix

LEMMA CurrentCausalCampaignsWithoutPromotion ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW campaigns, CurrentCausalCampaigns(campaigns),
           ~\E leader \in Server: BecomeLeader(leader)
    PROVE CurrentCausalCampaigns(campaigns)'
<1>base. TypeOK /\ MembershipCampaignsInv(voteHistory)
    BY JointCoreBase, SMT
<1> SUFFICES ASSUME NEW leader \in Server, state'[leader] = Leader
             PROVE \E campaign \in campaigns:
                       /\ campaign.candidate = leader /\ campaign.term = currentTerm'[leader]
                       /\ campaign.snapshot = CampaignPrefix(log'[leader], currentTerm'[leader])
    BY SMT DEF CurrentCausalCampaigns
<1>continues. state[leader] = Leader
    BY <1>base, NewLeaderUsesBecomeLeader, SMT
<1>campaign. PICK campaign \in campaigns:
        /\ campaign.candidate = leader /\ campaign.term = currentTerm[leader]
        /\ campaign.snapshot = CampaignPrefix(log[leader], currentTerm[leader])
    BY <1>continues, SMT DEF CurrentCausalCampaigns
<1>epoch. currentTerm'[leader] = currentTerm[leader]
    BY <1>base, <1>continues, ContinuingLeaderTermNext, SMT
<1>snapshot. CampaignPrefix(log'[leader], currentTerm'[leader]) = CampaignPrefix(log[leader], currentTerm[leader])
    BY <1>base, <1>continues, ContinuingLeaderCampaignPrefix, SMT
<1> QED BY <1>campaign, <1>epoch, <1>snapshot, SMT

LEMMA CurrentLeaderRecordedSupportSuppliesCampaignIntersections ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, NEW campaigns,
           CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns), NEW leader \in Server,
           state[leader] = Leader, NEW term \in Nat, currentTerm[leader] = term,
           NEW target \in Seq(LogEntry), NEW support,
           support \subseteq RecordedReplicationSupport(leader, term, Len(target))
    PROVE RecordedTargetCampaignIntersections(leader, term, target, support, campaigns)
<1>base. TypeOK /\ SendInvariant BY JointCoreBase, SMT
<1> SUFFICES ASSUME NEW campaign \in campaigns, term < campaign.term,
                      NEW peer \in support \cap campaign.support
             PROVE \E response \in messages:
                       /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
                       /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
    BY SMT DEF RecordedTargetCampaignIntersections
<1>vote. peer \in Server /\ RecordedCampaignVote(voteHistory, peer, campaign.candidate, campaign.term)
          /\ campaign.candidate \in Server /\ campaign.term \in Nat
    BY SMT DEF CausalCampaignWitnesses, CausalCampaignData, CausalElectionCertificate,
        RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
<1>other. peer # leader BY <1>base, <1>vote, RecordedCampaignVoteTermBound, SMT
<1> QED BY <1>other, SMT DEF RecordedReplicationSupport, RecordedAcknowledgment

LEMMA CausalCampaignProtectionSuppliesAncestryAndRequests ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           NEW leader \in Server, state[leader] = Leader, NEW term \in Nat, currentTerm[leader] = term,
           NEW target \in Seq(LogEntry), IsPrefix(target, log[leader]),
           \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
    PROVE LaterTermPrefixProtection(ancestry, target, term) /\ ProtectedAppendRequests(target, term)
<1>base. TypeOK /\ ReplicationPrefixInv(voteHistory) /\ CurrentRequestSendersUnique
    BY JointCoreBase, IntersectingRequestCertificatesIdentifySenders, SMT DEF MembershipJointCore
<1>ancestry. LaterTermPrefixProtection(ancestry, target, term)
    BY SequencePrefixTransitive, SMT
    DEF CausalCampaignWitnesses, CausalCampaignData, CreatorCampaignCoverage, LaterTermPrefixProtection,
        JointMembershipWitnesses, CertificateFamily, CertificateWitness, WitnessPrefixData
<1>requests. ProtectedAppendRequests(target, term)
    <2> SUFFICES ASSUME NEW request \in AppendRequests, request.mterm >= term
                 PROVE RequestRespectsPrefix(request, target) BY SMT DEF ProtectedAppendRequests
    <2>fields. request.mterm \in Nat /\ request.mentries \in Seq(LogEntry)
        BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
    <2>same. CASE request.mterm = term
        BY <1>base, <2>same, SameTermRequestRespectsLeaderPrefix, SMT
    <2>higher. CASE term < request.mterm
        <3>campaign. PICK campaign, prefix:
                /\ campaign \in campaigns /\ prefix \in Seq(LogEntry)
                /\ campaign.term = request.mterm /\ RequestPrefixData(request, prefix)
                /\ (IsPrefix(campaign.snapshot, prefix) \/ IsPrefix(prefix, campaign.snapshot))
            BY SMT DEF CausalCampaignWitnesses, RequestCampaignCoverage
        <3>target. IsPrefix(target, campaign.snapshot)
            BY <2>higher, <3>campaign, SMT
        <3> QED BY <2>fields, <3>campaign, <3>target, ComparableRequestPrefixRespectsTarget, SMT
            DEF CausalCampaignWitnesses, CausalCampaignData
    <2> QED BY <2>fields, <2>same, <2>higher, SMT
<1> QED BY <1>ancestry, <1>requests, SMT

LEMMA RecordedVoteFreshForProtectedAcknowledgment ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), AcknowledgmentVoteCutHistory(voteHistory), NEW leader \in Server,
           state[leader] = Leader, NEW term \in Nat, currentTerm[leader] = term,
           NEW target \in Seq(LogEntry), IsPrefix(target, log[leader]), ProtectedAppendRequests(target, term),
           NEW candidate \in Server, NEW later \in Nat, term < later, NEW snapshot \in Seq(LogEntry),
           RecordedCampaignRequests(candidate, later) = CampaignRequests(candidate, later, snapshot),
           HistoryCampaignSnapshot(voteHistory, candidate, later, snapshot),
           NEW peer \in RecordedReplicationSupport(leader, term, Len(target)),
           RecordedCampaignVote(voteHistory, peer, candidate, later)
    PROVE SnapshotCoversPrefix(snapshot, target)
<1>base. TypeOK /\ SendInvariant /\ peer \in Server
    BY JointCoreBase, SMT DEF RecordedReplicationSupport
<1>other. peer # leader BY <1>base, RecordedCampaignVoteTermBound, SMT
<1>response. PICK response \in messages:
        /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
        /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
    BY <1>other, SMT DEF RecordedReplicationSupport, RecordedAcknowledgment
<1>prefix. PICK prefix \in Seq(LogEntry):
        /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log[leader])
        /\ AcknowledgmentVoteCuts(voteHistory, prefix, peer, term)
    BY <1>response, SMT DEF AcknowledgmentVoteCutHistory
<1>inside. IsPrefix(target, prefix)
    BY <1>base, <1>response, <1>prefix, PrefixesWithBoundedLength, SMT DEF TypeOK, LogVarsTypeOK
<1>no_conflict. ~ConflictingRequestBeforeVote(peer, term, later, target)
    BY MessageFieldsTypeOK, SMT
    DEF ProtectedAppendRequests, ConflictingRequestBeforeVote, AppendRequests, TypeOK, MsgTypeOK
<1>request. PICK request \in RecordedVoteRequests(voteHistory, candidate, later): VoteRequestCoversPrefix(request, target)
    BY <1>prefix, <1>inside, <1>no_conflict, SMT DEF AcknowledgmentVoteCuts
<1> QED BY <1>request, RecordedVoteRequestsUseSnapshot, JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv, CampaignRequests, RecordedVoteRequests, HistoryCampaignSnapshot, CampaignHistory, CampaignHistoryRecord, SnapshotCoversPrefix, VoteRequestCoversPrefix

LEMMA HistoryProtectsAcknowledgersWithProtectedRequests ==
    ASSUME AcknowledgmentPrefixHistory, TypeOK, NEW leader \in Server, state[leader] = Leader,
           NEW term \in Nat, term = currentTerm[leader], NEW target \in Seq(LogEntry),
           IsPrefix(target, log[leader]), ProtectedAppendRequests(target, term)
    PROVE RecordedAcknowledgersProtected(leader, term, target)
<1> SUFFICES ASSUME NEW peer \in RecordedReplicationSupport(leader, term, Len(target))
             PROVE peer \in ProtectedVoters(target)
    BY SMT DEF RecordedAcknowledgersProtected
<1>typed. peer \in Server BY SMT DEF RecordedReplicationSupport
<1>self. CASE peer = leader
    BY <1>typed, <1>self, SMT DEF ProtectedVoters
<1>other. CASE peer # leader
    <2>response. PICK response \in messages:
            /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
            /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        BY <1>other, SMT DEF RecordedReplicationSupport, RecordedAcknowledgment
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log[leader])
            /\ \A shorter \in Seq(LogEntry): IsPrefix(shorter, prefix) =>
                   IsPrefix(shorter, log[peer]) \/ ConflictingHigherAppendRequest(peer, term, shorter)
        BY <2>response, SMT DEF AcknowledgmentPrefixHistory
    <2>contains. IsPrefix(target, prefix)
        BY <2>response, <2>prefix, PrefixesWithBoundedLength, SMT DEF TypeOK, LogVarsTypeOK
    <2>no_conflict. ~ConflictingHigherAppendRequest(peer, term, target)
        BY MessageFieldsTypeOK, SMT
        DEF ProtectedAppendRequests, ConflictingHigherAppendRequest, AppendRequests, TypeOK, MsgTypeOK
    <2> QED BY <1>typed, <2>prefix, <2>contains, <2>no_conflict, SMT DEF ProtectedVoters
<1> QED BY <1>self, <1>other, SMT

LEMMA CausalWitnessesProtectPendingTarget ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           AcknowledgmentVoteCutHistory(voteHistory), AcknowledgmentPrefixHistory,
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           FrozenRequestPrefixesAgree(ancestry),
           NEW leader \in Server, state[leader] = Leader, NEW term \in Nat, currentTerm[leader] = term,
           NEW target \in Seq(LogEntry), Len(target) > 0, LastTerm(target) = term,
           IsPrefix(target, log[leader]), NEW support,
           support \in Quorums(ConfigOf(log[leader])),
           support \subseteq RecordedReplicationSupport(leader, term, Len(target))
    PROVE PendingTargetProtection(voteHistory, ancestry, leader, term, target)
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>base. TypeOK /\ MembershipCampaignsInv(voteHistory) /\ SendInvariant /\ EntryEdgeBase /\ ReplicationPrefixInv(voteHistory)
          /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
          /\ WitnessEdgeConsistency(ancestry)
          /\ log[leader] \in Seq(LogEntry) /\ TermsOrdered(log[leader])
    BY <1>old, JointCoreBase, OrderedTermPrefixesAreEdgeConsistent, SMT
    DEF JointMembershipWitnesses, MembershipJointCore, MembershipCampaignsInv, TermOrderingInv,
        LogTermsMonotonic, TermsOrdered, TypeOK, LogVarsTypeOK
<1>prefix. CoveredPrefix(ancestry, target) /\ TargetCampaignEvidence(voteHistory, leader, term, target)
    BY <1>old, <1>base, CurrentLogPrefixCovered, CurrentLeaderTargetHasCampaignEvidence, SMT
    DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK
<1>profile. TermProtectedPrefix(ancestry, commits, term, log[leader])
    BY <1>old, CurrentLeaderSuppliesTermProtectedPrefix, SMT
<1>intersections. RecordedTargetCampaignIntersections(leader, term, target, support, campaigns)
    BY CurrentLeaderRecordedSupportSuppliesCampaignIntersections, SMT
<1>campaigns. \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
    BY <1>old, <1>prefix, <1>profile, <1>intersections, CausalCampaignsProtectRecordedTarget, SMT
<1>protection. LaterTermPrefixProtection(ancestry, target, term) /\ ProtectedAppendRequests(target, term)
    BY <1>old, <1>campaigns, CausalCampaignProtectionSuppliesAncestryAndRequests, SMT
<1>boundary. LaterTermPrefixProtection(ancestry, target, term) BY <1>protection, SMT
<1>holders. RecordedAcknowledgersProtected(leader, term, target)
    BY <1>base, <1>protection, HistoryProtectsAcknowledgersWithProtectedRequests, SMT
<1>target. TermsOrdered(target) /\ CoveredPrefix(ancestry, target) /\ IsPrefix(target, target)
    BY <1>base, <1>old, CurrentLogPrefixCovered, TermsOrderedOnPrefix,
       WholeSequencePrefix, LenProperties, SMT DEF JointMembershipWitnesses, IsPrefix
<1>eligible. EligibleCampaignsProtectTarget(voteHistory, target, term)
    <2> SUFFICES ASSUME NEW candidate \in Server, NEW later \in Nat,
                          NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW votes,
                          OpportunityCertificate(voteHistory, candidate, later, snapshot, occurrence, votes),
                          term <= later, ~IsPrefix(target, log[candidate])
                 PROVE FALSE
        BY SMT DEF EligibleCampaignsProtectTarget
    <2>snapshot. IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot)
        BY <1>old, CampaignOpportunitySnapshotCovered, SMT DEF OpportunityCertificate
    <2>same. CASE later = term
        <3>identity. candidate = leader
            BY <2>same, CurrentLeaderOpportunityIdentifiesCandidate, SMT
            DEF JointOpportunityWitnesses, OpportunityRelations
        <3> QED BY <3>identity, SMT
    <2>later. CASE term < later
        <3>bound. LastTerm(snapshot) <= term
            <4> SUFFICES ASSUME LastTerm(snapshot) > term PROVE FALSE BY LastTermTypeOK, SMT
            <4>last. Len(snapshot) > 0 BY LastTermTypeOK, LenProperties, SMT DEF LastTerm
            <4>witness. PICK witness \in ancestry: witness.prefix = snapshot /\ witness.edge.term = LastTerm(snapshot)
                BY <1>old, <1>base, <2>snapshot, <4>last, CoveredSequenceHasLastWitness, SMT
                DEF JointMembershipWitnesses
            <4>contains. IsPrefix(target, snapshot)
                BY <1>boundary, <4>witness, SMT DEF LaterTermPrefixProtection
            <4> QED BY <1>base, <2>snapshot, <4>contains, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
        <3>profile. TermProtectedPrefix(ancestry, commits, term, snapshot)
            BY <2>later, <3>bound, HigherOpportunitySnapshotSuppliesTermProtectedPrefix, SMT
        <3>shape. EqualOrAdjacentConfigurations(ConfigOf(log[leader]), ConfigOf(snapshot))
            BY <1>old, <1>profile, <3>profile, TermProtectedConfigurationsAreEqualOrAdjacent, SMT
        <3>votes. votes \in Quorums(ConfigOf(snapshot))
                  /\ ConfigOf(snapshot) \subseteq Server /\ ConfigOf(log[leader]) \subseteq Server
            BY <1>base, ConfigurationType, SMT DEF OpportunityCertificate, LatestConfigurationOccurrence,
                TypeOK, LogVarsTypeOK
        <3>shared. PICK peer \in support \cap votes: TRUE
            BY <3>shape, <3>votes, EqualOrAdjacentQuorumsIntersect, SMT
        <3>holder. peer \in Server /\ IsPrefix(target, log[peer])
                  /\ peer \in RecordedReplicationSupport(leader, term, Len(target))
            BY <1>holders, <3>shared, SMT DEF RecordedAcknowledgersProtected, ProtectedVoters
        <3>recorded. CASE RecordedCampaignVote(voteHistory, peer, candidate, later)
            <4>campaign. RecordedCampaignRequests(candidate, later) = CampaignRequests(candidate, later, snapshot)
                          /\ HistoryCampaignSnapshot(voteHistory, candidate, later, snapshot)
                BY <1>base, <3>holder, <3>recorded, RecordedCampaignVoteCandidateTermBound, RecordedOpportunityUsesHistorySnapshot, SMT
                DEF OpportunityCertificate, CampaignOpportunity, MembershipCampaignsInv,
                    TypeOK, ServerVarsTypeOK
            <4>fresh. LastTerm(snapshot) > LastTerm(target)
                     \/ (LastTerm(snapshot) = LastTerm(target) /\ Len(snapshot) >= Len(target))
                BY <2>later, <3>holder, <3>recorded, <4>campaign,
                   <1>protection, RecordedVoteFreshForProtectedAcknowledgment, SMT DEF SnapshotCoversPrefix
            <4>contains. IsPrefix(target, snapshot)
                BY <1>boundary, <1>base, <1>target, <2>snapshot, <4>fresh,
                   FreshCoveredSequenceContainsTarget, SMT
            <4> QED BY <1>base, <2>snapshot, <4>contains, SequencePrefixTransitive, SMT
                DEF TypeOK, LogVarsTypeOK
        <3>self. CASE peer = candidate
            BY <3>holder, <3>self, SMT
        <3>fresh. CASE NewPeerVoteEligible(peer, candidate, later, snapshot)
            <4>covered. CoveredPrefix(ancestry, log[peer])
                BY <1>old, <1>base, <3>holder, CurrentLogPrefixCovered,
                   WholeSequencePrefix, LenProperties, SMT DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK, IsPrefix
            <4>ordered. TermsOrdered(log[peer])
                BY <1>base, <3>holder, SMT DEF MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
            <4>contains. IsPrefix(target, snapshot)
                BY <1>base, <1>boundary, <1>target, <2>snapshot, <3>holder, <3>fresh, <4>covered, <4>ordered,
                   FreshCoveredSequenceContainsTarget, SMT
                DEF NewPeerVoteEligible, SnapshotFreshFor, TypeOK, LogVarsTypeOK
            <4> QED BY <1>base, <2>snapshot, <4>contains, SequencePrefixTransitive, SMT
                DEF TypeOK, LogVarsTypeOK
        <3> QED BY <3>shared, <3>recorded, <3>self, <3>fresh, SMT
            DEF OpportunityCertificate, OpportunityVoters
    <2> QED BY <2>same, <2>later, SMT
<1>leaders. ProtectedLeaders(target, term)
    <2> SUFFICES ASSUME NEW other \in Server, state[other] = Leader, currentTerm[other] >= term
                 PROVE IsPrefix(target, log[other])
        BY SMT DEF ProtectedLeaders
    <2>epoch. currentTerm[other] \in Nat BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK
    <2>certificate. PICK snapshot, occurrence, votes:
            /\ snapshot \in Seq(LogEntry)
            /\ CurrentElectionCertificate(voteHistory, other, currentTerm[other], snapshot, occurrence, votes)
        BY <1>base, CurrentLeaderHasElectionCertificate, SMT
    <2>opportunity. OpportunityCertificate(voteHistory, other, currentTerm[other], snapshot, occurrence, votes)
        BY <2>certificate, <2>epoch, CurrentCertificateIsReady, ReadyCertificateUsesOpportunity, SMT
    <2> QED BY <1>eligible, <2>certificate, <2>epoch, <2>opportunity, SMT DEF EligibleCampaignsProtectTarget
<1> QED BY <1>boundary, <1>protection, <1>holders, <1>eligible, <1>leaders, SMT DEF PendingTargetProtection

LEMMA CausalWitnessesSupplyPendingProtection ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           AcknowledgmentVoteCutHistory(voteHistory), AcknowledgmentPrefixHistory,
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns), FrozenRequestPrefixesAgree(ancestry)
    PROVE JointPendingProtection(voteHistory, ancestry) /\ CampaignPendingPrefixes(campaigns)
<1> SUFFICES ASSUME NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
                      PendingAgreement(leader, term, target)
             PROVE PendingTargetProtection(voteHistory, ancestry, leader, term, target)
                   /\ \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
    BY SMT DEF JointPendingProtection, CampaignPendingPrefixes
<1>quorum. PICK support:
        /\ support \in Quorums(ConfigOf(log[leader]))
        /\ support \subseteq RecordedAgreementSupport(leader, term, target)
    BY SMT DEF PendingAgreement
<1>numeric. support \subseteq RecordedReplicationSupport(leader, term, Len(target))
    BY <1>quorum, SMT DEF RecordedAgreementSupport, RecordedReplicationSupport,
        RecordedAcknowledgment, RecordedPrefixAcknowledgment
<1>protection. PendingTargetProtection(voteHistory, ancestry, leader, term, target)
    BY <1>quorum, <1>numeric, CausalWitnessesProtectPendingTarget, SMT DEF PendingAgreement
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>prefix. CoveredPrefix(ancestry, target) /\ TargetCampaignEvidence(voteHistory, leader, term, target)
    BY <1>old, JointCoreBase, CurrentLogPrefixCovered, CurrentLeaderTargetHasCampaignEvidence, SMT
    DEF JointMembershipWitnesses, PendingAgreement, TypeOK, LogVarsTypeOK
<1>profile. TermProtectedPrefix(ancestry, commits, term, log[leader])
    BY <1>old, CurrentLeaderSuppliesTermProtectedPrefix, SMT DEF PendingAgreement
<1>intersections. RecordedTargetCampaignIntersections(leader, term, target, support, campaigns)
    BY <1>numeric, CurrentLeaderRecordedSupportSuppliesCampaignIntersections, SMT DEF PendingAgreement
<1>campaigns. \A campaign \in campaigns: term < campaign.term => IsPrefix(target, campaign.snapshot)
    BY <1>old, <1>prefix, <1>profile, <1>quorum, <1>intersections,
       CausalCampaignsProtectRecordedTarget, SMT DEF PendingAgreement
<1> QED BY <1>protection, <1>campaigns, SMT

LEMMA PromotionExtendsCausalCampaigns ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns), CurrentCausalCampaigns(campaigns),
           FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry), RequestSourceVoteCutHistory(voteHistory, ancestry),
           LocalAppendVoteCutHistory(voteHistory), NEW actor \in Server, BecomeLeader(actor)
    PROVE \E fresh:
              /\ CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns \cup {fresh})'
              /\ CurrentCausalCampaigns(campaigns \cup {fresh})'
<1>next. [Next]_vars BY SMT DEF Next
<1>base. TypeOK /\ MembershipCampaignsInv(voteHistory) /\ JointMembershipWitnesses(voteHistory, ancestry, commits)
          /\ currentTerm[actor] \in Nat /\ state[actor] = Candidate
    BY JointCoreBase, SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses, BecomeLeader,
        TypeOK, ServerVarsTypeOK
<1>term. PICK term \in Nat: term = currentTerm[actor] BY <1>base, SMT
<1>chosen. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ ReadyElectionCertificate(voteHistory, actor, term, snapshot, occurrence, support)
    BY <1>base, <1>term, WinningCandidateHasReadyCertificate, SMT
<1>certificate. CausalElectionCertificate(voteHistory, ancestry, actor, term, snapshot, occurrence, support)
    BY <1>base, <1>term, <1>chosen, ReadyCandidateCapturesCausalCertificate, SMT
    DEF JointOpportunityWitnesses, OpportunityRelations
<1>source_cut. RequestSourceElectionCut(ancestry, actor, term, snapshot, support)
    BY <1>base, <1>term, <1>chosen, ReadyCandidateCapturesRequestSourceCut, SMT
    DEF JointOpportunityWitnesses, OpportunityRelations
<1>local_cut. LocalAppendElectionCut(voteHistory, term, snapshot, support)
    BY <1>base, <1>chosen, ReadyCandidateCapturesLocalAppendCut, SMT
    DEF JointOpportunityWitnesses, OpportunityRelations
<1>opportunity. OpportunityCertificate(voteHistory, actor, term, snapshot, occurrence, support)
    BY <1>chosen, ReadyCertificateUsesOpportunity, SMT
<1>prefix. CoveredPrefix(ancestry, snapshot) /\ TermsOrdered(snapshot)
    BY <1>base, <1>chosen, <1>opportunity, CampaignOpportunitySnapshotCovered, TermsOrderedOnPrefix, LenProperties, SMT
    DEF OpportunityCertificate, MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered,
        TypeOK, LogVarsTypeOK, IsPrefix
<1> DEFINE fresh == [candidate |-> actor, term |-> term, snapshot |-> snapshot,
                     occurrence |-> occurrence, support |-> support]
<1>fresh. CausalCampaignData(nextVoteHistory, ancestry, fresh)'
    BY <1>base, <1>chosen, <1>next, <1>certificate, <1>source_cut, <1>local_cut, <1>prefix,
       CausalElectionCertificateNext, RequestSourceElectionCutNext, LocalAppendElectionCutNext, SMT
    DEF fresh, CausalCampaignData, CausalElectionCertificate, CoveredPrefix, TermsOrdered, BecomeLeader
<1>old. CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>next, <1>base, CausalCampaignWitnessesNext, SMT
<1>commits. \A certificate \in commits:
        certificate.term < fresh.term => IsPrefix(CommitTarget(certificate), fresh.snapshot)
    <2> SUFFICES ASSUME NEW certificate \in commits, certificate.term < fresh.term
                 PROVE IsPrefix(CommitTarget(certificate), fresh.snapshot) BY SMT
    <2>data. RetainedCommitCertificate(voteHistory, certificate)
        BY <1>base, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
    <2>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
              /\ LastTerm(CommitTarget(certificate)) = certificate.term
        BY <2>data, CommitCertificateTargetProperties, LenProperties, SMT DEF RetainedCommitCertificate, LastTerm
    <2>held. IsPrefix(CommitTarget(certificate), log[actor])
        BY <1>base, <1>term, <1>chosen, <1>opportunity, <2>data, SMT
        DEF fresh, JointOpportunityWitnesses, OpportunityRelations, OpportunityCommitPrefixes, RetainedCommitCertificate
    <2> QED BY <1>term, <1>chosen, <1>opportunity, <1>base, <2>data, <2>target, <2>held, CampaignContainsOlderProtectedPrefix, SMT
        DEF fresh, OpportunityCertificate
<1>witnesses. CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns \cup {fresh})'
    BY <1>old, <1>fresh, <1>commits, SMT
    DEF CausalCampaignWitnesses, CreatorCampaignCoverage, RequestCampaignCoverage, CampaignCommitPrefixes
<1>current. CurrentCausalCampaigns(campaigns \cup {fresh})'
    <2> SUFFICES ASSUME NEW leader \in Server, state'[leader] = Leader
                 PROVE \E campaign \in campaigns \cup {fresh}:
                     /\ campaign.candidate = leader /\ campaign.term = currentTerm'[leader]
                     /\ campaign.snapshot = CampaignPrefix(log'[leader], currentTerm'[leader])
        BY SMT DEF CurrentCausalCampaigns
    <2>frame. UNCHANGED <<currentTerm, log>> BY SMT DEF BecomeLeader
    <2>snapshot. snapshot = CampaignPrefix(log[actor], term)
        BY <1>chosen, SMT DEF ReadyElectionCertificate
    <2>self. CASE leader = actor
        BY <1>term, <2>frame, <2>snapshot, <2>self, SMT DEF fresh
    <2>other. CASE leader # actor
        <3>before. state[leader] = Leader
            BY <1>base, <2>other, SMT DEF BecomeLeader, TypeOK, ServerVarsTypeOK
        <3>witness. PICK campaign \in campaigns:
                /\ campaign.candidate = leader /\ campaign.term = currentTerm[leader]
                /\ campaign.snapshot = CampaignPrefix(log[leader], currentTerm[leader])
            BY <3>before, SMT DEF CurrentCausalCampaigns
        <3> QED BY <2>frame, <3>witness, SMT
    <2> QED BY <2>self, <2>other, SMT
<1> QED BY <1>witnesses, <1>current, SMT

LEMMA CoveredRequestDataPrefixIsUnique ==
    ASSUME NEW ancestry, WitnessEdgeConsistency(ancestry), NEW request, request.mentries \in Seq(LogEntry),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           RequestPrefixData(request, left), RequestPrefixData(request, right),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right)
    PROVE left = right
<1>length. Len(left) = Len(right) /\ Len(left) \in Nat
    BY LenProperties, SMT DEF RequestPrefixData
<1>empty. CASE Len(left) = 0 BY <1>length, <1>empty, EmptySeq, SMT
<1>nonempty. CASE Len(left) > 0
    <2>entries. CASE Len(request.mentries) > 0
        <3> QED BY <1>length, <1>nonempty, <2>entries, CoveredPrefixesMatch,
            WholeSequencePrefix, LenProperties, SMT DEF RequestPrefixData, LastTerm
    <2>anchor. CASE Len(request.mentries) = 0
        <3> QED BY <1>length, <1>nonempty, <2>anchor, CoveredPrefixesMatch,
            WholeSequencePrefix, LenProperties, SMT DEF RequestPrefixData
    <2> QED BY <2>entries, <2>anchor, LenProperties, SMT
<1> QED BY <1>empty, <1>nonempty, SMT

LEMMA PostFrozenHistoriesLiftToLargerFamily ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK', NEW ancestry, NEW larger, ancestry \subseteq larger,
           PrefixWitnessFamilyData(larger), TermPrefixOrder(larger), RequestPrefixAncestry(nextVoteHistory, ancestry)',
           FrozenRequestPrefixesAgree(ancestry)', FrozenAcknowledgmentPrefixHistory(ancestry)',
           FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, ancestry)'
    PROVE FrozenRequestPrefixesAgree(larger)' /\ FrozenAcknowledgmentPrefixHistory(larger)'
          /\ FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, larger)'
<1>consistent. WitnessEdgeConsistency(larger) BY DataFamilyEdgeConsistency, SMT
<1>requests. FrozenRequestPrefixesAgree(larger)'
    <2> SUFFICES ASSUME NEW left \in AppendRequests', NEW right \in AppendRequests', left.mterm = right.mterm,
                          NEW leftPrefix \in Seq(LogEntry), NEW rightPrefix \in Seq(LogEntry),
                          RequestPrefixData(left, leftPrefix), CoveredPrefix(larger, leftPrefix),
                          RequestPrefixData(right, rightPrefix), CoveredPrefix(larger, rightPrefix)
                 PROVE IsPrefix(leftPrefix, rightPrefix) \/ IsPrefix(rightPrefix, leftPrefix)
        BY SMT DEF FrozenRequestPrefixesAgree, RequestPrefixData, CoveredPrefix
    <2>left_ancestry. AncestralRequestPrefix(nextVoteHistory, ancestry, left)'
        BY SMT DEF RequestPrefixAncestry
    <2>right_ancestry. AncestralRequestPrefix(nextVoteHistory, ancestry, right)'
        BY SMT DEF RequestPrefixAncestry
    <2>left. PICK oldLeft \in Seq(LogEntry):
            RequestPrefixData(left, oldLeft) /\ CoveredPrefix(ancestry, oldLeft)
        BY <2>left_ancestry, SMTT(10)
        DEF AncestralRequestPrefix, RequestPrefixData, CoveredPrefix
    <2>right. PICK oldRight \in Seq(LogEntry):
            RequestPrefixData(right, oldRight) /\ CoveredPrefix(ancestry, oldRight)
        BY <2>right_ancestry, SMTT(10)
        DEF AncestralRequestPrefix, RequestPrefixData, CoveredPrefix
    <2>frozen. RequestPrefixData(left, oldLeft) /\ CoveredPrefix(ancestry, oldLeft)
               /\ RequestPrefixData(right, oldRight) /\ CoveredPrefix(ancestry, oldRight)
        BY <2>left, <2>right, SMT
    <2>covered. CoveredPrefix(larger, oldLeft) /\ CoveredPrefix(larger, oldRight)
        BY <2>frozen, CoveredPrefixFamilyExtension, SMT
    <2>equal. oldLeft = leftPrefix /\ oldRight = rightPrefix
        BY <1>consistent, <2>frozen, <2>covered, MessageFieldsTypeOK, CoveredRequestDataPrefixIsUnique, SMT
        DEF TypeOK, MsgTypeOK, AppendRequests
    <2> QED BY <2>frozen, <2>equal, SMT DEF FrozenRequestPrefixesAgree, RequestPrefixData, CoveredPrefix
<1>covered. \A prefix \in Seq(LogEntry): CoveredPrefix(ancestry, prefix)' => CoveredPrefix(larger, prefix)'
    BY SMT DEF CoveredPrefix
<1> QED BY <1>requests, <1>covered, SMT
    DEF FrozenAcknowledgmentPrefixHistory, FrozenAcknowledgmentVoteCutHistory

LEMMA CausalMetadataFrameWithoutPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           ~\E leader \in Server: BecomeLeader(leader)
    PROVE CausalHistoryData(nextVoteHistory, ancestry, commits, campaigns)'
    BY FrozenRequestAgreementNext, FrozenAcknowledgmentPrefixHistoryNext, FrozenAcknowledgmentVoteCutHistoryNext,
       CausalCampaignWitnessesNext, CurrentCausalCampaignsWithoutPromotion, AppendRequestOwnersUniqueNext,
       RequestSourceHistoriesNext, LocalAppendOwnersNext, LocalAppendPrefixHistoryNext, LocalAppendVoteCutHistoryNext, SMT
    DEF CausalHistoryMetadata, CausalHistoryData

LEMMA CausalMetadataWithoutPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars,
           NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           ~(\E leader \in Server: BecomeLeader(leader)),
           ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    PROVE CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
    BY JointCoreBase, CausalMetadataFrameWithoutPromotion, LocalAppendCoverageWithoutClient, SMT
    DEF CausalHistoryMetadata, CausalHistoryData, LocalAppendRecordsCovered

LEMMA CausalMetadataPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, BecomeLeader(actor)
    PROVE \E fresh: CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns \cup {fresh})'
<1>next. [Next]_vars BY SMT DEF Next
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits) BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>histories. FrozenRequestPrefixesAgree(ancestry)' /\ FrozenAcknowledgmentPrefixHistory(ancestry)'
             /\ FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, ancestry)' /\ AppendRequestOwnersUnique'
             /\ RequestSourcePrefixHistory(ancestry)' /\ RequestSourceVoteCutHistory(nextVoteHistory, ancestry)'
    BY <1>old, <1>next, FrozenRequestAgreementNext, FrozenAcknowledgmentPrefixHistoryNext,
       FrozenAcknowledgmentVoteCutHistoryNext, AppendRequestOwnersUniqueNext, RequestSourceHistoriesNext, SMT
    DEF CausalHistoryMetadata
<1>fresh. PICK fresh:
        /\ CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns \cup {fresh})'
        /\ CurrentCausalCampaigns(campaigns \cup {fresh})'
    BY PromotionExtendsCausalCampaigns, SMT DEF CausalHistoryMetadata
<1>finite. IsFiniteSet(campaigns \cup {fresh})
    BY FS_AddElement, SMT DEF CausalHistoryMetadata
<1>base. TypeOK BY JointCoreBase, SMT
<1>no_client. ~(\E leader \in Server, payload \in ClientPayload: ClientRequest(leader, payload))
    BY <1>base, ServerStatesDistinct, SMT DEF BecomeLeader, ClientRequest, TypeOK, ServerVarsTypeOK
<1>local_coverage. LocalAppendRecordsCovered(nextVoteHistory, ancestry)
    BY <1>base, <1>no_client, LocalAppendCoverageWithoutClient, SMT DEF CausalHistoryMetadata
<1>local. /\ LocalAppendRequestOwnersUnique(nextVoteHistory)'
           /\ LocalAppendPrefixHistory(nextVoteHistory)' /\ LocalAppendVoteCutHistory(nextVoteHistory)'
    BY <1>old, <1>next, LocalAppendOwnersNext, LocalAppendPrefixHistoryNext, LocalAppendVoteCutHistoryNext, SMT
    DEF CausalHistoryMetadata
<1> QED BY <1>histories, <1>fresh, <1>finite, <1>local_coverage, <1>local, SMT
    DEF CausalHistoryMetadata, LocalAppendRecordsCovered

LEMMA CausalMetadataClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           fresh.prefix = log'[actor], fresh.edge.term = currentTerm[actor], fresh.owner = actor,
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)'
    PROVE CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
<1>next. [Next]_vars BY SMT DEF Next
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ ReplicationEvidenceInv(voteHistory)
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>no_promotion. ~\E leader \in Server: BecomeLeader(leader)
    BY <1>base, ServerStatesDistinct, SMT DEF ClientRequest, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>old. CausalHistoryData(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>next, <1>no_promotion, CausalMetadataFrameWithoutPromotion, SMT
<1>pure. PrefixWitnessFamilyData(ancestry \cup {fresh}) /\ TermPrefixOrder(ancestry \cup {fresh})
    BY SMT DEF JointMembershipData, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData,
        WitnessPrefixData, TermPrefixOrder
<1>requests. RequestPrefixAncestry(nextVoteHistory, ancestry)'
    BY <1>next, <1>base, RequestPrefixAncestryNext, SMT DEF JointMembershipWitnesses
<1>subset. ancestry \subseteq ancestry \cup {fresh} BY SMT
<1>old_histories. FrozenRequestPrefixesAgree(ancestry)' /\ FrozenAcknowledgmentPrefixHistory(ancestry)'
                   /\ FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, ancestry)'
    BY <1>old, SMT DEF CausalHistoryMetadata, CausalHistoryData
<1>histories. FrozenRequestPrefixesAgree(ancestry \cup {fresh})'
             /\ FrozenAcknowledgmentPrefixHistory(ancestry \cup {fresh})'
             /\ FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>base, <1>subset, <1>old_histories, <1>pure, <1>requests, PostFrozenHistoriesLiftToLargerFamily, SMT
<1>source_histories. RequestSourcePrefixHistory(ancestry \cup {fresh})'
                      /\ RequestSourceVoteCutHistory(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>old, <1>subset, PostRequestSourceHistoriesFamilyExtension, SMT DEF CausalHistoryMetadata, CausalHistoryData
<1>coverage. CreatorCampaignCoverage(ancestry \cup {fresh}, campaigns)
    <2>old. CreatorCampaignCoverage(ancestry, campaigns)
        BY SMT DEF CausalHistoryMetadata, CausalHistoryData, CausalCampaignWitnesses
    <2>campaign. PICK campaign \in campaigns:
            /\ campaign.candidate = actor /\ campaign.term = currentTerm[actor]
            /\ campaign.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
        BY SMT DEF CausalHistoryMetadata, CausalHistoryData, CurrentCausalCampaigns, ClientRequest
    <2>canonical. fresh.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
        BY <1>base, <1>pure, ClientRequestPreservesCampaignPrefix, SMTT(10)
        DEF PrefixWitnessFamilyData, WitnessPrefixData, ClientRequest
    <2> QED BY <2>old, <2>campaign, <2>canonical, SMT DEF CreatorCampaignCoverage
<1>old_witnesses. CausalCampaignWitnesses(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>old, SMT DEF CausalHistoryMetadata, CausalHistoryData
<1>covered_extension. \A prefix: CoveredPrefix(ancestry, prefix)' => CoveredPrefix(ancestry \cup {fresh}, prefix)'
    BY <1>subset, CoveredPrefixFamilyExtension, SMT
<1>data. \A campaign \in campaigns: CausalCampaignData(nextVoteHistory, ancestry \cup {fresh}, campaign)'
    <2> SUFFICES ASSUME NEW campaign \in campaigns PROVE CausalCampaignData(nextVoteHistory, ancestry \cup {fresh}, campaign)'
        BY SMT
    <2>old. CausalCampaignData(nextVoteHistory, ancestry, campaign)'
        BY <1>old_witnesses, SMT DEF CausalCampaignWitnesses
    <2> QED BY <2>old, <1>covered_extension, SMT
        DEF CausalCampaignData, CausalElectionCertificate, FrozenElectionAcknowledgmentCut, RequestSourceElectionCut
<1>request_coverage. RequestCampaignCoverage(ancestry \cup {fresh}, campaigns)'
    BY <1>old_witnesses, <1>covered_extension, SMT DEF CausalCampaignWitnesses, RequestCampaignCoverage
<1>commit_coverage. CommitPrefixCoverage(ancestry \cup {fresh}, commits)'
    BY <1>old_witnesses, <1>covered_extension, SMT DEF CausalCampaignWitnesses, CommitPrefixCoverage
<1>witnesses. CausalCampaignWitnesses(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
    BY <1>old_witnesses, <1>coverage, <1>data, <1>request_coverage, <1>commit_coverage, SMT
    DEF CausalCampaignWitnesses, CreatorCampaignCoverage
<1>local_coverage. LocalAppendRecordsCovered(nextVoteHistory, ancestry \cup {fresh})
    <2>snapshot. fresh.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
        BY <1>base, <1>pure, ClientRequestPreservesCampaignPrefix, SMT
        DEF PrefixWitnessFamilyData, WitnessPrefixData, ClientRequest
    <2> QED BY <1>base, <2>snapshot, LocalAppendCoverageClient, SMT DEF CausalHistoryMetadata
<1> QED BY <1>local_coverage, <1>old, <1>histories, <1>source_histories, <1>witnesses, SMT DEF CausalHistoryMetadata, CausalHistoryData

LEMMA CausalMetadataCommitCapture ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           AcknowledgmentVoteCutHistory(voteHistory), AcknowledgmentPrefixHistory,
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, AdvanceCommitIndex(actor), NEW fresh, RetainedCommitCertificate(nextVoteHistory, fresh)',
           fresh.leader = actor, fresh.term = currentTerm[actor], fresh.entries = log[actor]
    PROVE CausalHistoryMetadata(nextVoteHistory, ancestry, commits \cup {fresh}, campaigns)'
<1>next. [Next]_vars BY SMT DEF Next
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits) BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>base. TypeOK BY JointCoreBase, SMT
<1>no_promotion. ~\E leader \in Server: BecomeLeader(leader)
    BY <1>base, ServerStatesDistinct, SMT DEF AdvanceCommitIndex, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>no_client. ~(\E leader \in Server, payload \in ClientPayload: ClientRequest(leader, payload))
    BY <1>base, ContinuingLeadersExcludeClientAppend, SMT DEF ContinuingLeadersKeepLogs, AdvanceCommitIndex
<1>retained. CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>next, <1>old, <1>no_promotion, <1>no_client, CausalMetadataWithoutPromotion, SMT
<1>before. RetainedCommitCertificate(voteHistory, fresh)
    BY <1>base, CommitCertificateStateFrame, SMT DEF AdvanceCommitIndex
<1>pending. PendingAgreement(actor, fresh.term, CommitTarget(fresh))
    BY <1>before, OwnedCommitCertificateIsPending, SMT DEF AdvanceCommitIndex
<1>protection. CampaignPendingPrefixes(campaigns)
    BY CausalWitnessesSupplyPendingProtection, SMT DEF CausalHistoryMetadata
<1>new_prefixes. \A campaign \in campaigns: fresh.term < campaign.term => IsPrefix(CommitTarget(fresh), campaign.snapshot)
    BY <1>protection, <1>pending, <1>before, CommitCertificateTargetProperties, SMT
    DEF CampaignPendingPrefixes, RetainedCommitCertificate
<1>covered. CoveredPrefix(ancestry, fresh.entries)
    BY <1>old, <1>base, CurrentLogPrefixCovered, WholeSequencePrefix, LenProperties, SMT
    DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK, IsPrefix
<1> QED BY <1>retained, <1>new_prefixes, <1>covered, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses, CampaignCommitPrefixes, CommitPrefixCoverage, CoveredPrefix

LEMMA AppendReceiveRawAgreementHasCampaignProtection ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW received \in messages, received.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(received.mdest, received.msource, received),
           NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)',
           NEW target \in Seq(LogEntry), certificate.entries = target, certificate.index = Len(target),
           CoveredPrefix(ancestry, target)
    PROVE /\ LaterTermPrefixProtection(ancestry, target, certificate.term)
          /\ ProtectedAppendRequests(target, certificate.term)
          /\ \A campaign \in campaigns: certificate.term < campaign.term => IsPrefix(target, campaign.snapshot)
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits) BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ SendInvariant' /\ ElectionMessagesFrame
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, AppendReceiveElectionFrame, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>data. CommitLogData(certificate)
    BY SMT DEF RetainedCommitCertificate, CommitLogData, CommitPrefixData
<1>target. CommitTarget(certificate) = target /\ Len(target) > 0 /\ LastTerm(target) = certificate.term
            /\ certificate.term \in Nat /\ certificate.leader \in Server
    BY <1>data, CommitLogDataProperties, WholeSequencePrefix, SMT DEF CommitTarget, RetainedCommitCertificate
<1>election. RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term, certificate.snapshot,
                    certificate.electionOccurrence, certificate.election)
    BY <1>base, RetainedCertificateElectionMessagesFrame, SMT DEF RetainedCommitCertificate
<1>campaign. TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, target)
    BY <1>election, SMT DEF TargetCampaignEvidence, RetainedCommitCertificate
<1>support. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, target)
            /\ MixedRecordedTargetCampaignIntersections(certificate.leader, certificate.term, target, certificate.replication, campaigns)
    BY <1>old, <1>target, AppendReceiveCertificateSuppliesMixedSupport, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignRecords
<1>shape. TermProtectedPrefix(ancestry, commits, certificate.term, target)
          \/ SameTermEstablishedPrefix(commits, target, certificate.term)
    BY <1>old, <1>target, RawTargetFitsTermFrontierOrEstablishedPrefix, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>campaigns. \A campaign \in campaigns: certificate.term < campaign.term => IsPrefix(target, campaign.snapshot)
    <2>established. CASE SameTermEstablishedPrefix(commits, target, certificate.term)
        <3>longer. PICK longer \in commits: longer.term = certificate.term /\ IsPrefix(target, CommitTarget(longer))
            BY <2>established, SMT DEF SameTermEstablishedPrefix
        <3>types. CommitTarget(longer) \in Seq(LogEntry)
                  /\ \A campaign \in campaigns: campaign.snapshot \in Seq(LogEntry)
            BY <1>old, <3>longer, RetainedCommitReplicasHoldTarget, SMT
            DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignData
        <3> QED BY <3>longer, <3>types, SequencePrefixTransitive, SMT
            DEF CausalHistoryMetadata, CausalCampaignWitnesses, CampaignCommitPrefixes
    <2>new. CASE TermProtectedPrefix(ancestry, commits, certificate.term, target)
        <3>cuts. CampaignTargetVotingCuts(target, certificate.term, certificate.replication, campaigns)
            BY <1>old, <1>target, <1>campaign, <1>support, MixedSupportSuppliesTargetVotingCuts, SMT
            DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignRecords
        <3>quorum. certificate.replication \in Quorums(ConfigOf(target))
            BY <1>data, SMT DEF CommitLogData, CommitPrefixData, LatestConfigurationOccurrence
        <3> QED BY <1>old, <1>target, <2>new, <3>cuts, <3>quorum,
            CausalCampaignsProtectTargetFromVotingCuts, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignRecords
    <2> QED BY <1>shape, <2>established, <2>new, SMT
<1>history. LaterTermPrefixProtection(ancestry, target, certificate.term)
            /\ ProtectedAppendRequests(target, certificate.term)
    BY <1>old, <1>target, <1>campaign, <1>support, <1>campaigns,
       CampaignProtectedRawTargetHasBoundaryAndRequests, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignRecords
<1> QED BY <1>history, <1>campaigns, SMT

LEMMA AppendReceiveRawAgreementProtectsReadyPrefixes ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW received \in messages, received.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(received.mdest, received.msource, received),
           NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)', NEW target \in Seq(LogEntry),
           certificate.entries = target, certificate.index = Len(target), CoveredPrefix(ancestry, target),
           TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, target),
           LaterTermPrefixProtection(ancestry, target, certificate.term), ProtectedAppendRequests(target, certificate.term)
    PROVE ReadyTargetPrefix(nextVoteHistory, target, certificate.term)'
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits) /\ ReadyAncestryIntersections(voteHistory, ancestry)
          /\ ReadyCommitPrefixes(voteHistory, commits)
    BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses, ReadyMembershipRelations
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ MembershipCampaignsInv(voteHistory) /\ VoteRecordInv(voteHistory)
          /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY <1>old, JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, JointMembershipWitnesses, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>pure. PrefixWitnessFamilyData(ancestry)
    BY <1>old, SMT DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData
<1>frame. NoNewReadyCertificates(voteHistory, nextVoteHistory) /\ ActiveLogsExtend /\ ElectionMessagesFrame
    BY <1>base, ReadyAppendReceiveFrame, AppendReceiveElectionFrame, SMT
<1>data. CommitLogData(certificate) /\ CommitTarget(certificate) = target
          /\ Len(target) > 0 /\ LastTerm(target) = certificate.term /\ certificate.term \in Nat
          /\ certificate.leader \in Server /\ certificate.replication \in Quorums(ConfigOf(target))
    <2>fields.
            /\ certificate.term \in Nat /\ certificate.leader \in Server
            /\ certificate.entries \in Seq(LogEntry)
            /\ certificate.index \in 1..Len(certificate.entries)
            /\ certificate.entries[certificate.index].term = certificate.term
            /\ TermsOrdered(certificate.entries) /\ EntryStructure(certificate.entries, certificate.term)
            /\ certificate.configuration = LatestConfigurationOccurrence(certificate.entries)
            /\ certificate.configuration.members \subseteq Server
            /\ certificate.replication \in Quorums(certificate.configuration.members)
        BY Zenon DEF RetainedCommitCertificate
    <2>log. CommitLogData(certificate) BY <2>fields, SMT DEF CommitLogData, CommitPrefixData
    <2>target. CommitTarget(certificate) = target BY WholeSequencePrefix, SMT DEF CommitTarget
    <2>last. Len(target) > 0 /\ LastTerm(target) = certificate.term
        BY <2>fields, LenProperties, SMT DEF LastTerm
    <2>quorum. certificate.replication \in Quorums(ConfigOf(target))
        BY <2>fields, SMT DEF LatestConfigurationOccurrence
    <2> QED BY <2>fields, <2>log, <2>target, <2>last, <2>quorum, SMT
<1>retained. CertificateFamily(nextVoteHistory, ancestry)'
    BY <1>base, <1>next, CertificateFamilyNext, SMT
<1>history. \A campaign \in campaigns: certificate.term < campaign.term => IsPrefix(target, campaign.snapshot)
    BY <1>data, AppendReceiveRawAgreementHasCampaignProtection, SMT
<1>shape. TermProtectedPrefix(ancestry, commits, certificate.term, target)
          \/ SameTermEstablishedPrefix(commits, target, certificate.term)
    BY <1>old, <1>base, <1>data, RawTargetFitsTermFrontierOrEstablishedPrefix, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1> SUFFICES ASSUME NEW candidate \in Server, NEW later \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support, ReadyElectionCertificate(nextVoteHistory, candidate, later, snapshot, occurrence, support)',
                      certificate.term <= later
             PROVE IsPrefix(target, log'[candidate])
    BY SMT DEF ReadyTargetPrefix
<1>before. ReadyElectionCertificate(voteHistory, candidate, later, snapshot, occurrence, support)
    BY <1>frame, SMT DEF NoNewReadyCertificates
<1>opportunity. OpportunityCertificate(voteHistory, candidate, later, snapshot, occurrence, support)
    BY <1>before, ReadyCertificateUsesOpportunity, SMT
<1>snapshot. IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot)
    BY <1>old, <1>opportunity, CampaignOpportunitySnapshotCovered, SMT DEF OpportunityCertificate
<1>extend. IsPrefix(log[candidate], log'[candidate])
    BY <1>frame, SMT DEF ActiveLogsExtend, ReadyElectionCertificate
<1>same. CASE later = certificate.term
    <2>witness. PICK witness \in ancestry: witness.prefix = target /\ witness.edge.term = certificate.term
        BY <1>base, <1>data, CoveredSequenceHasLastWitness, OrderedTermPrefixesAreEdgeConsistent, SMT
    <2>intersection. witness.support \cap support # {}
        BY <1>old, <1>before, <1>same, <2>witness, SMT DEF ReadyAncestryIntersections
    <2>identity. witness.owner = candidate
        <3>left. witness.owner \in Server /\ VoteSupport(voteHistory, witness.owner, certificate.term, witness.support)
            <4>certificate. CertificateWitness(voteHistory, witness)
                BY <1>base, SMT DEF CertificateFamily
            <4>shape. WitnessPrefixData(witness) BY <4>certificate, Zenon DEF CertificateWitness
            <4>election. RetainedElectionCertificate(voteHistory, witness.owner, certificate.term,
                                                    witness.snapshot, witness.occurrence, witness.support)
                BY <4>certificate, <2>witness, SMT DEF CertificateWitness
            <4>owner. witness.owner \in Server BY <4>shape, Zenon DEF WitnessPrefixData
            <4>support. VoteSupport(voteHistory, witness.owner, certificate.term, witness.support)
                BY <4>election, Zenon DEF RetainedElectionCertificate
            <4> QED BY <4>owner, <4>support, SMT
        <3>right. VoteSupport(voteHistory, candidate, certificate.term, support)
            BY <1>before, <1>same, SMT DEF ReadyElectionCertificate, RetainedElectionCertificate
        <3> QED BY <1>base, <1>data, <3>left, <3>right, <2>intersection, IntersectingVoteSupportsUnique, Zenon
    <2> QED BY <1>retained, <1>same, <2>witness, <2>identity, SMT
        DEF CertificateFamily, CertificateWitness, OwnerPrefix, ReadyElectionCertificate
<1>higher. CASE certificate.term < later
    <2>leader. CASE state[candidate] = Leader
        <3>campaign. PICK campaign \in campaigns:
                /\ campaign.candidate = candidate /\ campaign.term = later /\ campaign.snapshot = snapshot
            BY <1>before, <2>leader, SMT DEF CausalHistoryMetadata, CurrentCausalCampaigns, ReadyElectionCertificate
        <3>inside. IsPrefix(target, snapshot) BY <1>history, <1>higher, <3>campaign, SMT
        <3>held. IsPrefix(target, log[candidate])
            BY <1>base, <1>snapshot, <3>inside, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
        <3> QED BY <1>base, <1>extend, <3>held, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
    <2>candidate. CASE state[candidate] = Candidate
        <3>established. CASE SameTermEstablishedPrefix(commits, target, certificate.term)
            <4>longer. PICK longer \in commits: longer.term = certificate.term /\ IsPrefix(target, CommitTarget(longer))
                BY <3>established, SMT DEF SameTermEstablishedPrefix
            <4>types. CommitTarget(longer) \in Seq(LogEntry)
                BY <1>old, <4>longer, RetainedCommitReplicasHoldTarget, SMT
            <4>held. IsPrefix(CommitTarget(longer), log[candidate])
                BY <1>old, <1>before, <4>longer, SMT DEF ReadyCommitPrefixes
            <4>prefix. IsPrefix(target, log[candidate])
                BY <1>base, <4>types, <4>held, <4>longer, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
            <4> QED BY <1>base, <1>extend, <4>prefix, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
        <3>profile. CASE TermProtectedPrefix(ancestry, commits, certificate.term, target)
            <4> SUFFICES ASSUME ~IsPrefix(target, log'[candidate]) PROVE FALSE BY SMT
            <4>bound. LastTerm(snapshot) <= certificate.term
                <5> SUFFICES ASSUME LastTerm(snapshot) > certificate.term PROVE FALSE BY <1>data, LastTermTypeOK, SMT
                <5>last. Len(snapshot) > 0 BY <1>data, LenProperties, LastTermTypeOK, SMT DEF LastTerm
                <5>witness. PICK witness \in ancestry: witness.prefix = snapshot /\ witness.edge.term = LastTerm(snapshot)
                    BY <1>base, <1>snapshot, <5>last, CoveredSequenceHasLastWitness,
                       OrderedTermPrefixesAreEdgeConsistent, SMT
                <5>inside. IsPrefix(target, snapshot) BY <5>witness, SMT DEF LaterTermPrefixProtection
                <5>held. IsPrefix(target, log[candidate])
                    BY <1>base, <1>snapshot, <5>inside, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
                <5> QED BY <1>base, <1>extend, <5>held, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
            <4>profile. TermProtectedPrefix(ancestry, commits, certificate.term, snapshot)
                BY <1>higher, <1>opportunity, <1>data, <4>bound, HigherOpportunitySnapshotSuppliesTermProtectedPrefix, SMT
            <4>shape. EqualOrAdjacentConfigurations(ConfigOf(target), ConfigOf(snapshot))
                BY <1>old, <1>data, <3>profile, <4>profile, TermProtectedConfigurationsAreEqualOrAdjacent, SMT
            <4>quorums. support \in Quorums(ConfigOf(snapshot))
                        /\ ConfigOf(target) \subseteq Server /\ ConfigOf(snapshot) \subseteq Server
                BY <1>before, ConfigurationType, SMT DEF ReadyElectionCertificate, RetainedElectionCertificate,
                    LatestConfigurationOccurrence
            <4>intersection. certificate.replication \cap support # {}
                BY <1>data, <4>shape, <4>quorums, EqualOrAdjacentQuorumsIntersect, SMT
            <4>certificate. CausalElectionCertificate(voteHistory, ancestry, candidate, later, snapshot, occurrence, support)
                BY <1>before, <2>candidate, ReadyCandidateCapturesCausalCertificate, SMT
                DEF CausalHistoryMetadata, JointOpportunityWitnesses, OpportunityRelations
            <4>source_cut. RequestSourceElectionCut(ancestry, candidate, later, snapshot, support)
                BY <1>before, <2>candidate, ReadyCandidateCapturesRequestSourceCut, SMT
                DEF CausalHistoryMetadata, JointOpportunityWitnesses, OpportunityRelations
            <4>local_cut. LocalAppendElectionCut(voteHistory, later, snapshot, support)
                BY <1>before, <2>candidate, ReadyCandidateCapturesLocalAppendCut, SMT
                DEF CausalHistoryMetadata, JointOpportunityWitnesses, OpportunityRelations
            <4>ordered. TermsOrdered(snapshot)
                BY <1>base, <1>snapshot, TermsOrderedOnPrefix, LenProperties, SMT
                DEF MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered, TypeOK, LogVarsTypeOK, IsPrefix
            <4> DEFINE query == [candidate |-> candidate, term |-> later, snapshot |-> snapshot,
                                 occurrence |-> occurrence, support |-> support]
            <4>query. CausalCampaignRecords(voteHistory, ancestry, {query})
                BY <1>snapshot, <4>certificate, <4>source_cut, <4>local_cut, <4>ordered, SMT
                DEF query, CausalCampaignRecords, CausalCampaignData
            <4>evidence. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, target)
                         /\ MixedRecordedTargetCampaignIntersections(certificate.leader, certificate.term,
                                target, certificate.replication, {query})
                BY <1>old, <1>data, <4>query, AppendReceiveCertificateSuppliesMixedSupport, SMT
                DEF CausalHistoryMetadata
            <4>cuts. CampaignTargetVotingCuts(target, certificate.term, certificate.replication, {query})
                BY <1>old, <1>data, <4>query, <4>evidence, MixedSupportSuppliesTargetVotingCuts, SMT
            <4>fresh. SnapshotCoversPrefix(snapshot, target)
                <5>cut. SnapshotCoversPrefix(snapshot, target)
                        \/ \E peer \in Server: EarlierConflictingRequest(peer, certificate.term, later, target)
                    BY <1>higher, <4>intersection, <4>cuts, SMT DEF query, CampaignTargetVotingCuts
                <5>no_conflicts. ~\E peer \in Server: EarlierConflictingRequest(peer, certificate.term, later, target)
                    <6> SUFFICES ASSUME NEW peer \in Server,
                                      EarlierConflictingRequest(peer, certificate.term, later, target)
                                 PROVE FALSE BY SMT
                    <6>request. PICK request \in AppendRequests:
                            /\ certificate.term < request.mterm /\ request.mterm < later
                            /\ ~RequestRespectsPrefix(request, target)
                        BY SMT DEF EarlierConflictingRequest
                    <6>fields. request.mterm \in Nat
                        BY <1>base, <6>request, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
                    <6>bound. request.mterm >= certificate.term
                        BY <1>data, <6>request, <6>fields, SMT
                    <6>respect. RequestRespectsPrefix(request, target)
                        BY <6>request, <6>bound, SMT DEF ProtectedAppendRequests
                    <6> QED BY <6>request, <6>respect, SMT
                <5> QED BY <5>cut, <5>no_conflicts, SMT
            <4>inside. IsPrefix(target, snapshot)
                BY <1>base, <1>pure, <1>data, <1>snapshot, <4>fresh, DataFreshWordContainsProtectedTarget, SMT
            <4>held. IsPrefix(target, log[candidate])
                BY <1>base, <1>snapshot, <4>inside, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
            <4> QED BY <1>base, <1>extend, <4>held, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
        <3> QED BY <1>shape, <3>established, <3>profile, SMT
    <2> QED BY <1>before, <2>leader, <2>candidate, SMT DEF ReadyElectionCertificate
<1> QED BY <1>data, <1>same, <1>higher, SMT

LEMMA AppendReceiveAdmitsRawEvidenceProtection ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns), CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)',
           NEW received \in messages, received.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(received.mdest, received.msource, received)
    PROVE JointEvidenceProtection(nextVoteHistory, ancestry)' /\ ReadyEvidencePrefixes(nextVoteHistory)'
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ ElectionMessagesFrame /\ AppendRequests' = AppendRequests
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, AppendReceiveElectionFrame, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>coverage. \A server \in Server: CoveredPrefix(ancestry, log'[server])
    BY <1>old, AppendReceiveLogsCoveredByPreAncestry, SMT
<1> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)'
             PROVE /\ LaterTermPrefixProtection(ancestry, target, LastTerm(target))'
                   /\ ProtectedAppendRequests(target, LastTerm(target))'
                   /\ ProtectedLeaders(target, LastTerm(target))'
                   /\ ReadyTargetPrefix(nextVoteHistory, target, LastTerm(target))'
    BY SMT DEF JointEvidenceProtection, ReadyEvidencePrefixes, ReadyTargetPrefix
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(nextVoteHistory, certificate)' /\ certificate.entries = target
        /\ certificate.index = Len(target) /\ IsPrefix(target, log'[certificate.leader])
    BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
<1>data. CommitLogData(certificate)
    BY <1>certificate, SMT
    DEF RetainedCommitCertificate, CommitLogData, CommitPrefixData
<1>target. target \in Seq(LogEntry) /\ Len(target) > 0 /\ LastTerm(target) = certificate.term
            /\ certificate.term \in Nat /\ certificate.leader \in Server
    BY <1>certificate, <1>data, CommitLogDataProperties, WholeSequencePrefix, SMT
    DEF CommitTarget, RetainedCommitCertificate
<1>covered. CoveredPrefix(ancestry, target)
    BY <1>coverage, <1>base, <1>certificate, <1>target, CoveredPrefixRestriction, SMT DEF TypeOK, LogVarsTypeOK
<1>election. RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term, certificate.snapshot,
                    certificate.electionOccurrence, certificate.election)
    BY <1>base, <1>certificate, RetainedCertificateElectionMessagesFrame, SMT DEF RetainedCommitCertificate
<1>campaign. TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, target)
    BY <1>certificate, <1>election, SMT DEF TargetCampaignEvidence, RetainedCommitCertificate
<1>history. LaterTermPrefixProtection(ancestry, target, certificate.term)
            /\ ProtectedAppendRequests(target, certificate.term)
    BY <1>certificate, <1>target, <1>covered, AppendReceiveRawAgreementHasCampaignProtection, SMT
<1>boundary. LaterTermPrefixProtection(ancestry, target, LastTerm(target))'
    BY <1>history, <1>target, SMT DEF LaterTermPrefixProtection
<1>requests. ProtectedAppendRequests(target, LastTerm(target))'
    BY <1>history, <1>target, <1>base, SMT DEF ProtectedAppendRequests
<1>ready. ReadyTargetPrefix(nextVoteHistory, target, LastTerm(target))'
    BY <1>certificate, <1>target, <1>covered, <1>campaign, <1>history,
       AppendReceiveRawAgreementProtectsReadyPrefixes, SMT
<1>leaders. ProtectedLeaders(target, LastTerm(target))'
    <2> SUFFICES ASSUME NEW leader \in Server, state'[leader] = Leader, currentTerm'[leader] >= LastTerm(target)
                 PROVE IsPrefix(target, log'[leader]) BY SMT DEF ProtectedLeaders
    <2>campaign. PICK campaign \in campaigns:
            /\ campaign.candidate = leader /\ campaign.term = currentTerm'[leader]
            /\ campaign.snapshot = CampaignPrefix(log'[leader], currentTerm'[leader])
        BY SMT DEF CausalHistoryMetadata, CurrentCausalCampaigns
    <2>data. CausalCampaignData(nextVoteHistory, ancestry, campaign)'
        BY <2>campaign, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
    <2>ready. ReadyElectionCertificate(nextVoteHistory, leader, campaign.term, campaign.snapshot, campaign.occurrence, campaign.support)'
        BY <2>campaign, <2>data, SMT
        DEF ReadyElectionCertificate, CausalCampaignData, CausalElectionCertificate
    <2> QED BY <1>ready, <2>campaign, <2>data, <2>ready, SMT DEF ReadyTargetPrefix, CausalCampaignData
<1> QED BY <1>boundary, <1>requests, <1>leaders, <1>ready, SMT

=======================================================================
