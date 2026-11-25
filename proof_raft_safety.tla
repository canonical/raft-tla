------------------------- MODULE proof_raft_safety ----------------------------
\* proof_raft_safety.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_joint_core,
        proof_exclusion,
        proof_evidence_admission

AppendCommitIndexBound ==
    \A request \in AppendRequests:
        request.mcommitIndex <= request.mprevLogIndex + Len(request.mentries)

LocalCommitPrefixEvidence(commits) ==
    \A server \in Server:
        /\ commitIndex[server] <= Len(log[server])
        /\ commitIndex[server] > 0 => \E certificate \in commits:
               /\ certificate.term <= currentTerm[server]
               /\ IsPrefix(Committed(server), CommitTarget(certificate))

\* Campaign activity and pending-prefix protection are consequences of the
\* selected creator, barrier, and causal-history witnesses in each state.
MembershipJointInv(voteHistory) ==
    /\ MembershipJointCore(voteHistory)
    /\ AcknowledgmentPrefixHistory /\ AcknowledgmentVoteCutHistory(voteHistory)
    /\ \E ancestry, commits, campaigns:
           /\ JointMembershipWitnesses(voteHistory, ancestry, commits)
           /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)

EarlierBarrierProfile(ancestry, commits, term, entries) ==
    /\ entries \in Seq(LogEntry) /\ CoveredPrefix(ancestry, entries) /\ TermsOrdered(entries)
    /\ \A index \in DOMAIN entries: entries[index].term < term
    /\ \A certificate \in commits: certificate.term < term => IsPrefix(CommitTarget(certificate), entries)

BarrierProtectedWord(ancestry, commits, entries) ==
    /\ entries \in Seq(LogEntry) /\ TermsOrdered(entries) /\ CoveredPrefix(ancestry, entries)
    /\ \A certificate \in commits: IsPrefix(CommitTarget(certificate), entries)

RaftSafety ==
    /\ TypeOK
    /\ SendInvariant
    /\ MoreThanOneLeaderInv
    /\ ElectionSafetyInv
    /\ LogMatchingInv
    /\ LogInv
    /\ QuorumLogInv
    /\ LeaderCompletenessInv

\* One choice of histories supports both membership and local commits.
RaftEvidence(votes, ancestry, commits, campaigns) ==
    /\ MembershipJointInv(votes)
    /\ JointMembershipWitnesses(votes, ancestry, commits)
    /\ CausalHistoryMetadata(votes, ancestry, commits, campaigns)
    /\ AppendCommitIndexBound
    /\ LocalCommitPrefixEvidence(commits)

RaftInductiveInv ==
    /\ \E votes, ancestry, commits, campaigns: RaftEvidence(votes, ancestry, commits, campaigns)
    /\ RaftSafety

RaftEvidenceSafetyRule ==
    \A votes, ancestry, commits, campaigns: RaftEvidence(votes, ancestry, commits, campaigns) => RaftSafety

LEMMA MembershipJointInit ==
    Init => MembershipJointInv({})
<1> SUFFICES ASSUME Init PROVE MembershipJointInv({}) BY SMT
<1>base. ReplicationPrefixInv({}) /\ CandidateAppendFree /\ SameTermAcknowledgmentPrefixes
    BY ReplicationPrefixInvInit, CandidateAppendFreeInit, SameTermAcknowledgmentPrefixesInit, SMT
<1>targets. EvidenceAgreementTargets({}) = {}
    BY EmptySeq, LenProperties, SubSeqEmpty, SMT
    DEF Init, InitLogVars, EvidenceAgreementTargets, LogPrefixSet,
        SupportedAgreementTarget, RetainedCommitCertificate
<1>empty. JointMembershipWitnesses({}, {}, {})
    BY <1>targets, CampaignHistoryInit, FS_EmptySet, SMT
    DEF JointMembershipWitnesses, CertificateFamily, TermPrefixOrder, CoversEntryEdges,
        HistoricalEntryEdges, AppendRequests, RequestPrefixAncestry,
        LiveAncestryCertificateIntersections, CommitCertificateFamily,
        LocalCommitEvidence, AdvertisedCommitEvidence, CommitLeaderProtection,
        CommitElectionIntersections, JointCommitProtection, JointEvidenceProtection,
        ConfigurationBarrierAncestry, Init, InitLogVars
<1>intersections. LiveLeaderCertificateIntersections({}) /\ CurrentRequestCertificateIntersections({})
    BY ServerStatesDistinct, SMT
    DEF LiveLeaderCertificateIntersections, CurrentRequestCertificateIntersections,
        CurrentElectionCertificate, AppendRequests, Init, InitServerVars
<1> QED BY <1>base, <1>empty, <1>intersections, CausalHistoryMetadataInit, AcknowledgmentPrefixHistoryInit,
    AcknowledgmentVoteCutHistoryInit, SMT
    DEF MembershipJointCore, MembershipJointInv

LEMMA SelectedCertificateTargetIsPresent ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW certificate \in commits
    PROVE /\ RetainedCommitCertificate(voteHistory, certificate) /\ CommitTarget(certificate) \in Seq(LogEntry)
          /\ Len(CommitTarget(certificate)) > 0 /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ certificate.leader \in Server /\ IsPrefix(CommitTarget(certificate), log[certificate.leader])
    BY RetainedCommitReplicasHoldTarget, SMT
    DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate,
        JointCommitProtection, RecordedAcknowledgersProtected, RecordedReplicationSupport, ProtectedVoters

LEMMA RetainedCertificateHasTargetRequestEvidence ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory),
           NEW certificate, RetainedCommitCertificate(voteHistory, certificate)
    PROVE TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
<1>wire. CASE certificate.replication \ {certificate.leader} # {}
    <2>peer. PICK peer \in certificate.replication \ {certificate.leader}: TRUE
        BY <1>wire, SMT
    <2>origin. PICK response, request:
            /\ response \in messages /\ request \in messages
            /\ SuccessfulAppendResponse(response) /\ ResponseMatchesRequest(response, request)
            /\ response.msource = peer /\ response.mdest = certificate.leader /\ response.mterm = certificate.term
            /\ response.mmatchIndex >= Len(CommitTarget(certificate))
        BY <2>peer, SMT DEF RetainedCommitCertificate, RecordedPrefixAcknowledgment
    <2>request. request \in AppendRequests /\ request.msource = certificate.leader /\ request.mterm = certificate.term
        BY <2>origin, SMT DEF AppendRequests, ResponseMatchesRequest
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
            /\ RequestCampaignBoundary(voteHistory, request, prefix)
        BY <2>request, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
    <2>length. Len(CommitTarget(certificate)) <= Len(prefix)
        BY <2>prefix, <2>origin, SMT DEF RequestPrefixData, ResponseMatchesRequest
    <2> QED BY <2>request, <2>prefix, <2>length, SMT DEF TargetRequestEvidence, TargetWireEvidence
    
<1>local. CASE certificate.replication \ {certificate.leader} = {}
    BY <1>local, RecordedLocalOriginSuppliesTargetEvidence, SMT
    DEF RetainedCommitCertificate, JointMembershipWitnesses, TargetRequestEvidence
<1> QED BY <1>wire, <1>local, SMT

LEMMA RetainedCertificateVoterHasTargetCut ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry), RequestSourceVoteCutHistory(voteHistory, ancestry),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory),
           LocalAppendVoteCutHistory(voteHistory),
           NEW certificate, RetainedCommitCertificate(voteHistory, certificate), CoveredPrefix(ancestry, certificate.entries),
           NEW peer \in certificate.replication
    PROVE \E prefix \in Seq(LogEntry):
              /\ IsPrefix(CommitTarget(certificate), prefix)
              /\ AcknowledgmentVoteCuts(voteHistory, prefix, peer, certificate.term)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>target. certificate.leader \in Server /\ certificate.term \in Nat
          /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ CoveredPrefix(ancestry, CommitTarget(certificate))
          /\ TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
    BY CommitCertificateTargetProperties, CommitCertificateSuppliesTargetCampaignEvidence,
       CoveredPrefixRestriction, LenProperties, SMT DEF RetainedCommitCertificate, LastTerm
<1>self. CASE peer = certificate.leader
    <2>evidence. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        BY RetainedCertificateHasTargetRequestEvidence, SMT
    <2>wire. CASE TargetWireEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        <3>original. PICK original, originalPrefix:
                /\ original \in AppendRequests /\ originalPrefix \in Seq(LogEntry)
                /\ original.msource = certificate.leader /\ original.mterm = certificate.term
                /\ RequestPrefixData(original, originalPrefix) /\ Len(CommitTarget(certificate)) <= Len(originalPrefix)
            BY <2>wire, SMT DEF TargetWireEvidence
        <3>frozen. PICK prefix \in Seq(LogEntry):
                /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
                /\ AcknowledgmentVoteCuts(voteHistory, prefix, certificate.leader, certificate.term)
            BY <3>original, SMT DEF RequestSourceVoteCutHistory
        <3>boundary. RequestCampaignBoundary(voteHistory, original, prefix)
            BY <1>base, <3>original, <3>frozen, CoveredRequestHasCampaignBoundary, SMT
        <3>length. Len(CommitTarget(certificate)) <= Len(prefix)
            BY <3>original, <3>frozen, SMT DEF RequestPrefixData
        <3>inside. IsPrefix(CommitTarget(certificate), prefix)
            BY <1>base, <1>target, <3>original, <3>frozen, <3>boundary, <3>length, FrozenRequestPrefixContainsTarget, SMT
        <3> QED BY <1>self, <3>frozen, <3>inside, SMT
    <2>local. CASE TargetLocalEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        BY <2>local, <1>self, SMT DEF TargetLocalEvidence, LocalAppendVoteCutHistory
    <2> QED BY <2>evidence, <2>wire, <2>local, SMT DEF TargetRequestEvidence
<1>other. CASE peer # certificate.leader
    <2>response. PICK response \in messages:
            /\ SuccessfulAppendResponse(response) /\ response.msource = peer
            /\ response.mdest = certificate.leader /\ response.mterm = certificate.term
            /\ response.mmatchIndex >= Len(CommitTarget(certificate))
        BY <1>other, SMT DEF RetainedCommitCertificate, RecordedPrefixAcknowledgment
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ AcknowledgmentVoteCuts(voteHistory, prefix, peer, certificate.term)
        BY <2>response, SMT DEF FrozenAcknowledgmentVoteCutHistory
    <2>boundary. RequestCampaignBoundary(voteHistory, request, prefix)
        BY <1>base, <2>frozen, CoveredRequestHasCampaignBoundary, SMT
    <2>inside. IsPrefix(CommitTarget(certificate), prefix)
        BY <1>base, <1>target, <2>response, <2>frozen, <2>boundary, FrozenRequestPrefixContainsTarget, SMT
        DEF ResponseMatchesRequest
    <2> QED BY <2>frozen, <2>inside, SMT
<1> QED BY <1>self, <1>other, SMT

LEMMA RecordedOpportunityVoteUsesSnapshot ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW peer \in Server, NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support), RecordedCampaignVote(voteHistory, peer, candidate, term)
    PROVE /\ RecordedCampaignRequests(candidate, term) = CampaignRequests(candidate, term, snapshot)
          /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
<1>base. TypeOK /\ SendInvariant /\ PositiveVoteResponseRequestInv /\ CampaignHistory(voteHistory)
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv
<1>epoch. term <= currentTerm[candidate]
    BY <1>base, RecordedCampaignVoteCandidateTermBound, SMT
<1> QED BY <1>base, <1>epoch, SMT DEF OpportunityCertificate, CampaignOpportunity, TypeOK, ServerVarsTypeOK, CampaignHistory, HistoryCampaignSnapshot

LEMMA RecordedReplicationVoterHasFreshSnapshot ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry), RequestSourceVoteCutHistory(voteHistory, ancestry),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory),
           LocalAppendVoteCutHistory(voteHistory),
           NEW certificate, RetainedCommitCertificate(voteHistory, certificate), CoveredPrefix(ancestry, certificate.entries),
           ProtectedAppendRequests(CommitTarget(certificate), certificate.term), NEW peer \in certificate.replication,
           NEW candidate \in Server, NEW term \in Nat, certificate.term < term,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support), RecordedCampaignVote(voteHistory, peer, candidate, term)
    PROVE SnapshotCoversPrefix(snapshot, CommitTarget(certificate))
<1>base. TypeOK /\ peer \in Server /\ certificate.term \in Nat
    BY JointCoreBase, SMT DEF RetainedCommitCertificate, Quorums
<1>target. CommitTarget(certificate) \in Seq(LogEntry)
    BY CommitCertificateTargetProperties, SMT
<1>cut. PICK prefix \in Seq(LogEntry):
        /\ IsPrefix(CommitTarget(certificate), prefix)
        /\ AcknowledgmentVoteCuts(voteHistory, prefix, peer, certificate.term)
    BY RetainedCertificateVoterHasTargetCut, SMT
<1>no_conflict. ~ConflictingRequestBeforeVote(peer, certificate.term, term, CommitTarget(certificate))
    <2> SUFFICES ASSUME NEW request \in AppendRequests, request.mdest = peer,
                          certificate.term < request.mterm, request.mterm <= term,
                          ~RequestRespectsPrefix(request, CommitTarget(certificate))
                 PROVE FALSE BY SMT DEF ConflictingRequestBeforeVote
    <2>fields. request.mterm \in Nat
        BY <1>base, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
    <2>bound. request.mterm >= certificate.term BY <1>base, <2>fields, SMT
    <2>respect. RequestRespectsPrefix(request, CommitTarget(certificate))
        BY <2>bound, SMT DEF ProtectedAppendRequests
    <2> QED BY <2>respect, SMT
<1>request. PICK request \in RecordedVoteRequests(voteHistory, candidate, term):
        VoteRequestCoversPrefix(request, CommitTarget(certificate))
    BY <1>target, <1>cut, <1>no_conflict, SMT DEF AcknowledgmentVoteCuts
<1>snapshot. RecordedCampaignRequests(candidate, term) = CampaignRequests(candidate, term, snapshot)
          /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
    BY <1>base, RecordedOpportunityVoteUsesSnapshot, SMT
<1> QED BY <1>base, <1>request, <1>snapshot, RecordedVoteRequestsUseSnapshot, SMT
    DEF VoteRequestCoversPrefix, SnapshotCoversPrefix, JointMembershipWitnesses, CertificateFamily

LEMMA SelectedCommitTargetsAreComparable ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW left \in commits, NEW right \in commits
    PROVE IsPrefix(CommitTarget(left), CommitTarget(right)) \/ IsPrefix(CommitTarget(right), CommitTarget(left))
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>data. CommitTarget(left) \in Seq(LogEntry) /\ Len(CommitTarget(left)) > 0
          /\ CommitTarget(right) \in Seq(LogEntry) /\ Len(CommitTarget(right)) > 0
          /\ LastTerm(CommitTarget(left)) = left.term /\ LastTerm(CommitTarget(right)) = right.term
          /\ CoveredPrefix(ancestry, CommitTarget(left)) /\ CoveredPrefix(ancestry, CommitTarget(right))
    BY <1>base, SelectedCertificateTargetIsPresent, CurrentLogPrefixCovered, SMT
    DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK
<1>boundaries. LaterTermPrefixProtection(ancestry, CommitTarget(left), LastTerm(CommitTarget(left)))
          /\ LaterTermPrefixProtection(ancestry, CommitTarget(right), LastTerm(CommitTarget(right)))
    BY <1>data, SMT DEF JointMembershipWitnesses, JointCommitProtection
<1> QED BY <1>base, <1>data, <1>boundaries, ExistingBoundaryComparesNewerPrefix, LastTermTypeOK, SMT

LEMMA SelectedCommitFamilyHasCoveringTarget ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits), commits # {}
    PROVE \E latest \in commits: \A certificate \in commits: IsPrefix(CommitTarget(certificate), CommitTarget(latest))
<1> DEFINE indexes == {certificate.index: certificate \in commits}
<1>finite_commits. IsFiniteSet(commits) BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>finite. IsFiniteSet(indexes) BY <1>finite_commits, FS_Image, Isa DEF indexes
<1>indexes. indexes \subseteq Nat /\ indexes # {}
    BY LenProperties, SMT DEF indexes, JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
<1>maximum. PICK maximum \in indexes: \A index \in indexes: index <= maximum
    BY <1>finite, <1>indexes, FiniteNaturalSetHasMaximum, SMT
<1>latest. PICK latest \in commits: latest.index = maximum BY <1>maximum, SMT DEF indexes
<1>targets. \A certificate \in commits: IsPrefix(CommitTarget(certificate), CommitTarget(latest))
    <2> SUFFICES ASSUME NEW certificate \in commits
                 PROVE IsPrefix(CommitTarget(certificate), CommitTarget(latest)) BY SMT
    <2>data. CommitTarget(certificate) \in Seq(LogEntry) /\ CommitTarget(latest) \in Seq(LogEntry)
              /\ Len(CommitTarget(certificate)) = certificate.index /\ Len(CommitTarget(latest)) = latest.index
        BY <1>latest, CommitCertificateTargetProperties, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
    <2>length. Len(CommitTarget(certificate)) <= Len(CommitTarget(latest))
        BY <1>maximum, <1>latest, <2>data, SMT DEF indexes
    <2>comparable. IsPrefix(CommitTarget(certificate), CommitTarget(latest)) \/ IsPrefix(CommitTarget(latest), CommitTarget(certificate))
        BY <1>latest, SelectedCommitTargetsAreComparable, SMT
    <2> QED BY <2>data, <2>length, <2>comparable, ComparablePrefixesWithOrderedLengths, SMT
<1> QED BY <1>latest, <1>targets, SMT

LEMMA MissingCertificateBlockerProtectsHeldPrefix ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           NEW target \in Seq(LogEntry), IsPrefix(target, entries),
           NEW original \in commits, IsPrefix(target, CommitTarget(original)),
           \E certificate \in commits: ~IsPrefix(CommitTarget(certificate), entries)
    PROVE \E blocker \in commits:
              /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
              /\ IsPrefix(target, CommitTarget(blocker))
<1>data. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>missing. PICK certificate \in commits: ~IsPrefix(CommitTarget(certificate), entries) BY SMT
<1>blocker. PICK blocker \in commits:
        /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
        /\ ~SnapshotCoversPrefix(entries, CommitTarget(blocker))
    BY <1>data, <1>missing, MissingProtectedTargetHasBlockingCertificate, SMT DEF BarrierExclusionData
<1>target. CommitTarget(original) \in Seq(LogEntry) /\ CommitTarget(blocker) \in Seq(LogEntry)
          /\ (IsPrefix(CommitTarget(original), CommitTarget(blocker)) \/ IsPrefix(CommitTarget(blocker), CommitTarget(original)))
    BY <1>blocker, SelectedCommitTargetsAreComparable, CommitCertificateTargetProperties, SMT
    DEF JointMembershipWitnesses, CommitCertificateFamily
<1>comparable. IsPrefix(target, CommitTarget(blocker)) \/ IsPrefix(CommitTarget(blocker), target)
    BY <1>target, <1>blocker, PrefixesWithBoundedLength, SequencePrefixTransitive,
       WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
<1>missing_prefix. ~IsPrefix(CommitTarget(blocker), entries)
    BY <1>blocker, SnapshotFreshnessCoversHeldPrefix, CommitCertificateTargetProperties,
       LastTermTypeOK, LenProperties, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>inside. IsPrefix(target, CommitTarget(blocker))
    BY <1>target, <1>comparable, <1>missing_prefix, SequencePrefixTransitive, SMT
<1> QED BY <1>blocker, <1>inside, SMT

LEMMA CompleteCertificateWordBlocksHeldConfiguration ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           NEW target \in Seq(LogEntry), NEW original \in commits, IsPrefix(target, CommitTarget(original)),
           \A certificate \in commits: IsPrefix(CommitTarget(certificate), entries)
    PROVE \E blocker \in commits:
              /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
              /\ IsPrefix(target, CommitTarget(blocker))
<1>latest. PICK latest \in commits:
        \A certificate \in commits: IsPrefix(CommitTarget(certificate), CommitTarget(latest))
    BY SelectedCommitFamilyHasCoveringTarget, SMT
<1>barriers. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>certificates. RetainedCommitCertificate(voteHistory, latest) /\ RetainedCommitCertificate(voteHistory, original)
    BY <1>latest, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>data. BarrierExclusionData(ancestry, commits) /\ RetainedCommitCertificate(voteHistory, latest)
          /\ latest.entries \in Seq(LogEntry) /\ CommitTarget(latest) \in Seq(LogEntry)
          /\ IsPrefix(CommitTarget(latest), latest.entries) /\ CommitTarget(original) \in Seq(LogEntry)
          /\ TermsOrdered(latest.entries) /\ CoveredPrefix(ancestry, latest.entries)
    BY <1>latest, <1>barriers, <1>certificates, CommitCertificateTargetProperties, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses, CommitPrefixCoverage, RetainedCommitCertificate
<1>parents. \A certificate \in FamilyBarriers(PairAncestry(ancestry, entries, latest.entries), commits):
        IsPrefix(CommitTarget(certificate), entries) /\ IsPrefix(CommitTarget(certificate), latest.entries)
    BY <1>latest, <1>data, CommitPrefixDataTargetProperties, SequencePrefixTransitive, SMT
    DEF FamilyBarriers, BarrierExclusionData, CommitLogData, CommitPrefixData
<1>shape. EqualOrAdjacentConfigurations(ConfigOf(entries), ConfigOf(latest.entries))
    BY <1>data, <1>parents, PairedParentsSupplyEqualOrAdjacentConfigurations, SMT DEF BarrierExclusionData, CommitLogData
<1>blocks. CertificateBlocksConfiguration(latest, ConfigOf(entries))
    BY <1>data, <1>shape, ConfigurationType, EqualOrAdjacentQuorumsIntersect, SMT
    DEF CertificateBlocksConfiguration, RetainedCommitCertificate, LatestConfigurationOccurrence
<1>inside. IsPrefix(target, CommitTarget(latest))
    BY <1>data, <1>latest, SequencePrefixTransitive, SMT
<1> QED BY <1>latest, <1>blocks, <1>inside, SMT

LEMMA HeldCertifiedPrefixHasBlockingCertificate ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           NEW target \in Seq(LogEntry), IsPrefix(target, entries),
           NEW original \in commits, IsPrefix(target, CommitTarget(original))
    PROVE \E blocker \in commits:
              /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
              /\ IsPrefix(target, CommitTarget(blocker))
<1>missing. CASE \E certificate \in commits: ~IsPrefix(CommitTarget(certificate), entries)
    BY <1>missing, MissingCertificateBlockerProtectsHeldPrefix, SMT
<1>complete. CASE \A certificate \in commits: IsPrefix(CommitTarget(certificate), entries)
    BY <1>complete, CompleteCertificateWordBlocksHeldConfiguration, SMT
<1> QED BY <1>missing, <1>complete, SMT

LEMMA NewAppendMessageBoundsCommitIndex ==
    ASSUME TypeOK, NextIndexBound, NEW leader \in Server, NEW peer \in Server, state[leader] = Leader
    PROVE AppendEntriesMessage(leader, peer).mcommitIndex <=
              AppendEntriesMessage(leader, peer).mprevLogIndex + Len(AppendEntriesMessage(leader, peer).mentries)
<1>types. log[leader] \in Seq(LogEntry) /\ Len(log[leader]) \in Nat
          /\ nextIndex[leader][peer] \in 1..(Len(log[leader]) + 1) /\ nextIndex[leader][peer] \in Nat /\ commitIndex[leader] \in Nat
    BY LenProperties, SMT DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK, NextIndexBound
<1>endpoint. AppendEntriesLastEntry(leader, peer) =
        nextIndex[leader][peer] - 1 + Len(AppendEntriesEntries(leader, peer))
    <2>entry. CASE nextIndex[leader][peer] <= Len(log[leader])
        <3>last. AppendEntriesLastEntry(leader, peer) = nextIndex[leader][peer]
            BY <1>types, <2>entry, MinOrderedPair, SMT DEF AppendEntriesLastEntry
        <3>length. Len(AppendEntriesEntries(leader, peer)) = 1
            BY <1>types, <2>entry, <3>last, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF AppendEntriesEntries
        <3> QED BY <1>types, <3>last, <3>length, SMT
    <2>heartbeat. CASE nextIndex[leader][peer] = Len(log[leader]) + 1
        <3>pair. {Len(log[leader]), nextIndex[leader][peer]} = {nextIndex[leader][peer], Len(log[leader])} BY SMT
        <3>last. AppendEntriesLastEntry(leader, peer) = Len(log[leader])
            BY <1>types, <2>heartbeat, <3>pair, MinOrderedPair, SMT DEF AppendEntriesLastEntry
        <3>length. Len(AppendEntriesEntries(leader, peer)) = 0
            BY <1>types, <2>heartbeat, <3>last, SubSeqEmpty, EmptySeq, LenProperties, SMT DEF AppendEntriesEntries
        <3> QED BY <1>types, <2>heartbeat, <3>last, <3>length, SMT
    <2> QED BY <1>types, <2>entry, <2>heartbeat, SMT
<1> QED BY <1>types, <1>endpoint, AppendEntriesLastEntryTypeOK, MinTypeOK, SMT DEF AppendEntriesMessage

LEMMA AppendCommitIndexBoundInit == Init => AppendCommitIndexBound
    BY SMT DEF Init, AppendCommitIndexBound, AppendRequests

LEMMA AppendCommitIndexBoundNext ==
    ASSUME NEW voteHistory, MembershipJointInv(voteHistory), AppendCommitIndexBound, [Next]_vars
    PROVE AppendCommitIndexBound'
<1>base. TypeOK /\ EntryEdgeBase /\ NextIndexBound
    BY JointCoreBase, SMT DEF MembershipJointInv, EntryEdgeBase
<1> SUFFICES ASSUME NEW request \in AppendRequests'
             PROVE request.mcommitIndex <= request.mprevLogIndex + Len(request.mentries)
    BY SMT DEF AppendCommitIndexBound
<1>old. CASE request \in messages
    BY <1>old, SMT DEF AppendCommitIndexBound, AppendRequests
<1>new. CASE request \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer) /\ request = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2> QED BY <1>base, <2>origin, NewAppendMessageBoundsCommitIndex, SMT DEF AppendEntries
<1> QED BY <1>old, <1>new, SMT

LEMMA RequestPrefixAndEarlierCertificateAreComparable ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW request \in AppendRequests, NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix),
           CoveredPrefix(ancestry, prefix), NEW certificate \in commits, certificate.term <= request.mterm
    PROVE IsPrefix(prefix, CommitTarget(certificate)) \/ IsPrefix(CommitTarget(certificate), prefix)
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>fields. request.mentries \in Seq(LogEntry) /\ request.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF AppendRequests, TypeOK, MsgTypeOK
<1>target. RetainedCommitCertificate(voteHistory, certificate) /\ certificate.leader \in Server /\ certificate.term \in Nat
          /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ CoveredPrefix(ancestry, CommitTarget(certificate))
          /\ TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>base, SelectedCertificateTargetIsPresent, CurrentLogPrefixCovered,
       CommitCertificateSuppliesTargetCampaignEvidence, SMT
    DEF JointMembershipWitnesses, RetainedCommitCertificate, TypeOK, LogVarsTypeOK
<1>same. CASE certificate.term = request.mterm
    <2>evidence. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        BY <1>target, RetainedCertificateHasTargetRequestEvidence, SMT DEF CausalHistoryMetadata
    <2>wire. CASE TargetWireEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        <3>original. PICK original, frozen:
                /\ original \in AppendRequests /\ frozen \in Seq(LogEntry)
                /\ original.msource = certificate.leader /\ original.mterm = certificate.term
                /\ RequestPrefixData(original, frozen) /\ CoveredPrefix(ancestry, frozen)
                /\ RequestCampaignBoundary(voteHistory, original, frozen) /\ Len(CommitTarget(certificate)) <= Len(frozen)
            BY <2>wire, SMT DEF TargetWireEvidence
        <3>inside. IsPrefix(CommitTarget(certificate), frozen)
            BY <1>base, <1>target, <3>original, FrozenRequestPrefixContainsTarget, SMT
        <3>ordered. IsPrefix(prefix, frozen) \/ IsPrefix(frozen, prefix)
            BY <1>same, <3>original, SMT DEF CausalHistoryMetadata, FrozenRequestPrefixesAgree
        <3> QED BY <1>target, <3>original, <3>inside, <3>ordered,
            PrefixesWithBoundedLength, SequencePrefixTransitive, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
    <2>local. CASE TargetLocalEvidence(voteHistory, ancestry, certificate.leader, certificate.term, CommitTarget(certificate))
        <3>boundary. RequestCampaignBoundary(voteHistory, request, prefix)
            BY <1>base, CoveredRequestHasCampaignBoundary, SMT
        <3>word. PICK word \in Seq(LogEntry):
            IsPrefix(CommitTarget(certificate), word) /\ (IsPrefix(prefix, word) \/ IsPrefix(word, prefix))
            BY <1>base, <1>target, <1>same, <2>local, <3>boundary, TargetLocalAndRequestPrefixesAreComparable, SMT
        <3> QED BY <1>target, <3>word, PrefixesWithBoundedLength, SequencePrefixTransitive,
            WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
    <2> QED BY <2>evidence, <2>wire, <2>local, SMT DEF TargetRequestEvidence
<1>higher. CASE certificate.term < request.mterm
    <2>campaign. PICK campaign, frozen:
            /\ campaign \in campaigns /\ frozen \in Seq(LogEntry)
            /\ campaign.term = request.mterm /\ RequestPrefixData(request, frozen) /\ CoveredPrefix(ancestry, frozen)
            /\ (IsPrefix(campaign.snapshot, frozen) \/ IsPrefix(frozen, campaign.snapshot))
        BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, RequestCampaignCoverage
    <2>equal. prefix = frozen
        BY <1>base, <1>fields, <2>campaign, CoveredRequestPrefixIsUnique, SMT
    <2>inside. campaign.snapshot \in Seq(LogEntry) /\ IsPrefix(CommitTarget(certificate), campaign.snapshot)
        BY <1>higher, <2>campaign, SMT
        DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignData, CampaignCommitPrefixes
    <2> QED BY <1>target, <2>campaign, <2>equal, <2>inside,
        PrefixesWithBoundedLength, SequencePrefixTransitive, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
<1> QED BY <1>fields, <1>target, <1>same, <1>higher, SMT

LEMMA CutOfComparablePrefixesIsInsideCertificate ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW target \in Seq(LogEntry), NEW cut \in Nat,
           IsPrefix(prefix, target) \/ IsPrefix(target, prefix), cut <= Len(prefix), cut <= Len(target)
    PROVE /\ SubSeq(prefix, 1, cut) \in Seq(LogEntry) /\ Len(SubSeq(prefix, 1, cut)) = cut
          /\ IsPrefix(SubSeq(prefix, 1, cut), target)
<1>segment. SubSeq(prefix, 1, cut) \in Seq(LogEntry) /\ Len(SubSeq(prefix, 1, cut)) = cut
          /\ IsPrefix(SubSeq(prefix, 1, cut), prefix)
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1> QED BY <1>segment, PrefixesWithBoundedLength, SequencePrefixTransitive, SMT

LEMMA AdvertisedCommitPrefixHasCertificate ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), AppendCommitIndexBound, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW request \in AppendRequests, request.mcommitIndex > 0,
           NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix)
    PROVE \E certificate \in commits:
              /\ certificate.term <= request.mterm
              /\ IsPrefix(SubSeq(prefix, 1, request.mcommitIndex), CommitTarget(certificate))
<1>base. TypeOK BY JointCoreBase, SMT
<1>certificate. PICK certificate \in commits:
        request.mcommitIndex <= certificate.index /\ certificate.term <= request.mterm
    BY SMT DEF JointMembershipWitnesses, AdvertisedCommitEvidence
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) = certificate.index
    BY <1>certificate, CommitCertificateTargetProperties, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>bounds. request.mcommitIndex \in Nat /\ request.mcommitIndex <= Len(prefix)
    BY <1>base, MessageFieldsTypeOK, SMT DEF AppendCommitIndexBound, RequestPrefixData, AppendRequests, TypeOK, MsgTypeOK
<1>comparable. IsPrefix(prefix, CommitTarget(certificate)) \/ IsPrefix(CommitTarget(certificate), prefix)
    BY <1>certificate, RequestPrefixAndEarlierCertificateAreComparable, SMT
<1>inside. IsPrefix(SubSeq(prefix, 1, request.mcommitIndex), CommitTarget(certificate))
    BY <1>certificate, <1>target, <1>bounds, <1>comparable, CutOfComparablePrefixesIsInsideCertificate, SMT
<1> QED BY <1>certificate, <1>inside, SMT

LEMMA PhysicalPrefixDeterminesShorterCut ==
    ASSUME NEW prefix \in Seq(LogEntry), NEW entries \in Seq(LogEntry), IsPrefix(prefix, entries),
           NEW cut \in Nat, cut <= Len(prefix)
    PROVE cut <= Len(entries) /\ SubSeq(entries, 1, cut) = SubSeq(prefix, 1, cut)
    BY PrefixContainsInitialSegment, LenProperties, SMT DEF IsPrefix

LEMMA ExistingLocalCommitPrefixSurvives ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           LocalCommitPrefixEvidence(commits), NEW server \in Server, commitIndex[server] > 0
    PROVE \E certificate \in commits:
              /\ certificate.term <= currentTerm'[server]
              /\ IsPrefix(Committed(server), CommitTarget(certificate))
              /\ IsPrefix(Committed(server), log'[server])
<1>base. TypeOK /\ ReplicationPrefixInv(voteHistory)
    BY JointCoreBase, SMT DEF MembershipJointCore
<1>certificate. PICK certificate \in commits:
        certificate.term <= currentTerm[server] /\ IsPrefix(Committed(server), CommitTarget(certificate))
    BY SMT DEF LocalCommitPrefixEvidence
<1>target. PICK target \in Seq(LogEntry): target = Committed(server)
    BY <1>base, SubSeqTypeOK, SMT DEF Committed, LocalCommitPrefixEvidence, TypeOK, LogVarsTypeOK
<1>data. RetainedCommitCertificate(voteHistory, certificate) /\ CommitTarget(certificate) \in Seq(LogEntry)
          /\ certificate.term \in Nat /\ IsPrefix(target, log[server])
    <2>certificate. RetainedCommitCertificate(voteHistory, certificate)
        BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily
    <2>fields. CommitTarget(certificate) \in Seq(LogEntry) /\ certificate.term \in Nat
        BY <2>certificate, CommitCertificateTargetProperties, SMT DEF RetainedCommitCertificate
    <2>log. log[server] \in Seq(LogEntry) /\ commitIndex[server] \in Nat
            /\ commitIndex[server] <= Len(log[server])
        BY <1>base, SMT DEF TypeOK, LogVarsTypeOK, LocalCommitPrefixEvidence
    <2>prefix. IsPrefix(target, log[server])
        BY <1>target, <2>log, SubSeqProperties, LenProperties, SMT DEF Committed, IsPrefix
    <2> QED BY <2>certificate, <2>fields, <2>prefix, SMT
<1>protection. ProtectedAppendRequests(target, certificate.term)
    BY <1>certificate, <1>target, <1>data, ProtectedAppendRequestsOnPrefix, SMT
    DEF JointMembershipWitnesses, JointCommitProtection
<1>peer. ProtectedPeer(target, certificate.term, server)
    BY <1>certificate, <1>data, SMT DEF ProtectedPeer
<1>after. ProtectedPeer(target, certificate.term, server)'
    BY <1>base, <1>target, <1>data, <1>protection, <1>peer, ProtectedPeerNext, SMT
<1> QED BY <1>certificate, <1>target, <1>after, SMT DEF ProtectedPeer

LEMMA IncreasingAppendReceiveFields ==
    ASSUME TypeOK, NEW request \in AppendRequests,
           HandleAppendEntriesRequest(request.mdest, request.msource, request),
           commitIndex'[request.mdest] > commitIndex[request.mdest]
    PROVE /\ request.mterm = currentTerm[request.mdest] /\ state[request.mdest] # Leader
          /\ AppendAnchorMatches(request, request.mdest)
          /\ commitIndex'[request.mdest] = request.mcommitIndex /\ request.mcommitIndex > 0
<1>fields. request.mdest \in Server /\ request.mterm \in Nat /\ request.mcommitIndex \in Nat
           /\ currentTerm[request.mdest] \in Nat /\ commitIndex[request.mdest] \in Nat
    BY MessageFieldsTypeOK, Zenon DEF AppendRequests, TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>changed. ~UNCHANGED commitIndex BY SMT
<1>accepted.
        /\ request.mterm <= currentTerm[request.mdest] /\ ~(request.mterm < currentTerm[request.mdest])
        /\ state[request.mdest] # Leader /\ AppendAnchorMatches(request, request.mdest)
        /\ commitIndex' = [commitIndex EXCEPT ![request.mdest] = request.mcommitIndex]
    BY <1>changed, Zenon DEF HandleAppendEntriesRequest, AppendAnchorMatches
<1>term. request.mterm = currentTerm[request.mdest] BY <1>fields, <1>accepted, SMT
<1>post. commitIndex'[request.mdest] = request.mcommitIndex /\ request.mcommitIndex > 0
    BY <1>fields, <1>accepted, SMT DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>term, <1>accepted, <1>post, SMT

LEMMA FollowerCommitIncreaseHasAppendRequest ==
    ASSUME TypeOK, [Next]_vars, NEW server \in Server, state'[server] # Leader,
           commitIndex'[server] > commitIndex[server]
    PROVE \E request \in AppendRequests:
              /\ request.mdest = server
              /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
              /\ commitIndex'[server] = request.mcommitIndex
              /\ request.mterm = currentTerm[server]
              /\ state[server] # Leader /\ AppendAnchorMatches(request, server)
<1>types. commitIndex[server] \in Nat BY SMT DEF TypeOK, LogVarsTypeOK
<1>changed. ~UNCHANGED commitIndex BY SMT
<1>restart. \A actor \in Server: ~Restart(actor)
    BY <1>types, SMT DEF Restart, TypeOK, LogVarsTypeOK
<1>advance. \A actor \in Server: ~AdvanceCommitIndex(actor)
    BY <1>types, SMT DEF AdvanceCommitIndex, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>other_actions.
        /\ \A actor \in Server: ~(Timeout(actor) \/ BecomeLeader(actor) \/ LeaderStepDown(actor))
        /\ \A actor \in Server, payload \in ClientPayload: ~ClientRequest(actor, payload)
        /\ \A actor, peer \in Server: ~AppendEntries(actor, peer)
    BY <1>changed, Zenon DEF Timeout, BecomeLeader, LeaderStepDown, ClientRequest, AppendEntries
<1>receive. PICK request \in messages: Receive(request)
    BY <1>changed, <1>restart, <1>advance, <1>other_actions, SMT DEF Next, vars
<1>handled. request.mtype = AppendEntriesRequest
           /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    BY <1>receive, <1>changed, SMT
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse, HandleAppendEntriesResponse
<1>fields. request.mdest \in Server
    BY <1>receive, <1>handled, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK
<1>update. \E value: commitIndex' = [commitIndex EXCEPT ![request.mdest] = value]
    BY <1>handled, <1>changed, Zenon DEF HandleAppendEntriesRequest
<1>recipient. request.mdest = server
    BY <1>fields, <1>update, <1>types, SMT DEF TypeOK, LogVarsTypeOK
<1>append. request \in AppendRequests /\ commitIndex'[request.mdest] > commitIndex[request.mdest]
    BY <1>handled, <1>recipient, SMT DEF AppendRequests
<1>accepted. request.mterm = currentTerm[server] /\ state[server] # Leader
            /\ AppendAnchorMatches(request, server) /\ commitIndex'[server] = request.mcommitIndex
    BY <1>handled, <1>recipient, <1>append, IncreasingAppendReceiveFields, SMT
<1> QED BY <1>handled, <1>recipient, <1>append, <1>accepted, SMT

LEMMA AppendReceiveCommitPrefixHasCertificate ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), AppendCommitIndexBound, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW request \in AppendRequests, HandleAppendEntriesRequest(request.mdest, request.msource, request),
           commitIndex'[request.mdest] > commitIndex[request.mdest]
    PROVE /\ commitIndex'[request.mdest] <= Len(log'[request.mdest])
          /\ \E certificate \in commits:
                 /\ certificate.term <= currentTerm'[request.mdest]
                 /\ IsPrefix(Committed(request.mdest)', CommitTarget(certificate))
<1>base. TypeOK /\ TypeOK' /\ WitnessEdgeConsistency(ancestry)
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, OrderedTermPrefixesAreEdgeConsistent, SMT
    DEF Next, Receive, HandleMsg, AppendRequests, MembershipJointCore, JointMembershipWitnesses,
        ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>fields. request.mdest \in Server /\ request.msource \in Server /\ request.mcommitIndex \in Nat
          /\ request.mterm \in Nat /\ request.mentries \in Seq(LogEntry)
    BY <1>base, MessageFieldsTypeOK, SMT DEF AppendRequests, TypeOK, MsgTypeOK
<1>accepted. request.mterm = currentTerm[request.mdest] /\ state[request.mdest] # Leader
          /\ AppendAnchorMatches(request, request.mdest) /\ commitIndex'[request.mdest] = request.mcommitIndex
          /\ request.mcommitIndex > 0
    BY <1>base, IncreasingAppendReceiveFields, SMT
<1>prefix. PICK prefix \in Seq(LogEntry):
        RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
    BY SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
<1>length. Len(request.mentries) <= 1 /\ request.mcommitIndex <= Len(prefix)
    BY <1>prefix, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix,
        AppendCommitIndexBound, RequestPrefixData
<1>received. IsPrefix(prefix, log'[request.mdest])
    BY <1>base, <1>fields, <1>accepted, <1>prefix, <1>length, AcceptedAppendHasExactPrefix, SMT
    DEF JointMembershipWitnesses
<1>certificate. PICK certificate \in commits:
        certificate.term <= request.mterm /\ IsPrefix(SubSeq(prefix, 1, request.mcommitIndex), CommitTarget(certificate))
    BY <1>accepted, <1>prefix, AdvertisedCommitPrefixHasCertificate, SMT
<1>cut. request.mcommitIndex <= Len(log'[request.mdest])
          /\ SubSeq(log'[request.mdest], 1, request.mcommitIndex) = SubSeq(prefix, 1, request.mcommitIndex)
    BY <1>base, <1>fields, <1>prefix, <1>length, <1>received, PhysicalPrefixDeterminesShorterCut, SMT
    DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>accepted, <1>certificate, <1>cut, SMT DEF Committed, HandleAppendEntriesRequest

LEMMA PostLeaderHasLocalCommitPrefix ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK', NEW ancestry, NEW commits, JointMembershipWitnesses(nextVoteHistory, ancestry, commits)',
           NEW leader \in Server, state'[leader] = Leader, commitIndex'[leader] > 0
    PROVE /\ commitIndex'[leader] <= Len(log'[leader])
          /\ \E certificate \in commits:
                 /\ certificate.term <= currentTerm'[leader]
                 /\ IsPrefix(Committed(leader)', CommitTarget(certificate))
<1>certificate. PICK certificate \in commits:
        commitIndex'[leader] <= certificate.index /\ certificate.term <= currentTerm'[leader]
    BY SMT DEF JointMembershipWitnesses, LocalCommitEvidence
<1>data. CommitPrefixData(certificate) /\ log'[leader] \in Seq(LogEntry) /\ commitIndex'[leader] \in Nat
    BY <1>certificate, SMT DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate,
        CommitPrefixData, TypeOK, LogVarsTypeOK
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) = certificate.index
    BY <1>data, CommitPrefixDataTargetProperties, SMT
<1>held. IsPrefix(CommitTarget(certificate), log'[leader])
    BY <1>certificate, SMT DEF JointMembershipWitnesses, CommitLeaderProtection
<1>bound. commitIndex'[leader] <= Len(log'[leader])
    BY <1>certificate, <1>data, <1>target, <1>held, LenProperties, SMT DEF IsPrefix
<1>prefix. IsPrefix(Committed(leader)', CommitTarget(certificate))
    BY <1>certificate, <1>data, <1>target, <1>held, <1>bound, CutOfComparablePrefixesIsInsideCertificate, SMT DEF Committed
<1> QED BY <1>certificate, <1>bound, <1>prefix, SMT

LEMMA SelectedHistoryPreservesLocalCommitPrefixes ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), AppendCommitIndexBound, [Next]_vars,
           NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           LocalCommitPrefixEvidence(commits), NEW largerAncestry, NEW largerCommits,
           commits \subseteq largerCommits, JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
    PROVE LocalCommitPrefixEvidence(largerCommits)'
<1>base. MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK'
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointInv, MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW server \in Server
             PROVE /\ commitIndex'[server] <= Len(log'[server])
                   /\ commitIndex'[server] > 0 => \E certificate \in largerCommits:
                          /\ certificate.term <= currentTerm'[server]
                          /\ IsPrefix(Committed(server)', CommitTarget(certificate))
    BY SMT DEF LocalCommitPrefixEvidence
<1>zero. CASE commitIndex'[server] = 0
    BY <1>base, <1>zero, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1>leader. CASE commitIndex'[server] > 0 /\ state'[server] = Leader
    BY <1>base, <1>leader, PostLeaderHasLocalCommitPrefix, SMT
<1>old. CASE commitIndex'[server] > 0 /\ commitIndex'[server] <= commitIndex[server] /\ state'[server] # Leader
    <2>positive. commitIndex[server] > 0
        BY <1>base, <1>old, SMT DEF TypeOK, LogVarsTypeOK
    <2>target. PICK target \in Seq(LogEntry): target = Committed(server)
        BY <1>base, SubSeqTypeOK, SMT DEF LocalCommitPrefixEvidence, Committed, TypeOK, LogVarsTypeOK
    <2>certificate. PICK certificate \in commits:
            /\ certificate.term <= currentTerm'[server]
            /\ IsPrefix(target, CommitTarget(certificate)) /\ IsPrefix(target, log'[server])
        BY <1>base, <2>positive, <2>target, ExistingLocalCommitPrefixSurvives, SMT
    <2>data. Len(target) = commitIndex[server] /\ CommitTarget(certificate) \in Seq(LogEntry)
              /\ log'[server] \in Seq(LogEntry) /\ commitIndex'[server] \in Nat
        BY <1>base, <2>target, <2>certificate, CommitCertificateTargetProperties,
           SubSeqProperties, ElementOfSeq, LenProperties, SMT
        DEF LocalCommitPrefixEvidence, JointMembershipWitnesses, CommitCertificateFamily,
            TypeOK, LogVarsTypeOK, Committed
    <2>cut. commitIndex'[server] <= Len(log'[server])
              /\ SubSeq(log'[server], 1, commitIndex'[server]) = SubSeq(target, 1, commitIndex'[server])
        BY <1>old, <2>target, <2>certificate, <2>data, PhysicalPrefixDeterminesShorterCut, SMT
    <2>inside. IsPrefix(SubSeq(target, 1, commitIndex'[server]), CommitTarget(certificate))
        BY <1>old, <2>target, <2>certificate, <2>data, CutOfComparablePrefixesIsInsideCertificate, LenProperties, SMT DEF IsPrefix
    <2> QED BY <2>certificate, <2>cut, <2>inside, SMT DEF Committed
<1>increase. CASE commitIndex'[server] > commitIndex[server] /\ state'[server] # Leader
    <2>request. PICK request \in AppendRequests:
            /\ request.mdest = server /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        BY <1>base, <1>increase, FollowerCommitIncreaseHasAppendRequest, SMT
    <2>covered. commitIndex'[server] <= Len(log'[server])
              /\ \E certificate \in commits:
                     /\ certificate.term <= currentTerm'[server]
                     /\ IsPrefix(Committed(server)', CommitTarget(certificate))
        BY <1>base, <1>increase, <2>request, AppendReceiveCommitPrefixHasCertificate, SMT
    <2> QED BY <2>covered, SMT
<1> QED BY <1>base, <1>zero, <1>leader, <1>old, <1>increase, SMT DEF TypeOK, LogVarsTypeOK

LEMMA SelectedCommitsImplyLogInv ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), LocalCommitPrefixEvidence(commits)
    PROVE LogInv
<1> SUFFICES ASSUME NEW left \in Server, NEW right \in Server
             PROVE IsPrefix(Committed(left), Committed(right)) \/ IsPrefix(Committed(right), Committed(left))
    BY SMT DEF LogInv
<1>base. MembershipJointCore(voteHistory) /\ TypeOK
    BY JointCoreBase, SMT
<1>types. Committed(left) \in Seq(LogEntry) /\ Committed(right) \in Seq(LogEntry)
          /\ commitIndex[left] \in Nat /\ commitIndex[right] \in Nat
    BY <1>base, SubSeqTypeOK, SMT
    DEF LocalCommitPrefixEvidence, Committed, TypeOK, LogVarsTypeOK
<1>empty. CASE commitIndex[left] = 0 \/ commitIndex[right] = 0
    BY <1>types, <1>empty, SubSeqEmpty, LenProperties, SMT DEF Committed, IsPrefix
<1>nonempty. CASE commitIndex[left] > 0 /\ commitIndex[right] > 0
    <2>left. PICK first \in commits: IsPrefix(Committed(left), CommitTarget(first))
        BY <1>nonempty, SMT DEF LocalCommitPrefixEvidence
    <2>right. PICK second \in commits: IsPrefix(Committed(right), CommitTarget(second))
        BY <1>nonempty, SMT DEF LocalCommitPrefixEvidence
    <2>targets. CommitTarget(first) \in Seq(LogEntry) /\ CommitTarget(second) \in Seq(LogEntry)
              /\ (IsPrefix(CommitTarget(first), CommitTarget(second)) \/ IsPrefix(CommitTarget(second), CommitTarget(first)))
        BY <1>base, <2>left, <2>right,
           CommitCertificateTargetProperties, SelectedCommitTargetsAreComparable, SMT
        DEF JointMembershipWitnesses, CommitCertificateFamily
    <2> QED BY <1>types, <2>left, <2>right, <2>targets, PrefixesWithBoundedLength, SequencePrefixTransitive, SMT
<1> QED BY <1>types, <1>empty, <1>nonempty, SMT

LEMMA SelectedCommitsImplyLeaderCompleteness ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), LocalCommitPrefixEvidence(commits)
    PROVE LeaderCompletenessInv
<1> SUFFICES ASSUME NEW server \in Server, NEW leader \in CurrentLeaders,
                      currentTerm[server] <= currentTerm[leader]
             PROVE IsPrefix(Committed(server), log[leader]) BY SMT DEF LeaderCompletenessInv
<1>base. MembershipJointCore(voteHistory) /\ TypeOK /\ leader \in Server /\ state[leader] = Leader
    BY JointCoreBase, SMT DEF CurrentLeaders
<1>types. Committed(server) \in Seq(LogEntry) /\ log[leader] \in Seq(LogEntry)
          /\ commitIndex[server] \in Nat /\ currentTerm[server] \in Nat /\ currentTerm[leader] \in Nat
    BY <1>base, SubSeqTypeOK, SMT
    DEF LocalCommitPrefixEvidence, Committed, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>empty. CASE commitIndex[server] = 0
    BY <1>types, <1>empty, SubSeqEmpty, LenProperties, SMT DEF Committed, IsPrefix
<1>nonempty. CASE commitIndex[server] > 0
    <2>certificate. PICK certificate \in commits:
            certificate.term <= currentTerm[server] /\ IsPrefix(Committed(server), CommitTarget(certificate))
        BY <1>nonempty, SMT DEF LocalCommitPrefixEvidence
    <2>data. CommitTarget(certificate) \in Seq(LogEntry) /\ certificate.term \in Nat
        BY <2>certificate, CommitCertificateTargetProperties, SMT
        DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
    <2>leader. IsPrefix(CommitTarget(certificate), log[leader])
        BY <1>base, <1>types, <2>certificate, <2>data, SMT
        DEF JointMembershipWitnesses, CommitLeaderProtection
    <2> QED BY <1>types, <2>certificate, <2>data, <2>leader, SequencePrefixTransitive, SMT
<1> QED BY <1>types, <1>empty, <1>nonempty, SMT

LEMMA SelectedCommitsImplyQuorumLog ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits),
           CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns), LocalCommitPrefixEvidence(commits)
    PROVE QuorumLogInv
<1> SUFFICES ASSUME NEW server \in Server,
                      NEW quorum \in Quorums(LastConfiguration(server))
             PROVE \E peer \in quorum: IsPrefix(Committed(server), log[peer])
    BY SMT DEF QuorumLogInv
<1>base. MembershipJointCore(voteHistory) /\ TypeOK /\ log[server] \in Seq(LogEntry)
          /\ LastConfiguration(server) \subseteq Server
    BY JointCoreBase, ConfigurationType, SMT
    DEF LastConfiguration, TypeOK, LogVarsTypeOK
<1>empty. CASE commitIndex[server] = 0
    <2>peer. PICK peer \in quorum: TRUE
        BY <1>base, ConfigurationQuorumNonempty, SMT
    <2>type. peer \in Server /\ log[peer] \in Seq(LogEntry)
        BY <1>base, <2>peer, SMT DEF TypeOK, LogVarsTypeOK, Quorums
    <2>prefix. IsPrefix(Committed(server), log[peer])
        BY <1>empty, <2>type, SubSeqEmpty, LenProperties, SMT DEF Committed, IsPrefix
    <2> QED BY <2>peer, <2>prefix, SMT
<1>nonempty. CASE commitIndex[server] > 0
    <2>target. PICK target \in Seq(LogEntry): target = Committed(server) /\ IsPrefix(target, log[server])
        BY <1>base, SubSeqTypeOK, SubSeqProperties, ElementOfSeq, LenProperties, SMT
        DEF LocalCommitPrefixEvidence, Committed, TypeOK, LogVarsTypeOK, IsPrefix
    <2>certificate. PICK certificate \in commits: IsPrefix(target, CommitTarget(certificate))
        BY <1>nonempty, <2>target, SMT DEF LocalCommitPrefixEvidence
    <2>word. TermsOrdered(log[server]) /\ CoveredPrefix(ancestry, log[server])
        BY <1>base, CurrentLogPrefixCovered, WholeSequencePrefix, LenProperties, JointCoreBase, SMT
        DEF JointMembershipWitnesses, MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered, IsPrefix
    <2>blocker. PICK blocker \in commits:
            /\ CertificateBlocksConfiguration(blocker, ConfigOf(log[server]))
            /\ IsPrefix(target, CommitTarget(blocker))
        BY <1>base, <2>target, <2>certificate, <2>word, HeldCertifiedPrefixHasBlockingCertificate, SMT
    <2>peer. PICK peer \in quorum \cap blocker.replication: TRUE
        BY <2>blocker, SMT DEF CertificateBlocksConfiguration, LastConfiguration
    <2>physical. CommitTarget(blocker) \in Seq(LogEntry)
              /\ blocker.replication \subseteq ProtectedVoters(CommitTarget(blocker))
        BY <2>blocker, RetainedCommitReplicasHoldTarget, SMT
    <2>held. IsPrefix(target, log[peer])
        BY <1>base, <2>target, <2>blocker, <2>peer, <2>physical, SequencePrefixTransitive, SMT
        DEF ProtectedVoters, TypeOK, LogVarsTypeOK
    <2> QED BY <2>target, <2>peer, <2>held, SMT
<1> QED BY <1>base, <1>empty, <1>nonempty, SMT DEF TypeOK, LogVarsTypeOK

\* Cover internal entries as well as log tips: a peer may already hold
\* entries from a later term while the original leader remains in office.
LEMMA CurrentLeaderContainsEverySameTermIndex ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW leader \in Server,
           state[leader] = Leader, NEW peer \in Server,
           NEW index \in DOMAIN log[peer], log[peer][index].term = currentTerm[leader]
    PROVE index \in DOMAIN log[leader] /\ log[leader][index].term = currentTerm[leader]
<1>base. TypeOK /\ log[peer] \in Seq(LogEntry) /\ log[leader] \in Seq(LogEntry)
    BY JointCoreBase, SMT DEF TypeOK, LogVarsTypeOK
<1>edge. LogEntryEdge(log[peer], index) \in HistoricalEntryEdges
    BY SMT DEF HistoricalEntryEdges
<1>witness. PICK witness \in ancestry: witness.edge = LogEntryEdge(log[peer], index)
    BY <1>edge, SMT DEF JointMembershipWitnesses, CoversEntryEdges
<1>term. witness.edge.term = currentTerm[leader]
    BY <1>witness, SMT DEF LogEntryEdge
<1>owner. witness.owner = leader
    BY <1>term, LiveAncestryIdentifiesCurrentOwners, SMT
<1>prefix.
        /\ witness.prefix \in Seq(LogEntry) /\ IsPrefix(witness.prefix, log[leader])
        /\ Len(witness.prefix) = index /\ witness.prefix[index].term = currentTerm[leader]
    <2>certificate. CertificateWitness(voteHistory, witness)
        BY <1>witness, SMT DEF JointMembershipWitnesses, CertificateFamily
    <2>data. WitnessPrefixData(witness) /\ OwnerPrefix(witness.owner, witness.edge.term, witness.prefix)
        BY <2>certificate, Zenon DEF CertificateWitness
    <2>fields. witness.prefix \in Seq(LogEntry) /\ Len(witness.prefix) = index
        BY <2>data, <1>witness, SMT DEF WitnessPrefixData, LogEntryEdge
    <2>last. witness.prefix[index].term = currentTerm[leader]
        BY <2>data, <2>fields, <1>term, WitnessPrefixLastTerm, SMT DEF LastTerm
    <2>held. IsPrefix(witness.prefix, log[leader])
        BY <2>data, <1>owner, <1>term, SMT DEF OwnerPrefix
    <2> QED BY <2>fields, <2>last, <2>held, SMT
<1>position. index \in 1..Len(witness.prefix) /\ index \in DOMAIN log[leader]
    BY <1>base, <1>prefix, LenProperties, SMT DEF IsPrefix
<1>entry. witness.prefix[index] = log[leader][index]
    BY <1>base, <1>prefix, <1>position, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1> QED BY <1>prefix, <1>position, <1>entry, SMT

LEMMA JointCoreImpliesGreatestCurrentTermIndex ==
    ASSUME NEW voteHistory
    PROVE MembershipJointCore(voteHistory) => ElectionSafetyInv
<1> SUFFICES ASSUME MembershipJointCore(voteHistory), NEW leader \in Server,
                      state[leader] = Leader, NEW peer \in Server
             PROVE MaxOrZero({index \in DOMAIN log[leader]: log[leader][index].term = currentTerm[leader]})
                   >= MaxOrZero({index \in DOMAIN log[peer]: log[peer][index].term = currentTerm[leader]})
    BY Zenon DEF ElectionSafetyInv
<1>base. log[peer] \in Seq(LogEntry) /\ log[leader] \in Seq(LogEntry)
    BY JointCoreBase, SMT DEF TypeOK, LogVarsTypeOK
<1>selected. PICK ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF MembershipJointCore
<1> DEFINE smaller == {index \in DOMAIN log[peer]: log[peer][index].term = currentTerm[leader]}
           larger == {index \in DOMAIN log[leader]: log[leader][index].term = currentTerm[leader]}
<1>subset. smaller \subseteq larger
    BY <1>selected, CurrentLeaderContainsEverySameTermIndex, SMT DEF smaller, larger
<1>bounded. Len(log[leader]) \in Nat
          /\ smaller \subseteq 1..Len(log[leader]) /\ larger \subseteq 1..Len(log[leader])
    BY <1>base, <1>subset, LenProperties, SMT DEF smaller, larger
<1> QED BY <1>subset, <1>bounded, PositiveIndexMaxOrZeroSubsetMonotone,
    PositiveIndexMaxOrZeroProperties, SMT DEF smaller, larger

LEMMA OpportunitySnapshotData ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE /\ IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot) /\ TermsOrdered(snapshot)
          /\ \A index \in DOMAIN snapshot: snapshot[index].term < term
<1>base. TypeOK /\ TermsOrdered(log[candidate]) /\ LogTermBoundInv
    BY JointCoreBase, LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>covered. IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot)
    BY CampaignOpportunitySnapshotCovered, SMT DEF OpportunityCertificate
<1>ordered. TermsOrdered(snapshot)
    BY <1>base, <1>covered, TermsOrderedOnPrefix, LenProperties, SMT DEF TypeOK, LogVarsTypeOK, IsPrefix
<1>terms. \A index \in DOMAIN snapshot: snapshot[index].term < term
    <2>future. CASE currentTerm[candidate] < term
        BY <1>base, <2>future, ElementOfSeq, SMT
        DEF OpportunityCertificate, CampaignOpportunity, LogTermBoundInv, TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LogEntry
    <2>current. CASE currentTerm[candidate] = term
        BY <1>base, <2>current, CampaignPrefixProperties, SMT
        DEF OpportunityCertificate, CampaignOpportunity, TypeOK, LogVarsTypeOK
    <2> QED BY <2>future, <2>current, SMT DEF OpportunityCertificate, CampaignOpportunity
<1> QED BY <1>covered, <1>ordered, <1>terms, SMT

LEMMA NonleaderOpportunityUsesFullLog ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           CampaignOpportunity(candidate, term, snapshot), ~(currentTerm[candidate] = term /\ state[candidate] = Leader)
    PROVE snapshot = log[candidate]
<1>base. TypeOK /\ CandidateCurrentTermFree
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, MembershipElectionBase
<1> QED BY <1>base, CampaignPrefixBeforeTerm, SMT
    DEF CampaignOpportunity, CandidateCurrentTermFree, TypeOK, LogVarsTypeOK

LEMMA OpportunityAboveCertificateContainsTarget ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW initial, RetainedCommitCertificate(voteHistory, initial), CoveredPrefix(ancestry, initial.entries),
           initial.replication \subseteq ProtectedVoters(CommitTarget(initial)),
           LaterTermPrefixProtection(ancestry, CommitTarget(initial), initial.term),
           ProtectedAppendRequests(CommitTarget(initial), initial.term), ProtectedLeaders(CommitTarget(initial), initial.term),
           NEW candidate \in Server, NEW term \in Nat, initial.term < term,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE IsPrefix(CommitTarget(initial), log[candidate])
<1>base. TypeOK /\ \A server \in Server: TermsOrdered(log[server])
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>data. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>initial. CommitLogData(initial) /\ CommitTarget(initial) \in Seq(LogEntry) /\ initial.term \in Nat
    BY CommitCertificateTargetProperties, SMT DEF RetainedCommitCertificate, CommitLogData, CommitPrefixData
<1>leader. CASE currentTerm[candidate] = term /\ state[candidate] = Leader
    BY <1>leader, SMT DEF ProtectedLeaders
<1>other. CASE ~(currentTerm[candidate] = term /\ state[candidate] = Leader)
    <2>snapshot. snapshot = log[candidate] /\ CoveredPrefix(ancestry, snapshot) /\ TermsOrdered(snapshot)
        BY <1>other, NonleaderOpportunityUsesFullLog, OpportunitySnapshotData, SMT DEF OpportunityCertificate
    <2> SUFFICES ASSUME ~IsPrefix(CommitTarget(initial), log[candidate]) PROVE FALSE BY SMT
    <2>blocker. PICK blocker \in TermCommits(commits, initial.term) \cup {initial}:
            /\ CertificateBlocksConfiguration(blocker, ConfigOf(snapshot))
            /\ ~SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
        BY <1>data, <1>initial, <2>snapshot, MissingProtectedTargetHasTermBoundedBlocker, SMT
    <2>retained. RetainedCommitCertificate(voteHistory, blocker) /\ CoveredPrefix(ancestry, blocker.entries)
                  /\ ProtectedAppendRequests(CommitTarget(blocker), blocker.term)
        BY <2>blocker, SMT
        DEF TermCommits, JointMembershipWitnesses, CommitCertificateFamily, JointCommitProtection,
            CausalHistoryMetadata, CausalCampaignWitnesses, CommitPrefixCoverage
    <2>term. blocker.term < term
        BY <1>initial, <2>blocker, <2>retained, SMT DEF TermCommits, RetainedCommitCertificate
    <2>physical. blocker.replication \subseteq ProtectedVoters(CommitTarget(blocker))
        BY <2>blocker, RetainedCommitReplicasHoldTarget, SMT DEF TermCommits
    <2>properties. RetainedCommitCertificate(voteHistory, blocker) /\ CoveredPrefix(ancestry, blocker.entries)
                  /\ blocker.term < term /\ CommitTarget(blocker) \in Seq(LogEntry)
                  /\ blocker.replication \subseteq ProtectedVoters(CommitTarget(blocker))
                  /\ ProtectedAppendRequests(CommitTarget(blocker), blocker.term)
        BY <2>retained, <2>term, <2>physical, CommitCertificateTargetProperties, SMT
    <2>quorum. support \in Quorums(ConfigOf(snapshot))
        BY SMT DEF OpportunityCertificate, LatestConfigurationOccurrence
    <2>peer. PICK peer \in support \cap blocker.replication: TRUE
        BY <2>blocker, <2>quorum, SMT DEF CertificateBlocksConfiguration
    <2>held. peer \in Server /\ IsPrefix(CommitTarget(blocker), log[peer])
        BY <2>peer, <2>properties, SMT DEF ProtectedVoters
    <2>recorded. CASE RecordedCampaignVote(voteHistory, peer, candidate, term)
        <3>fresh. SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
            BY <2>properties, <2>peer, <2>recorded, RecordedReplicationVoterHasFreshSnapshot, SMT
            DEF CausalHistoryMetadata
        <3> QED BY <2>blocker, <3>fresh, SMT
    <2>self. CASE peer = candidate
        <3>fresh. SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
            BY <1>base, <2>snapshot, <2>properties, <2>held, <2>self,
               SnapshotFreshnessCoversHeldPrefix, LastTermTypeOK, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
        <3> QED BY <2>blocker, <3>fresh, SMT
    <2>fresh_peer. CASE NewPeerVoteEligible(peer, candidate, term, snapshot)
        <3>fresh. SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
            BY <1>base, <2>properties, <2>held, <2>fresh_peer, SnapshotFreshnessCoversHeldPrefix, SMT
            DEF NewPeerVoteEligible, SnapshotFreshFor, TypeOK, LogVarsTypeOK
        <3> QED BY <2>blocker, <3>fresh, SMT
    <2> QED BY <2>peer, <2>recorded, <2>self, <2>fresh_peer, SMT DEF OpportunityCertificate, OpportunityVoters
<1> QED BY <1>leader, <1>other, SMT

LEMMA CausalOpportunityContainsEarlierCommitTargets ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE \A certificate \in commits: certificate.term < term => IsPrefix(CommitTarget(certificate), snapshot)
<1> SUFFICES ASSUME NEW certificate \in commits, certificate.term < term
             PROVE IsPrefix(CommitTarget(certificate), snapshot) BY SMT
<1>data. RetainedCommitCertificate(voteHistory, certificate) /\ CoveredPrefix(ancestry, certificate.entries)
          /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
          /\ ProtectedAppendRequests(CommitTarget(certificate), certificate.term)
          /\ ProtectedLeaders(CommitTarget(certificate), certificate.term)
          /\ certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
    BY RetainedCommitReplicasHoldTarget, SMT
    DEF JointMembershipWitnesses, CommitCertificateFamily, JointCommitProtection,
        CausalHistoryMetadata, CausalCampaignWitnesses, CommitPrefixCoverage
<1>prefix. IsPrefix(CommitTarget(certificate), log[candidate])
    BY <1>data, OpportunityAboveCertificateContainsTarget, SMT
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
              /\ LastTerm(CommitTarget(certificate)) < term
    BY <1>data, CommitCertificateTargetProperties, LenProperties, SMT DEF RetainedCommitCertificate, LastTerm
<1> QED BY <1>prefix, <1>target, CampaignContainsOlderProtectedPrefix, SMT DEF OpportunityCertificate

LEMMA CausalOpportunityContainsSameTermCoveredWord ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW target \in Seq(LogEntry), Len(target) > 0, CoveredPrefix(ancestry, target),
           NEW candidate \in Server, NEW term \in Nat, LastTerm(target) = term,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE IsPrefix(target, log[candidate])
<1>pure. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>witness. PICK witness \in ancestry: witness.prefix = target /\ witness.edge.term = term
    BY <1>pure, DataCoveredWordHasLastWitness, SMT DEF BarrierExclusionData
<1>data. CertificateWitness(voteHistory, witness)
    BY <1>witness, SMT DEF JointMembershipWitnesses, CertificateFamily
<1>campaign. PICK campaign \in campaigns:
        /\ campaign.candidate = witness.owner /\ campaign.term = term /\ campaign.snapshot = witness.snapshot
    BY <1>witness, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CreatorCampaignCoverage
<1>profile. CausalCampaignData(voteHistory, ancestry, campaign)
          /\ \A certificate \in commits: certificate.term < term => IsPrefix(CommitTarget(certificate), witness.snapshot)
    BY <1>campaign, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CampaignCommitPrefixes
<1>query. CoveredPrefix(ancestry, snapshot) /\ TermsOrdered(snapshot)
          /\ \A index \in DOMAIN snapshot: snapshot[index].term < term
    BY OpportunitySnapshotData, SMT
<1>commits. \A certificate \in commits: certificate.term < term => IsPrefix(CommitTarget(certificate), snapshot)
    BY CausalOpportunityContainsEarlierCommitTargets, SMT
<1>adjacent. EqualOrAdjacentConfigurations(ConfigOf(witness.snapshot), ConfigOf(snapshot))
    BY <1>pure, <1>data, <1>campaign, <1>profile, <1>query, <1>commits,
       PrefixesProtectedBelowTermHaveAdjacentConfigurations, SMT
    DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, CertificateWitness, WitnessPrefixData
<1>intersects. witness.support \cap support # {}
    BY <1>data, <1>adjacent, EqualOrAdjacentQuorumsIntersect, SMT
    DEF CertificateWitness, RetainedElectionCertificate, OpportunityCertificate, LatestConfigurationOccurrence
<1>owner. witness.owner = candidate
    BY <1>data, <1>witness, <1>intersects, RecordedSupportMeetsOpportunityOnlyForOwner, SMT
    DEF CertificateWitness, WitnessPrefixData, RetainedElectionCertificate
<1>epoch. currentTerm[candidate] >= term
    BY <1>data, <1>witness, <1>owner, SMT DEF CertificateWitness, OwnerPrefix
<1> QED BY <1>data, <1>witness, <1>owner, <1>epoch, JointCoreBase, SMT
    DEF CertificateWitness, OwnerPrefix, OpportunityCertificate, CampaignOpportunity, TypeOK, ServerVarsTypeOK

LEMMA CausalWitnessesSupplyOpportunityCommitPrefixes ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityCommitPrefixes(voteHistory, commits)
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support, OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
                      NEW certificate \in commits, certificate.term <= term
             PROVE IsPrefix(CommitTarget(certificate), log[candidate]) BY SMT DEF OpportunityCommitPrefixes
<1>data. RetainedCommitCertificate(voteHistory, certificate) /\ CoveredPrefix(ancestry, certificate.entries)
          /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
    BY CommitCertificateTargetProperties, LenProperties, SMT
    DEF JointMembershipWitnesses, CommitCertificateFamily, CausalHistoryMetadata,
        CausalCampaignWitnesses, CommitPrefixCoverage, RetainedCommitCertificate, LastTerm
<1>strict. CASE certificate.term < term
    <2>prefix. IsPrefix(CommitTarget(certificate), snapshot)
        BY <1>strict, CausalOpportunityContainsEarlierCommitTargets, SMT
    <2> QED BY <1>data, <2>prefix, CampaignOpportunitySnapshotCovered, JointCoreBase, SequencePrefixTransitive, SMT
        DEF OpportunityCertificate, TypeOK, LogVarsTypeOK
<1>same. CASE certificate.term = term
    <2>covered. CoveredPrefix(ancestry, CommitTarget(certificate))
        BY <1>data, CommitCertificateTargetProperties, CoveredPrefixRestriction, SMT DEF RetainedCommitCertificate
    <2> QED BY <1>data, <1>same, <2>covered, CausalOpportunityContainsSameTermCoveredWord, SMT
<1> QED BY <1>data, <1>strict, <1>same, SMT DEF RetainedCommitCertificate

LEMMA CausalWitnessesSupplyOpportunityEvidencePrefixes ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityEvidencePrefixes(voteHistory)
<1>base. TypeOK BY JointCoreBase, SMT
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support, OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
                      NEW target \in EvidenceAgreementTargets(voteHistory), LastTerm(target) <= term
             PROVE IsPrefix(target, log[candidate]) BY SMT DEF OpportunityEvidencePrefixes
<1>certificate. PICK certificate:
        /\ RetainedCommitCertificate(voteHistory, certificate) /\ certificate.entries = target
        /\ certificate.index = Len(target) /\ IsPrefix(target, log[certificate.leader])
    BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
<1>data. target \in Seq(LogEntry) /\ Len(target) > 0 /\ LastTerm(target) = certificate.term
          /\ certificate.term \in Nat /\ CommitTarget(certificate) = target /\ certificate.leader \in Server
    BY <1>certificate, CommitCertificateTargetProperties, WholeSequencePrefix, LenProperties, SMT
    DEF RetainedCommitCertificate, CommitTarget, LastTerm
<1>covered. CoveredPrefix(ancestry, target)
    BY <1>base, <1>certificate, <1>data, CurrentLogPrefixCovered, SMT
    DEF JointMembershipWitnesses, TypeOK, LogVarsTypeOK
<1>strict. CASE LastTerm(target) < term
    <2>protection. LaterTermPrefixProtection(ancestry, target, certificate.term)
                  /\ ProtectedAppendRequests(target, certificate.term) /\ ProtectedLeaders(target, certificate.term)
        BY <1>data, SMT DEF JointMembershipWitnesses, JointEvidenceProtection
    <2>physical. certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
        BY <1>certificate, <1>data, <2>protection, ProtectedRetainedCertificateHasPhysicalQuorum, SMT
        DEF CausalHistoryMetadata
    <2> QED BY <1>certificate, <1>data, <1>covered, <1>strict, <2>protection, <2>physical,
        OpportunityAboveCertificateContainsTarget, SMT
<1>same. CASE LastTerm(target) = term
    BY <1>data, <1>covered, <1>same, CausalOpportunityContainsSameTermCoveredWord, SMT
<1> QED BY <1>data, <1>strict, <1>same, SMT

LEMMA EarlierBarrierProfilesIntersect ==
    ASSUME NEW ancestry, NEW commits, BarrierExclusionData(ancestry, commits), NEW term \in Nat,
           NEW left, NEW right, EarlierBarrierProfile(ancestry, commits, term, left),
           EarlierBarrierProfile(ancestry, commits, term, right),
           ConfigOf(left) \subseteq Server, ConfigOf(right) \subseteq Server,
           NEW first \in Quorums(ConfigOf(left)), NEW second \in Quorums(ConfigOf(right))
    PROVE first \cap second # {}
    BY PrefixesProtectedBelowTermHaveAdjacentConfigurations, EqualOrAdjacentQuorumsIntersect, SMT
    DEF EarlierBarrierProfile

LEMMA CausalCampaignHasEarlierBarrierProfile ==
    ASSUME NEW voteHistory, NEW ancestry, NEW commits, NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW campaign \in campaigns
    PROVE EarlierBarrierProfile(ancestry, commits, campaign.term, campaign.snapshot)
    BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignData,
        CausalElectionCertificate, RetainedElectionCertificate, CampaignCommitPrefixes, EarlierBarrierProfile

LEMMA CausalOpportunityHasEarlierBarrierProfile ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE EarlierBarrierProfile(ancestry, commits, term, snapshot)
    BY OpportunitySnapshotData, CausalOpportunityContainsEarlierCommitTargets, SMT DEF EarlierBarrierProfile

LEMMA CausalRetainedSnapshotHasEarlierBarrierProfile ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support), CoveredPrefix(ancestry, snapshot),
           NEW campaign \in campaigns, campaign.candidate = candidate, campaign.term = term
    PROVE EarlierBarrierProfile(ancestry, commits, term, snapshot)
<1>data. CausalCampaignData(voteHistory, ancestry, campaign)
    BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>equal. snapshot = campaign.snapshot
    BY <1>data, HistorySnapshotIsUnique, SMT
    DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, LatestConfigurationOccurrence
<1> QED BY <1>equal, CausalCampaignHasEarlierBarrierProfile, SMT

LEMMA CausalWitnessesSupplyOpportunityElectionIntersections ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityElectionIntersections(voteHistory)
<1>pure. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1> SUFFICES ASSUME NEW left \in Server, NEW right \in Server, NEW term \in Nat,
                      NEW leftSnapshot \in Seq(LogEntry), NEW rightSnapshot \in Seq(LogEntry),
                      NEW leftOccurrence, NEW rightOccurrence, NEW first, NEW second,
                      OpportunityCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, first),
                      OpportunityCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, second)
             PROVE first \cap second # {} BY SMT DEF OpportunityElectionIntersections
<1>profiles. EarlierBarrierProfile(ancestry, commits, term, leftSnapshot)
            /\ EarlierBarrierProfile(ancestry, commits, term, rightSnapshot)
    BY CausalOpportunityHasEarlierBarrierProfile, SMT
<1> QED BY <1>pure, <1>profiles, EarlierBarrierProfilesIntersect, SMT
    DEF OpportunityCertificate, LatestConfigurationOccurrence

LEMMA CausalWitnessesSupplyOpportunityRequestIntersections ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityRequestIntersections(voteHistory)
<1>pure. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support, OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
                      NEW request \in AppendRequests, request.mterm = term
             PROVE \E requestSnapshot \in Seq(LogEntry): \E requestOccurrence, requestSupport:
                       /\ RetainedElectionCertificate(voteHistory, request.msource, term, requestSnapshot, requestOccurrence, requestSupport)
                       /\ support \cap requestSupport # {} BY SMT DEF OpportunityRequestIntersections
<1>campaign. PICK campaign \in campaigns: campaign.candidate = request.msource /\ campaign.term = term
    BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, RequestCampaignCoverage
<1>data. CausalCampaignData(voteHistory, ancestry, campaign)
    BY <1>campaign, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>profiles. EarlierBarrierProfile(ancestry, commits, term, snapshot)
            /\ EarlierBarrierProfile(ancestry, commits, term, campaign.snapshot)
    BY <1>campaign, CausalOpportunityHasEarlierBarrierProfile, CausalCampaignHasEarlierBarrierProfile, SMT
<1>intersection. support \cap campaign.support # {}
    BY <1>pure, <1>data, <1>profiles, EarlierBarrierProfilesIntersect, SMT
    DEF OpportunityCertificate, CausalCampaignData, CausalElectionCertificate,
        RetainedElectionCertificate, LatestConfigurationOccurrence
<1> QED BY <1>campaign, <1>data, <1>intersection, SMT
    DEF CausalCampaignData, CausalElectionCertificate

LEMMA CausalWitnessesSupplyOpportunityAncestryIntersections ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityAncestryIntersections(voteHistory, ancestry)
<1>pure. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1> SUFFICES ASSUME NEW witness \in ancestry, NEW candidate \in Server, NEW term \in Nat,
                      NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
                      OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support), witness.edge.term = term
             PROVE witness.support \cap support # {} BY SMT DEF OpportunityAncestryIntersections
<1>data. CertificateWitness(voteHistory, witness)
    BY SMT DEF JointMembershipWitnesses, CertificateFamily
<1>campaign. PICK campaign \in campaigns:
        /\ campaign.candidate = witness.owner /\ campaign.term = term /\ campaign.snapshot = witness.snapshot
    BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CreatorCampaignCoverage
<1>profiles. EarlierBarrierProfile(ancestry, commits, term, snapshot)
            /\ EarlierBarrierProfile(ancestry, commits, term, witness.snapshot)
    BY <1>campaign, CausalOpportunityHasEarlierBarrierProfile, CausalCampaignHasEarlierBarrierProfile, SMT
<1> QED BY <1>pure, <1>data, <1>profiles, EarlierBarrierProfilesIntersect, SMT
    DEF OpportunityCertificate, CertificateWitness, RetainedElectionCertificate, LatestConfigurationOccurrence

LEMMA CausalWitnessesSupplyOpportunityCommitIntersections ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityCommitIntersections(voteHistory, commits)
<1>pure. BarrierExclusionData(ancestry, commits)
    BY JointWitnessesSupplyBarrierExclusionData, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1> SUFFICES ASSUME NEW certificate \in commits, NEW candidate \in Server, NEW term \in Nat,
                      NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
                      OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support), certificate.term = term
             PROVE certificate.election \cap support # {} BY SMT DEF OpportunityCommitIntersections
<1>data. RetainedCommitCertificate(voteHistory, certificate) /\ CoveredPrefix(ancestry, certificate.entries)
    BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily, CausalHistoryMetadata,
        CausalCampaignWitnesses, CommitPrefixCoverage
<1>covered. CoveredPrefix(ancestry, certificate.snapshot)
    BY <1>data, CoveredPrefixRestriction, SMT DEF RetainedCommitCertificate
<1>request_evidence. TargetRequestEvidence(voteHistory, ancestry, certificate.leader, term, CommitTarget(certificate))
    BY <1>data, RetainedCertificateHasTargetRequestEvidence, SMT DEF CausalHistoryMetadata
<1>campaign. PICK campaign \in campaigns: campaign.candidate = certificate.leader /\ campaign.term = term
    BY <1>request_evidence, TargetSourceEvidenceHasCapturedCampaign, SMT
    DEF CausalHistoryMetadata
<1>profiles. EarlierBarrierProfile(ancestry, commits, term, snapshot)
            /\ EarlierBarrierProfile(ancestry, commits, term, certificate.snapshot)
    BY <1>data, <1>covered, <1>campaign, CausalOpportunityHasEarlierBarrierProfile,
       CausalRetainedSnapshotHasEarlierBarrierProfile, SMT DEF RetainedCommitCertificate
<1>quorums.
        /\ ConfigOf(certificate.snapshot) \subseteq Server
        /\ ConfigOf(snapshot) \subseteq Server
        /\ certificate.election \in Quorums(ConfigOf(certificate.snapshot))
        /\ support \in Quorums(ConfigOf(snapshot))
    BY <1>data, SMT
    DEF OpportunityCertificate, RetainedCommitCertificate, RetainedElectionCertificate, LatestConfigurationOccurrence
<1> QED BY <1>pure, <1>profiles, <1>quorums, EarlierBarrierProfilesIntersect, Zenon

LEMMA CausalWitnessesDeriveOpportunityRelations ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE OpportunityRelations(voteHistory, ancestry, commits)
    BY CausalWitnessesSupplyOpportunityElectionIntersections, CausalWitnessesSupplyOpportunityRequestIntersections,
       CausalWitnessesSupplyOpportunityAncestryIntersections, CausalWitnessesSupplyOpportunityCommitIntersections,
       CausalWitnessesSupplyOpportunityCommitPrefixes, CausalWitnessesSupplyOpportunityEvidencePrefixes, SMT
    DEF OpportunityRelations

LEMMA OpportunityRelationsSupplyReady ==
    ASSUME NEW voteHistory, NEW ancestry, NEW commits, OpportunityRelations(voteHistory, ancestry, commits)
    PROVE ReadyMembershipRelations(voteHistory, ancestry, commits)
    BY ReadyCertificateUsesOpportunity, SMT
    DEF OpportunityRelations, ReadyMembershipRelations,
        OpportunityElectionIntersections, ReadyElectionIntersections,
        OpportunityRequestIntersections, ReadyRequestIntersections,
        OpportunityAncestryIntersections, ReadyAncestryIntersections,
        OpportunityCommitIntersections, ReadyCommitIntersections,
        OpportunityCommitPrefixes, ReadyCommitPrefixes,
        OpportunityEvidencePrefixes, ReadyEvidencePrefixes

LEMMA CausalWitnessesDeriveOpportunityWitnesses ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    PROVE JointOpportunityWitnesses(voteHistory, ancestry, commits)
    BY CausalWitnessesDeriveOpportunityRelations, OpportunityRelationsSupplyReady, SMT
    DEF JointOpportunityWitnesses, JointCandidateWitnesses

LEMMA ClientAppendExtendsConfigurationBarriers ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server,
           NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           fresh.prefix = log'[actor], fresh.owner = actor,
           fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
    PROVE ConfigurationBarrierAncestry(ancestry \cup {fresh}, commits)
<1>base. TypeOK /\ SendInvariant /\ ReplicationPrefixInv(voteHistory) /\ log[actor] \in Seq(LogEntry)
    BY JointCoreBase, SMT DEF MembershipJointCore, TypeOK, LogVarsTypeOK
<1>append. PICK entry \in LogEntry:
        /\ log'[actor] = Append(log[actor], entry) /\ entry.term = currentTerm[actor]
        /\ entry.members = payload.members
    BY <1>base, ClientRequestAppendsCurrentTerm, SMT
<1>fresh.
        /\ fresh.edge.entry = entry /\ fresh.edge.term = currentTerm[actor]
        /\ fresh.edge.index = Len(log[actor]) + 1
        /\ SubSeq(fresh.prefix, 1, fresh.edge.index - 1) = log[actor]
    BY <1>base, <1>append, AppendProperties, AppendPreservesSequencePrefix,
       WholeSequencePrefix, LenProperties, SMT DEF LogEntryEdge
<1>config. CASE payload.members # Nil
    <2>guard. CanReconfigure(actor, payload.members) /\ payload.members \in SUBSET Server
        BY <1>config, SMT DEF ClientRequest, CanReconfigure
    <2>barrier. PICK certificate \in commits: CurrentBarrierCertificate(voteHistory, actor, certificate)
        BY <1>base, <2>guard, CanReconfigureHasCurrentBarrierCertificate, SMT
        DEF JointMembershipWitnesses
    <2>match. ConfigurationBarrierFor(fresh, certificate)
        BY <1>base, <1>fresh, <1>config, <2>guard, <2>barrier,
           ConfigurationAppendHasEarlierCertifiedBarrier, LenProperties, SMT
        DEF CurrentBarrierCertificate, RetainedCommitCertificate, ConfigurationBarrierFor, IsPrefix,
            LatestConfigurationOccurrence
    <2> QED BY <2>barrier, <2>match, SMT
        DEF ConfigurationBarrierAncestry, JointMembershipWitnesses
<1>noConfig. CASE payload.members = Nil
    BY <1>noConfig, <1>append, <1>fresh, SMT
    DEF ConfigurationBarrierAncestry, JointMembershipWitnesses
<1> QED BY <1>config, <1>noConfig, SMT

LEMMA CurrentCertificateClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW leader \in Server,
           NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
<1>retained. RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
             <=> RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    BY ClientRequestKeepsSelectedCampaignHistory, ElectionCertificateMessagesFrame, SMT DEF ClientRequest
<1>frame.
    /\ UNCHANGED <<state, currentTerm>>
    /\ leader \in Server =>
           /\ currentTerm[leader] \in Nat
           /\ CampaignPrefix(log'[leader], currentTerm'[leader]) =
                   CampaignPrefix(log[leader], currentTerm[leader])
    BY ClientRequestPreservesCampaignPrefix, SMT DEF ClientRequest, TypeOK, ServerVarsTypeOK
<1> QED BY <1>retained, <1>frame, SMT
    DEF CurrentElectionCertificate, RetainedElectionCertificate

LEMMA ProtectedLeadersClientAppend ==
    ASSUME TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW target \in Seq(LogEntry), NEW term \in Nat,
           ProtectedLeaders(target, term)
    PROVE ProtectedLeaders(target, term)'
    BY ContinuingLeaderPrefixNext, SMT DEF ProtectedLeaders, ClientRequest, Next

LEMMA ProtectedVotersClientAppend ==
    ASSUME TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW target \in Seq(LogEntry)
    PROVE ProtectedVoters(target) \subseteq ProtectedVoters(target)'
    BY ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
    DEF ProtectedVoters, ClientRequest, TypeOK, LogVarsTypeOK

LEMMA LiveIntersectionsClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), LiveLeaderCertificateIntersections(voteHistory),
           CurrentRequestCertificateIntersections(voteHistory), NEW commits, CommitElectionIntersections(voteHistory, commits)
    PROVE /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
          /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
          /\ CommitElectionIntersections(nextVoteHistory, commits)'
<1>leaders. LiveLeaderCertificateIntersections(nextVoteHistory)'
    BY CurrentCertificateClientAppend, SMT DEF LiveLeaderCertificateIntersections
<1>requests. CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY CurrentCertificateClientAppend, ClientRequestKeepsSelectedCampaignHistory, ElectionCertificateMessagesFrame, SMT
    DEF CurrentRequestCertificateIntersections, AppendRequests, ClientRequest
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY CurrentCertificateClientAppend, SMT DEF CommitElectionIntersections, ClientRequest
<1> QED BY <1>leaders, <1>requests, <1>commits, SMT

\* Capture the actual appender and its current election certificate. The same
\* witness is then used throughout the joint post-state construction.
LEMMA ClientAppendCreatesJointWitness ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           CurrentElectionCertificate(voteHistory, actor, currentTerm[actor], snapshot, occurrence, support)
    PROVE \E fresh:
              /\ CertificateWitness(nextVoteHistory, fresh)'
              /\ fresh.prefix = log'[actor]
              /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
              /\ fresh.edge.index = Len(log[actor]) + 1
              /\ fresh.edge.term = currentTerm[actor]
              /\ fresh.owner = actor /\ fresh.support = support
<1>base.
        /\ TypeOK /\ SendInvariant /\ MembershipCampaignsInv(voteHistory)
        /\ LogStructureInv /\ LogTermsMonotonic /\ LogTermBoundInv
    BY JointCoreBase, LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, TermOrderingInv
<1>next. [Next]_vars BY SMT DEF Next
<1>term. PICK term \in Nat: term = currentTerm[actor]
    BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK
<1>entries. PICK entries \in Seq(LogEntry): entries = log'[actor]
    BY <1>base, ClientRequestLogTypeOK, SMT DEF LogVarsTypeOK
<1>append.
        /\ Len(entries) = Len(log[actor]) + 1
        /\ Len(entries) \in Nat \ {0}
        /\ entries[Len(entries)].term = term
    BY <1>base, <1>term, <1>entries, ClientRequestAppendsCurrentTerm,
       AppendProperties, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1>snapshot.
        /\ IsPrefix(snapshot, entries) /\ Len(snapshot) < Len(entries)
    BY <1>base, <1>entries, <1>append, ClientRequestCapturesElectionCertificate,
       CampaignPrefixProperties, PreTermIndexProperties, WholeSequencePrefix,
       ClientRequestAppendsCurrentTerm, PrefixOnAppend, LenProperties, SMT
    DEF CurrentElectionCertificate, IsPrefix, TypeOK, LogVarsTypeOK
<1>canonical. snapshot = CampaignPrefix(entries, term)
    BY <1>base, <1>term, <1>entries, ClientRequestPreservesCampaignPrefix, SMT
    DEF CurrentElectionCertificate, ClientRequest
<1>retained. RetainedElectionCertificate(nextVoteHistory, actor, term, snapshot, occurrence, support)'
    BY <1>base, <1>next, <1>term, CaptureCurrentElectionCertificate,
       RetainedElectionCertificateNext, SMT
<1>structure. TermsOrdered(entries) /\ EntryStructure(entries, term)
    BY <1>base, <1>term, <1>entries, ClientRequestPreservesLogTermsMonotonic,
       ClientRequestPreservesLogStructure, SMT
    DEF OrderingBase, LogTermsMonotonic, TermsOrdered, LogStructureInv, ClientRequest
<1>owner. OwnerPrefix(actor, term, entries)'
    BY <1>base, <1>term, <1>entries, WholeSequencePrefix, LenProperties, SMT
    DEF OwnerPrefix, ClientRequest, IsPrefix
<1> DEFINE fresh ==
        [edge |-> LogEntryEdge(entries, Len(entries)), prefix |-> entries,
         owner |-> actor, snapshot |-> snapshot, occurrence |-> occurrence, support |-> support]
<1>fields.
        /\ fresh.prefix = entries /\ fresh.edge.index = Len(entries)
        /\ fresh.edge.term = term /\ fresh.owner = actor
        /\ fresh.snapshot = snapshot /\ fresh.occurrence = occurrence /\ fresh.support = support
    BY <1>append, SMT DEF fresh, LogEntryEdge
<1>data. WitnessPrefixData(fresh)
    BY <1>term, <1>entries, <1>append, <1>snapshot, <1>canonical, <1>structure, <1>fields, SMT
    DEF WitnessPrefixData, fresh
<1>valid. CertificateWitness(nextVoteHistory, fresh)'
    BY <1>data, <1>fields, <1>retained, <1>owner, SMT DEF CertificateWitness
<1> QED BY <1>valid, <1>fields, <1>term, <1>entries, <1>append, SMT DEF fresh

LEMMA ClientAppendPreservesCommitProtection ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server,
           NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           fresh.prefix = log'[actor], fresh.edge.term = currentTerm[actor]
    PROVE /\ JointCommitProtection(ancestry \cup {fresh}, commits)'
          /\ CommitLeaderProtection(commits)'
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>commits. JointCommitProtection(ancestry \cup {fresh}, commits)'
    <2> SUFFICES ASSUME NEW certificate \in commits
                 PROVE /\ LaterTermPrefixProtection(ancestry \cup {fresh},
                                                     CommitTarget(certificate), certificate.term)'
                       /\ ProtectedAppendRequests(CommitTarget(certificate), certificate.term)'
                       /\ ProtectedLeaders(CommitTarget(certificate), certificate.term)'
                       /\ RecordedAcknowledgersProtected(certificate.leader, certificate.term,
                                                          CommitTarget(certificate))'
        BY SMT DEF JointCommitProtection
    <2>data. CommitTarget(certificate) \in Seq(LogEntry) /\ certificate.term \in Nat
        BY CommitCertificateTargetProperties, SMT
        DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
    <2>boundary. LaterTermPrefixProtection(ancestry \cup {fresh},
                                          CommitTarget(certificate), certificate.term)'
        BY <1>base, <2>data, ClientAppendPreservesLaterTermBoundary, SMT
        DEF JointMembershipWitnesses, JointCommitProtection
    <2>requests. ProtectedAppendRequests(CommitTarget(certificate), certificate.term)'
        BY SMT DEF JointMembershipWitnesses, JointCommitProtection,
            ProtectedAppendRequests, ClientRequest, AppendRequests
    <2>leaders. ProtectedLeaders(CommitTarget(certificate), certificate.term)'
        BY <1>base, <2>data, ProtectedLeadersClientAppend, SMT
        DEF JointMembershipWitnesses, JointCommitProtection
    <2>holders. RecordedAcknowledgersProtected(certificate.leader, certificate.term,
                                              CommitTarget(certificate))'
        BY <1>base, <2>data, ProtectedVotersClientAppend, SMT
        DEF JointMembershipWitnesses, JointCommitProtection, RecordedAcknowledgersProtected,
            RecordedReplicationSupport, RecordedAcknowledgment, ClientRequest
    <2> QED BY <2>boundary, <2>requests, <2>leaders, <2>holders, SMT
<1>leaders. CommitLeaderProtection(commits)'
    BY <1>base, CommitCertificateTargetProperties, ContinuingLeaderPrefixNext, SMT
    DEF JointMembershipWitnesses, CommitLeaderProtection, CommitCertificateFamily, ClientRequest, Next
<1> QED BY <1>commits, <1>leaders, SMT

LEMMA JointProtectionClientAppend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server,
           NEW payload \in ClientPayload, ClientRequest(actor, payload), ConfigOf(log'[actor]) # {actor}, NEW fresh,
           fresh.prefix = log'[actor], fresh.edge.term = currentTerm[actor]
    PROVE /\ JointCommitProtection(ancestry \cup {fresh}, commits)'
          /\ JointEvidenceProtection(nextVoteHistory, ancestry \cup {fresh})'
          /\ CommitLeaderProtection(commits)'
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
    BY ClientAppendPreservesEvidenceTargets, SMT DEF MembershipJointCore
<1>commits. JointCommitProtection(ancestry \cup {fresh}, commits)'
    <2> SUFFICES ASSUME NEW certificate \in commits
                 PROVE /\ LaterTermPrefixProtection(ancestry \cup {fresh},
                                                     CommitTarget(certificate), certificate.term)'
                       /\ ProtectedAppendRequests(CommitTarget(certificate), certificate.term)'
                       /\ ProtectedLeaders(CommitTarget(certificate), certificate.term)'
                       /\ RecordedAcknowledgersProtected(certificate.leader, certificate.term,
                                                          CommitTarget(certificate))'
        BY SMT DEF JointCommitProtection
    <2>data. CommitTarget(certificate) \in Seq(LogEntry) /\ certificate.term \in Nat
        BY CommitCertificateTargetProperties, SMT
        DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
    <2>boundary. LaterTermPrefixProtection(ancestry \cup {fresh},
                                          CommitTarget(certificate), certificate.term)'
        BY <1>base, <2>data, ClientAppendPreservesLaterTermBoundary, SMT
        DEF JointMembershipWitnesses, JointCommitProtection
    <2>requests. ProtectedAppendRequests(CommitTarget(certificate), certificate.term)'
        BY SMT DEF JointMembershipWitnesses, JointCommitProtection,
            ProtectedAppendRequests, ClientRequest, AppendRequests
    <2>leaders. ProtectedLeaders(CommitTarget(certificate), certificate.term)'
        BY <1>base, <2>data, ProtectedLeadersClientAppend, SMT
        DEF JointMembershipWitnesses, JointCommitProtection
    <2>holders. RecordedAcknowledgersProtected(certificate.leader, certificate.term,
                                              CommitTarget(certificate))'
        BY <1>base, <2>data, ProtectedVotersClientAppend, SMT
        DEF JointMembershipWitnesses, JointCommitProtection, RecordedAcknowledgersProtected,
            RecordedReplicationSupport, RecordedAcknowledgment, ClientRequest
    <2> QED BY <2>boundary, <2>requests, <2>leaders, <2>holders, SMT
<1>evidence. JointEvidenceProtection(nextVoteHistory, ancestry \cup {fresh})'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory)
                 PROVE /\ LaterTermPrefixProtection(ancestry \cup {fresh}, target, LastTerm(target))'
                       /\ ProtectedAppendRequests(target, LastTerm(target))'
                       /\ ProtectedLeaders(target, LastTerm(target))'
        BY <1>targets, SMT DEF JointEvidenceProtection
    <2>data. target \in Seq(LogEntry) /\ LastTerm(target) \in Nat
        BY LastTermTypeOK, SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>boundary. LaterTermPrefixProtection(ancestry \cup {fresh}, target, LastTerm(target))'
        BY <1>base, <2>data, ClientAppendPreservesLaterTermBoundary, SMT
        DEF JointMembershipWitnesses, JointEvidenceProtection
    <2>requests. ProtectedAppendRequests(target, LastTerm(target))'
        BY SMT DEF JointMembershipWitnesses, JointEvidenceProtection,
            ProtectedAppendRequests, ClientRequest, AppendRequests
    <2>leaders. ProtectedLeaders(target, LastTerm(target))'
        BY <1>base, <2>data, ProtectedLeadersClientAppend, SMT
        DEF JointMembershipWitnesses, JointEvidenceProtection
    <2> QED BY <2>boundary, <2>requests, <2>leaders, SMT
<1>leaders. CommitLeaderProtection(commits)'
    BY <1>base, CommitCertificateTargetProperties, ContinuingLeaderPrefixNext, SMT
    DEF JointMembershipWitnesses, CommitLeaderProtection, CommitCertificateFamily, ClientRequest, Next
<1> QED BY <1>commits, <1>evidence, <1>leaders, SMT

LEMMA ClientAppendExtendsJointData ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload)
    PROVE \E fresh:
        /\ CertificateWitness(nextVoteHistory, fresh)' /\ fresh.prefix = log'[actor]
        /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
        /\ fresh.edge.term = currentTerm[actor] /\ fresh.owner = actor
        /\ JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)' 
<1>base. TypeOK /\ SendInvariant /\ MembershipCampaignsInv(voteHistory) /\ ReplicationEvidenceInv(voteHistory) /\ EntryEdgeBase
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, actor, currentTerm[actor], snapshot, occurrence, support)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT DEF ClientRequest
<1>fresh. PICK fresh:
        /\ CertificateWitness(nextVoteHistory, fresh)'
        /\ fresh.prefix = log'[actor]
        /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
        /\ fresh.edge.index = Len(log[actor]) + 1
        /\ fresh.edge.term = currentTerm[actor]
        /\ fresh.owner = actor /\ fresh.support = support
    BY <1>campaign, ClientAppendCreatesJointWitness, SMT
<1>retained.
        /\ CertificateFamily(nextVoteHistory, ancestry)' /\ CommitCertificateFamily(nextVoteHistory, commits)'
        /\ RequestPrefixAncestry(nextVoteHistory, ancestry)'
    BY <1>base, <1>next, <1>old, CertificateFamilyNext,
       CommitCertificateFamilyNext, RequestPrefixAncestryNext, SMT DEF JointMembershipWitnesses
<1>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh.edge}
    BY <1>base, <1>fresh, ClientHistoricalEntryEdges, SMT
<1>coverage. CoversEntryEdges(ancestry \cup {fresh}, HistoricalEntryEdges')
    BY <1>old, <1>edges, SMT DEF JointMembershipWitnesses, CoversEntryEdges
<1>ancestors. \A index \in DOMAIN fresh.prefix:
        \E witness \in ancestry \cup {fresh}: witness.edge = LogEntryEdge(fresh.prefix, index)
    <2> SUFFICES ASSUME NEW index \in DOMAIN fresh.prefix
                 PROVE \E witness \in ancestry \cup {fresh}:
                           witness.edge = LogEntryEdge(fresh.prefix, index)
        BY SMT
    <2>edge. LogEntryEdge(fresh.prefix, index) \in HistoricalEntryEdges'
        BY <1>fresh, SMT DEF HistoricalEntryEdges
    <2> QED BY <1>coverage, <2>edge, SMT DEF CoversEntryEdges
<1>family. CertificateFamily(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>retained, <1>fresh, <1>ancestors, ExtendCertificateFamilyAfter, SMT
<1>order. TermPrefixOrder(ancestry \cup {fresh})'
    BY <1>base, <1>old, <1>campaign, <1>fresh, CurrentCertificateAdmitsOrderedPrefix, SMT
    DEF JointMembershipWitnesses, LiveAncestryCertificateIntersections,
        CurrentElectionCertificate, TypeOK, ServerVarsTypeOK
<1>requests. RequestPrefixAncestry(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>retained, SMT DEF RequestPrefixAncestry, AncestralRequestPrefix, CoveredPrefix
<1>live_old. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY <1>base, <1>old, CurrentCertificateClientAppend, SMT
    DEF JointMembershipWitnesses, LiveAncestryCertificateIntersections
<1>live_fresh.
    ASSUME NEW leader \in Server, NEW term \in Nat,
           NEW leaderSnapshot \in Seq(LogEntry), NEW leaderOccurrence, NEW leaderSupport,
           CurrentElectionCertificate(nextVoteHistory, leader, term, leaderSnapshot, leaderOccurrence, leaderSupport)',
           fresh.edge.term = term
    PROVE fresh.support \cap leaderSupport # {}
    <2> USE CurrentElectionCertificate(nextVoteHistory, leader, term, leaderSnapshot, leaderOccurrence, leaderSupport)',
            fresh.edge.term = term
    <2>before. CurrentElectionCertificate(voteHistory, leader, term, leaderSnapshot, leaderOccurrence, leaderSupport)
        BY <1>base, CurrentCertificateClientAppend, SMT
    <2>creator. CurrentElectionCertificate(voteHistory, actor, term, snapshot, occurrence, support)
        BY <1>campaign, <1>fresh, SMT
    <2> QED BY <1>campaign, <1>fresh, <2>before, <2>creator, SMT
        DEF MembershipJointCore, LiveLeaderCertificateIntersections
<1>live. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>live_old, <1>live_fresh, SMT DEF LiveAncestryCertificateIntersections
<1>metadata.
        /\ LocalCommitEvidence(commits)' /\ AdvertisedCommitEvidence(commits)'
        /\ CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>base, <1>old, LiveIntersectionsClientAppend, SMT
    DEF MembershipJointCore, JointMembershipWitnesses,
        LocalCommitEvidence, AdvertisedCommitEvidence, ClientRequest, AppendRequests
<1>protection.
        /\ JointCommitProtection(ancestry \cup {fresh}, commits)'
        /\ CommitLeaderProtection(commits)'
    BY <1>old, <1>fresh, ClientAppendPreservesCommitProtection, SMT
<1>barriers. ConfigurationBarrierAncestry(ancestry \cup {fresh}, commits)
    BY <1>old, <1>fresh, ClientAppendExtendsConfigurationBarriers, SMT
<1>witnesses. JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)'
    BY <1>family, <1>order, <1>coverage, <1>requests, <1>live,
       <1>retained, <1>metadata, <1>protection, <1>barriers, SMT DEF JointMembershipData
<1> QED BY <1>fresh, <1>witnesses, SMT

LEMMA ClientFutureCertificateContainsProtectedTarget ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)', CommitPrefixCoverage(ancestry \cup {fresh}, commits)',
           NEW initial, RetainedCommitCertificate(voteHistory, initial), CoveredPrefix(ancestry, initial.entries),
           initial.replication \subseteq ProtectedVoters(CommitTarget(initial)),
           LaterTermPrefixProtection(ancestry \cup {fresh}, CommitTarget(initial), initial.term)',
           NEW later \in Nat, currentTerm[actor] < later, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(nextVoteHistory, actor, later, snapshot, occurrence, support)'
    PROVE IsPrefix(CommitTarget(initial), log'[actor])
<1>next. [Next]_vars BY SMT DEF Next
<1>base. TypeOK /\ TypeOK' /\ SendInvariant' /\ PositiveVoteResponseRequestInv'
          /\ \A server \in Server: TermsOrdered(log'[server])
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>frame. AllLogsExtend /\ snapshot = log'[actor] /\ currentTerm'[actor] < later
    BY <1>base, ClientRequestAllLogsExtend, SMT DEF OpportunityCertificate, CampaignOpportunity, ClientRequest
<1>data. BarrierExclusionData(ancestry \cup {fresh}, commits)
    BY PostJointWitnessesSupplyBarrierExclusionData, SMT
<1>initial_data. CommitLogData(initial) /\ CommitTarget(initial) \in Seq(LogEntry)
    BY CommitCertificateTargetProperties, SMT DEF RetainedCommitCertificate, CommitLogData, CommitPrefixData
<1>subset. ancestry \subseteq ancestry \cup {fresh} BY SMT
<1>initial_covered. CoveredPrefix(ancestry \cup {fresh}, initial.entries)
    BY <1>subset, CoveredPrefixFamilyExtension, SMT
<1>initial_boundary. LaterTermPrefixProtection(ancestry \cup {fresh}, CommitTarget(initial), initial.term)
    BY SMT DEF LaterTermPrefixProtection
<1>initial_physical. initial.replication \subseteq ProtectedVoters(CommitTarget(initial))'
    BY <1>base, <1>frame, <1>initial_data, SequencePrefixTransitive, SMT
    DEF ProtectedVoters, AllLogsExtend, TypeOK, LogVarsTypeOK
<1>commit_physical. \A certificate \in commits:
        certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))'
    <2> SUFFICES ASSUME NEW certificate \in commits
                 PROVE certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))' BY SMT
    <2>before. CommitTarget(certificate) \in Seq(LogEntry)
               /\ certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
        BY RetainedCommitReplicasHoldTarget, SMT
    <2> QED BY <1>base, <1>frame, <2>before, SequencePrefixTransitive, SMT
        DEF ProtectedVoters, AllLogsExtend, TypeOK, LogVarsTypeOK
<1>covered. CoveredPrefix(ancestry \cup {fresh}, snapshot) /\ TermsOrdered(snapshot)
    <2>ordered. TermsOrdered(snapshot) BY <1>base, <1>frame, SMT
    <2>edges. CoversEntryEdges(ancestry \cup {fresh}, HistoricalEntryEdges)'
        BY SMT DEF JointMembershipData, JointMembershipWitnesses
    <2>covered. CoveredPrefix(ancestry \cup {fresh}, snapshot)
        <3> SUFFICES ASSUME NEW index \in DOMAIN snapshot
                     PROVE \E witness \in ancestry \cup {fresh}: witness.edge = LogEntryEdge(snapshot, index)
            BY SMT DEF CoveredPrefix
        <3>edge. LogEntryEdge(log'[actor], index) \in HistoricalEntryEdges'
            BY <1>frame, SMT DEF HistoricalEntryEdges, LogEntryEdge
        <3> QED BY <1>frame, <2>edges, <3>edge, SMT DEF CoversEntryEdges, LogEntryEdge
    <2> QED BY <2>ordered, <2>covered, SMT
<1> SUFFICES ASSUME ~IsPrefix(CommitTarget(initial), log'[actor]) PROVE FALSE BY SMT
<1>blocker. PICK blocker \in commits \cup {initial}:
        /\ CertificateBlocksConfiguration(blocker, ConfigOf(snapshot))
        /\ ~SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
    BY <1>frame, <1>data, <1>initial_data, <1>initial_covered, <1>initial_boundary, <1>covered,
       MissingProtectedTargetHasBlockingCertificate, SMT DEF BarrierExclusionData
<1>physical. CommitLogData(blocker) /\ blocker.replication \subseteq ProtectedVoters(CommitTarget(blocker))'
    BY <1>blocker, <1>initial_data, <1>data, <1>initial_physical, <1>commit_physical, SMT DEF BarrierExclusionData
<1> QED BY <1>base, <1>frame, <1>blocker, <1>physical, PostFutureCertificateCannotBeBlocked, SMT

LEMMA ClientFutureCertificateContainsAllCommitTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)', CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)',
           NEW later \in Nat, currentTerm[actor] < later, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(nextVoteHistory, actor, later, snapshot, occurrence, support)'
    PROVE \A certificate \in commits: IsPrefix(CommitTarget(certificate), log'[actor])
<1> SUFFICES ASSUME NEW certificate \in commits PROVE IsPrefix(CommitTarget(certificate), log'[actor]) BY SMT
<1>certificate. RetainedCommitCertificate(voteHistory, certificate) /\ CoveredPrefix(ancestry, certificate.entries)
    BY SMT DEF JointMembershipData, JointMembershipWitnesses, CommitCertificateFamily, CausalHistoryMetadata,
        CausalCampaignWitnesses, CommitPrefixCoverage
<1>physical. certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
    BY RetainedCommitReplicasHoldTarget, SMT
<1>boundary. LaterTermPrefixProtection(ancestry \cup {fresh}, CommitTarget(certificate), certificate.term)'
    BY SMT DEF JointMembershipData, JointMembershipWitnesses, JointCommitProtection
<1> QED BY <1>certificate, <1>physical, <1>boundary, ClientFutureCertificateContainsProtectedTarget, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses

LEMMA ClientFutureQuorumMeetsBarrierProtectedWord ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           fresh.prefix = log'[actor], JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)',
           CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)',
           NEW later \in Nat, currentTerm[actor] < later, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(nextVoteHistory, actor, later, snapshot, occurrence, support)',
           NEW entries, BarrierProtectedWord(ancestry, commits, entries), NEW votes \in Quorums(ConfigOf(entries))
    PROVE support \cap votes # {}
<1>data. BarrierExclusionData(ancestry \cup {fresh}, commits)
    BY PostJointWitnessesSupplyBarrierExclusionData, SMT
    DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>snapshot. snapshot = fresh.prefix /\ snapshot \in Seq(LogEntry) /\ TermsOrdered(snapshot)
              /\ CoveredPrefix(ancestry \cup {fresh}, snapshot)
    BY <1>data, SMT DEF OpportunityCertificate, CampaignOpportunity, ClientRequest,
        BarrierExclusionData, PrefixWitnessFamilyData, WitnessPrefixData, CoveredPrefix
<1>targets. \A certificate \in commits: IsPrefix(CommitTarget(certificate), snapshot)
    BY <1>snapshot, ClientFutureCertificateContainsAllCommitTargets, SMT
<1>subset. ancestry \subseteq ancestry \cup {fresh} BY SMT
<1>other. entries \in Seq(LogEntry) /\ TermsOrdered(entries) /\ CoveredPrefix(ancestry \cup {fresh}, entries)
          /\ \A certificate \in commits: IsPrefix(CommitTarget(certificate), entries)
    BY <1>subset, CoveredPrefixFamilyExtension, SMT DEF BarrierProtectedWord
<1>parents. \A certificate \in FamilyBarriers(PairAncestry(ancestry \cup {fresh}, snapshot, entries), commits):
        IsPrefix(CommitTarget(certificate), snapshot) /\ IsPrefix(CommitTarget(certificate), entries)
    BY <1>targets, <1>other, SMT DEF FamilyBarriers
<1>shape. EqualOrAdjacentConfigurations(ConfigOf(snapshot), ConfigOf(entries))
    BY <1>data, <1>snapshot, <1>other, <1>parents, PairedParentsSupplyEqualOrAdjacentConfigurations, SMT
    DEF BarrierExclusionData, CommitLogData
<1>quorum. support \in Quorums(ConfigOf(snapshot))
    BY SMT DEF OpportunityCertificate, LatestConfigurationOccurrence
<1>types. ConfigOf(snapshot) \subseteq Server /\ ConfigOf(entries) \subseteq Server
    BY <1>snapshot, <1>other, ConfigurationType, SMT
<1> QED BY <1>shape, <1>quorum, <1>types, EqualOrAdjacentQuorumsIntersect, SMT

LEMMA ClientFutureCertificateBoundsCommits ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload), NEW fresh,
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)', CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)',
           NEW later \in Nat, currentTerm[actor] < later, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(nextVoteHistory, actor, later, snapshot, occurrence, support)'
    PROVE \A certificate \in commits: certificate.term <= currentTerm[actor]
<1>next. [Next]_vars BY SMT DEF Next
<1>base. TypeOK /\ TypeOK' /\ log[actor] \in Seq(LogEntry)
          /\ TermsOrdered(log'[actor])
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered, TypeOK, LogVarsTypeOK
<1>entry. PICK entry \in LogEntry: log'[actor] = Append(log[actor], entry) /\ entry.term = currentTerm[actor]
    BY <1>base, ClientRequestAppendsCurrentTerm, SMT
<1>last. LastTerm(log'[actor]) = currentTerm[actor] /\ log'[actor] \in Seq(LogEntry) /\ TermsOrdered(log'[actor])
    BY <1>base, <1>entry, AppendLastTerm, SMT DEF TypeOK, LogVarsTypeOK
<1>targets. \A certificate \in commits: IsPrefix(CommitTarget(certificate), log'[actor])
    BY ClientFutureCertificateContainsAllCommitTargets, SMT
<1> SUFFICES ASSUME NEW certificate \in commits PROVE certificate.term <= currentTerm[actor] BY SMT
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
    BY RetainedCommitReplicasHoldTarget, SMT
<1> QED BY <1>last, <1>targets, <1>target, OrderedPrefixLastTermBound, SMT

\* An append send adds a request, without adding a vote or acknowledgment.
LEMMA AppendSendElectionCertificatesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, NEW peer \in Server, AppendEntries(actor, peer),
           NEW leader, NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE /\ (CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
              <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support))
          /\ (RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
              <=> RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support))
    BY UnchangedLogsAndTermsKeepSelectedHistory, MessageTypesDistinct, SMT
    DEF CurrentElectionCertificate, RetainedElectionCertificate, RecordedCampaignRequests,
        VoteSupport, VoteFor, Grant, Started, AppendEntries, AppendEntriesMessage,
        Send, WithMessage, WithMessages, CampaignHistoryContextStep, HistoryCampaignSnapshot

LEMMA AppendSendRecordedAcknowledgmentsFrame ==
    ASSUME NEW actor \in Server, NEW peer \in Server, AppendEntries(actor, peer),
           NEW voter, NEW leader, NEW term, NEW index
    PROVE RecordedAcknowledgment(voter, leader, term, index)'
          <=> RecordedAcknowledgment(voter, leader, term, index)
    BY MessageTypesDistinct, SMT
    DEF RecordedAcknowledgment, SuccessfulAppendResponse, AppendEntries, AppendEntriesMessage,
        Send, WithMessage, WithMessages

\* A new request cannot make a retained response certify a new present target.
\* If the request is new, its owner is the current sender, whose old response
\* already justifies the corresponding physical prefix.
LEMMA PrefixAcknowledgmentBeforeAppendSend ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW peer \in Server,
           AppendEntries(actor, peer), NEW voter \in Server, NEW leader \in Server,
           NEW term \in Nat, NEW target \in Seq(LogEntry), IsPrefix(target, log[leader]),
           RecordedPrefixAcknowledgment(voter, leader, term, target)'
    PROVE RecordedPrefixAcknowledgment(voter, leader, term, target)
<1>frozen. PICK response, request, prefix:
        /\ response \in messages' /\ request \in messages' /\ prefix \in Seq(LogEntry)
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = voter /\ response.mdest = leader
        /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        /\ ResponseMatchesRequest(response, request)
        /\ RequestPrefixData(request, prefix) /\ OwnerPrefix(leader, term, prefix)'
        /\ IsPrefix(target, prefix)
    BY SMT DEF RecordedPrefixAcknowledgment
<1>response. response \in messages
    BY <1>frozen, MessageTypesDistinct, SMT
    DEF SuccessfulAppendResponse, AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages
<1>old. CASE request \in messages
    BY <1>frozen, <1>response, <1>old, SMT
    DEF RecordedPrefixAcknowledgment, OwnerPrefix, AppendEntries
<1>new. CASE request \notin messages
    <2>sender. leader = actor /\ term = currentTerm[actor]
        BY <1>frozen, <1>new, SMT
        DEF ResponseMatchesRequest, AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages
    <2>numeric. RecordedAcknowledgment(voter, leader, term, Len(target))
        BY <1>frozen, <1>response, SMT DEF RecordedAcknowledgment
    <2> QED BY <2>sender, <2>numeric, CurrentRecordedAcknowledgmentCoversPrefix, SMT
        DEF AppendEntries
<1> QED BY <1>old, <1>new, SMT

LEMMA PresentCommitCertificateBeforeAppendSend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW peer \in Server,
           AppendEntries(actor, peer), NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)',
           certificate.index = Len(certificate.entries),
           IsPrefix(certificate.entries, log'[certificate.leader])
    PROVE RetainedCommitCertificate(voteHistory, certificate)
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>election. RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
        certificate.snapshot, certificate.electionOccurrence, certificate.election)
    BY AppendSendElectionCertificatesFrame, CampaignsSupplyEntryBounds, SMT
    DEF RetainedCommitCertificate, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>target. CommitTarget(certificate) = certificate.entries
    BY <1>data, WholeSequencePrefix, SMT DEF CommitTarget
<1>acks. \A voter \in certificate.replication \ {certificate.leader}:
        RecordedPrefixAcknowledgment(voter, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>data, <1>target, PrefixAcknowledgmentBeforeAppendSend, SMT
    DEF RetainedCommitCertificate, AppendEntries, Quorums
<1> QED BY <1>election, <1>acks, UnchangedLogsAndTermsKeepSelectedHistory, CampaignsSupplyEntryBounds, SMT
    DEF RetainedCommitCertificate, OwnerPrefix, AppendEntries, ReplicationPrefixInv,
        ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase

LEMMA AppendSendPreservesEvidenceTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), NEW actor \in Server, NEW peer \in Server,
           AppendEntries(actor, peer)
    PROVE EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
<1>base. TypeOK /\ SendInvariant
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>next. [Next]_vars BY SMT DEF Next
<1>forward. EvidenceAgreementTargets(voteHistory) \subseteq EvidenceAgreementTargets(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory) PROVE target \in EvidenceAgreementTargets(nextVoteHistory)'
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(voteHistory, certificate)
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>retained. RetainedCommitCertificate(nextVoteHistory, certificate)'
        BY <1>base, <1>next, <2>certificate, RetainedCommitCertificateNext, SMT
    <2> QED BY <2>certificate, <2>retained, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, AppendEntries
<1>reverse. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory)
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)' PROVE target \in EvidenceAgreementTargets(voteHistory)
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log'[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>before. RetainedCommitCertificate(voteHistory, certificate)
        BY <2>certificate, PresentCommitCertificateBeforeAppendSend, SMT
    <2> QED BY <2>certificate, <2>before, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, AppendEntries
<1> QED BY <1>forward, <1>reverse, SMT

LEMMA AppendSendPreservesRequestCertificateIntersections ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW actor \in Server, NEW peer \in Server, AppendEntries(actor, peer)
    PROVE CurrentRequestCertificateIntersections(nextVoteHistory)'
<1>base. MembershipCampaignsInv(voteHistory) /\ currentTerm \in [Server -> Nat]
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>safety. MembershipElectionSafety /\ CurrentRequestSendersUnique
    BY <1>base, JointCoreImpliesElectionSafety, IntersectingRequestCertificatesIdentifySenders, SMT
    DEF MembershipJointCore
<1> SUFFICES ASSUME NEW leader \in Server, NEW request \in AppendRequests',
                      state'[leader] = Leader, request.mterm = currentTerm'[leader]
             PROVE \E leaderSnapshot, requestSnapshot \in Seq(LogEntry):
                   \E leaderOccurrence, requestOccurrence, leaderSupport, requestSupport:
                       /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm,
                               leaderSnapshot, leaderOccurrence, leaderSupport)'
                       /\ RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                               requestSnapshot, requestOccurrence, requestSupport)'
                       /\ leaderSupport \cap requestSupport # {}
    BY SMT DEF CurrentRequestCertificateIntersections
<1>owner. request.msource = leader
    <2>old. CASE request \in messages
        BY <1>safety, <2>old, SMT DEF CurrentRequestSendersUnique, AppendRequests, AppendEntries
    <2>new. CASE request \notin messages
        BY <1>safety, <2>new, SMT
        DEF MembershipElectionSafety, AppendRequests, AppendEntries, AppendEntriesMessage,
            Send, WithMessage, WithMessages
    <2> QED BY <2>old, <2>new, SMT
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, request.mterm, snapshot, occurrence, support)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT DEF AppendEntries
<1>after.
        /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm, snapshot, occurrence, support)'
        /\ RetainedElectionCertificate(nextVoteHistory, leader, request.mterm, snapshot, occurrence, support)'
    BY <1>base, <1>campaign, JointCoreBase, AppendSendElectionCertificatesFrame, CaptureCurrentElectionCertificate, SMT
    DEF AppendEntries, MembershipJointCore, EntryEdgeBase
<1>nonempty. support # {}
    BY <1>campaign, ConfigurationQuorumNonempty, SMT DEF CurrentElectionCertificate
<1> QED BY <1>owner, <1>campaign, <1>after, <1>nonempty, SMT

LEMMA JointProtectionAppendSend ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server,
           NEW peer \in Server, AppendEntries(actor, peer)
    PROVE /\ JointCommitProtection(ancestry, commits)'
          /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
          /\ CommitLeaderProtection(commits)'
<1>base. EntryEdgeBase /\ TypeOK
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
    BY AppendSendPreservesEvidenceTargets, SMT DEF MembershipJointCore
<1>commits. JointCommitProtection(ancestry, commits)'
    BY <1>base, <1>next, CommitCertificateTargetProperties, ProtectedAppendRequestsNext,
       AppendSendRecordedAcknowledgmentsFrame, SMT
    DEF JointMembershipWitnesses, JointCommitProtection, CommitCertificateFamily,
        RetainedCommitCertificate, ProtectedLeaders, RecordedAcknowledgersProtected,
        RecordedReplicationSupport, ProtectedVoters, AppendEntries
<1>evidence. JointEvidenceProtection(nextVoteHistory, ancestry)'
    BY <1>base, <1>next, <1>targets, LastTermTypeOK, ProtectedAppendRequestsNext, SMT
    DEF JointMembershipWitnesses, JointEvidenceProtection, EvidenceAgreementTargets,
        SupportedAgreementTarget, ProtectedLeaders, AppendEntries
<1>leaders. CommitLeaderProtection(commits)'
    BY SMT DEF JointMembershipWitnesses, CommitLeaderProtection, AppendEntries
<1> QED BY <1>commits, <1>evidence, <1>leaders, SMT

\* Self-only replication admits the new full prefix immediately. The barrier
\* argument below therefore precedes assembly of agreement protection.
LEMMA SingletonClientHasFutureSelfCertificate ==
    ASSUME TypeOK, NEW voteHistory, NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), ConfigOf(log'[actor]) = {actor},
           NEW entries \in Seq(LogEntry), entries = log'[actor],
           NEW later \in Nat, currentTerm[actor] < later
    PROVE OpportunityCertificate(voteHistory, actor, later, entries, LatestConfigurationOccurrence(entries), {actor})'
BY FS_Singleton, NonemptyFiniteSetIsQuorum, SMT
DEF OpportunityCertificate, CampaignOpportunity, OpportunityVoters, LatestConfigurationOccurrence, ClientRequest

LEMMA SingletonClientBoundsCapturedCampaigns ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload),
           ConfigOf(log'[actor]) = {actor}, NEW fresh, fresh.prefix = log'[actor],
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)',
           CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
    PROVE \A campaign \in campaigns: campaign.term <= currentTerm[actor]
<1>base. TypeOK /\ SendInvariant /\ currentTerm[actor] \in Nat
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>entries. PICK entries \in Seq(LogEntry): entries = log'[actor]
    BY <1>base, ClientRequestLogTypeOK, SMT DEF LogVarsTypeOK
<1>later. PICK later \in Nat: later = currentTerm[actor] + 1
    BY <1>base, SMT
<1>future. OpportunityCertificate(nextVoteHistory, actor, later, entries, LatestConfigurationOccurrence(entries), {actor})'
    BY <1>base, <1>entries, <1>later, SingletonClientHasFutureSelfCertificate, SMT
<1>bounds. \A certificate \in commits: certificate.term <= currentTerm[actor]
    BY <1>base, <1>entries, <1>later, <1>future, ClientFutureCertificateBoundsCommits, SMT
<1> SUFFICES ASSUME NEW campaign \in campaigns, currentTerm[actor] < campaign.term PROVE FALSE
    BY <1>base, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CausalCampaignData
<1>data. CausalCampaignData(voteHistory, ancestry, campaign)
    BY SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses
<1>word. BarrierProtectedWord(ancestry, commits, campaign.snapshot)
    <2>snapshot.
            /\ campaign.snapshot \in Seq(LogEntry) /\ TermsOrdered(campaign.snapshot)
            /\ CoveredPrefix(ancestry, campaign.snapshot)
        BY <1>data, SMT DEF CausalCampaignData
    <2>prefixes. \A certificate \in commits: IsPrefix(CommitTarget(certificate), campaign.snapshot)
        <3> SUFFICES ASSUME NEW certificate \in commits
                     PROVE IsPrefix(CommitTarget(certificate), campaign.snapshot) BY SMT
        <3>epoch. certificate.term \in Nat /\ certificate.term <= currentTerm[actor]
            BY <1>bounds, SMT DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
        <3>earlier. certificate.term < campaign.term
            BY <1>base, <1>data, <3>epoch, SMT DEF CausalCampaignData
        <3> QED BY <3>earlier, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CampaignCommitPrefixes
    <2> QED BY <2>snapshot, <2>prefixes, SMT DEF BarrierProtectedWord
<1>quorum. campaign.support \in Quorums(ConfigOf(campaign.snapshot))
    BY <1>data, SMT DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, LatestConfigurationOccurrence
<1>intersection. {actor} \cap campaign.support # {}
    BY <1>base, <1>entries, <1>later, <1>future, <1>data, <1>word, <1>quorum,
       ClientFutureQuorumMeetsBarrierProtectedWord, SMT DEF CausalCampaignData
<1>vote. RecordedCampaignVote(voteHistory, actor, campaign.candidate, campaign.term)
    BY <1>data, <1>intersection, SMT
    DEF CausalCampaignData, CausalElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
<1> QED BY <1>base, <1>data, <1>vote, RecordedCampaignVoteTermBound, SMT DEF CausalCampaignData

LEMMA SingletonClientClosesJointWitnesses ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW campaigns, CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload),
           ConfigOf(log'[actor]) = {actor}, NEW fresh,
           fresh.prefix = log'[actor], fresh.edge.term = currentTerm[actor],
           JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)',
           CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
    PROVE JointMembershipWitnesses(nextVoteHistory, ancestry \cup {fresh}, commits)'
<1>base. TypeOK /\ SendInvariant /\ currentTerm[actor] \in Nat
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>term. PICK term \in Nat: term = currentTerm[actor] BY <1>base, SMT
<1>entries. PICK entries \in Seq(LogEntry): entries = log'[actor]
    BY <1>base, ClientRequestLogTypeOK, SMT DEF LogVarsTypeOK
<1>campaigns. \A campaign \in campaigns: campaign.term <= term
    BY <1>term, SingletonClientBoundsCapturedCampaigns, SMT
<1>ancestry. \A witness \in ancestry: witness.edge.term <= term
    BY <1>campaigns, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, CreatorCampaignCoverage
<1>requests. \A request \in AppendRequests: request.mterm <= term
    BY <1>campaigns, SMT DEF CausalHistoryMetadata, CausalCampaignWitnesses, RequestCampaignCoverage
<1>leader_bounds. \A leader \in Server: state[leader] = Leader => currentTerm[leader] <= term
    BY <1>campaigns, SMT DEF CausalHistoryMetadata, CurrentCausalCampaigns
<1>fresh_boundary. LaterTermPrefixProtection(ancestry \cup {fresh}, entries, term)'
    BY <1>ancestry, <1>term, SMT
    DEF LaterTermPrefixProtection, JointMembershipWitnesses, CertificateFamily, CertificateWitness, WitnessPrefixData
<1>fresh_requests. ProtectedAppendRequests(entries, term)'
    <2> SUFFICES ASSUME NEW request \in AppendRequests', request.mterm >= term
                 PROVE RequestRespectsPrefix(request, entries)
        BY SMT DEF ProtectedAppendRequests
    <2>same. request \in AppendRequests /\ request.mterm = currentTerm[actor]
        <3>retained. request \in AppendRequests BY SMT DEF ClientRequest, AppendRequests
        <3>fields. request.mterm \in Nat
            BY <1>base, <3>retained, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
        <3>bound. request.mterm <= term BY <1>requests, <3>retained, SMT
        <3> QED BY <1>term, <3>retained, <3>fields, <3>bound, SMT
    <2>sent. PICK sent \in Seq(LogEntry): RequestPrefixData(request, sent) /\ CoveredPrefix(ancestry, sent)
        BY <2>same, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
    <2>held. IsPrefix(sent, log[actor])
        BY <2>same, <2>sent, CurrentRequestCoveredPrefixBelongsToLeader, SMT DEF ClientRequest
    <2>append. IsPrefix(log[actor], entries)
        BY <1>base, <1>entries, ClientRequestAppendsCurrentTerm, PrefixOnAppend, WholeSequencePrefix, LenProperties, SMT
        DEF TypeOK, LogVarsTypeOK, IsPrefix
    <2>inside. IsPrefix(sent, entries)
        BY <1>base, <1>entries, <2>sent, <2>held, <2>append, SequencePrefixTransitive, SMT
        DEF TypeOK, LogVarsTypeOK
    <2>types. request.mentries \in Seq(LogEntry)
        BY <1>base, <2>same, MessageFieldsTypeOK, Zenon DEF AppendRequests, TypeOK, MsgTypeOK
    <2>self. IsPrefix(entries, entries)
        BY <1>entries, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
    <2> QED BY <1>entries, <2>sent, <2>inside, <2>types, <2>self,
        ComparableRequestPrefixRespectsTarget, SMT
<1>fresh_leaders. ProtectedLeaders(entries, term)'
    <2> SUFFICES ASSUME NEW leader \in Server, state'[leader] = Leader, currentTerm'[leader] >= term
                 PROVE IsPrefix(entries, log'[leader])
        BY SMT DEF ProtectedLeaders
    <2>epoch. state[leader] = Leader /\ currentTerm[leader] = currentTerm[actor]
        BY <1>base, <1>term, <1>leader_bounds, SMT DEF ClientRequest, TypeOK, ServerVarsTypeOK
    <2>owner. leader = actor
        BY <2>epoch, JointCoreImpliesElectionSafety, SMT DEF MembershipElectionSafety, ClientRequest
    <2> QED BY <1>entries, <2>owner, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
<1>old. \A target \in EvidenceAgreementTargets(voteHistory):
        /\ LaterTermPrefixProtection(ancestry \cup {fresh}, target, LastTerm(target))'
        /\ ProtectedAppendRequests(target, LastTerm(target))'
        /\ ProtectedLeaders(target, LastTerm(target))'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory)
                 PROVE /\ LaterTermPrefixProtection(ancestry \cup {fresh}, target, LastTerm(target))'
                       /\ ProtectedAppendRequests(target, LastTerm(target))'
                       /\ ProtectedLeaders(target, LastTerm(target))'
        BY SMT
    <2>data. target \in Seq(LogEntry) /\ LastTerm(target) \in Nat
        BY LastTermTypeOK, SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>boundary. LaterTermPrefixProtection(ancestry \cup {fresh}, target, LastTerm(target))'
        BY <1>base, <2>data, ClientAppendPreservesLaterTermBoundary, SMT
        DEF JointMembershipWitnesses, JointEvidenceProtection, LaterTermPrefixProtection
    <2>requests. ProtectedAppendRequests(target, LastTerm(target))'
        BY SMT DEF JointMembershipWitnesses, JointEvidenceProtection, ProtectedAppendRequests, AppendRequests, ClientRequest
    <2>leaders. ProtectedLeaders(target, LastTerm(target))'
        BY <1>base, <2>data, ProtectedLeadersClientAppend, SMT DEF JointMembershipWitnesses, JointEvidenceProtection
    <2> QED BY <2>boundary, <2>requests, <2>leaders, SMT
<1>last. LastTerm(entries) = term
    BY <1>base, <1>term, <1>entries, ClientRequestAppendsCurrentTerm, AppendLastTerm, SMT DEF TypeOK, LogVarsTypeOK
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory) \cup {entries}
    BY <1>entries, ClientAppendEvidenceTargets, SMT DEF MembershipJointCore
<1>protection. JointEvidenceProtection(nextVoteHistory, ancestry \cup {fresh})'
    BY <1>old, <1>last, <1>targets, <1>fresh_boundary, <1>fresh_requests, <1>fresh_leaders, SMT
    DEF JointEvidenceProtection
<1> QED BY <1>protection, SMT DEF JointMembershipWitnesses, JointMembershipData

LEMMA JointHistoryStepBase ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars
    PROVE /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
          /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointInv, MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, EntryEdgeBase

LEMMA JointAcknowledgmentHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars,
           NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits)
    PROVE AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
<1>base.
    /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
    /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1> QED BY <1>base, AcknowledgmentPrefixHistoryNext,
    AcknowledgmentVoteCutHistoryNext, SMT DEF MembershipJointInv

\* These actions keep the chosen ancestry, commit certificates, and campaigns.
LEMMA MembershipHistoryWithoutAdmission ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars,
           NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits),
           CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           CandidateRetirementAction \/ (\E actor \in Server: Timeout(actor))
               \/ (\E actor, peer \in Server: AppendEntries(actor, peer))
    PROVE /\ MembershipJointInv(nextVoteHistory)'
          /\ JointMembershipWitnesses(nextVoteHistory, ancestry, commits)'
          /\ CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>retirement. CandidateRetirementAction => JointRetirementFrame
    BY <1>base, CandidateRetirementFrames, SMT
<1>frame. ContinuingLeadersKeepLogs
    BY <1>base, <1>retirement, ServerStatesDistinct, SMT
    DEF JointRetirementFrame, ContinuingLeadersKeepLogs, Timeout, AppendEntries, TypeOK, ServerVarsTypeOK
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
    <2>excluded. /\ ~(\E actor \in Server: BecomeLeader(actor))
                 /\ ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
        BY <1>base, <1>frame, ContinuingLeadersExcludeClientAppend, ServerStatesDistinct, SMT
        DEF ContinuingLeadersKeepLogs, BecomeLeader, TypeOK, ServerVarsTypeOK
    <2> QED BY <1>base, <2>excluded, CausalMetadataWithoutPromotion, SMT
<1>witnesses.
        /\ JointMembershipWitnesses(nextVoteHistory, ancestry, commits)'
        /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
        /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
    <2>retire. CASE CandidateRetirementAction
        BY <1>base, <1>retirement, <2>retire, JointWitnessesRetirementFrame, LiveIntersectionsRetirementFrame, SMT
        DEF MembershipJointCore, JointMembershipWitnesses
    <2>send. CASE (\E actor \in Server: Timeout(actor)) \/ (\E actor, peer \in Server: AppendEntries(actor, peer))
        <3>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges
            BY <1>base, <2>send, TimeoutAppendEvidenceFrame, EntryEdgeAppendSendSubset, SMT
            DEF HistoricalEntryEdges, Timeout
        <3>metadata. JointWitnessMetadata(nextVoteHistory, ancestry, commits)'
            BY <1>base, <2>send, <3>edges, JointMetadataWithoutNewCommit, SMT DEF Timeout, AppendEntries
        <3>live.
                /\ LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
                /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)' /\ CommitElectionIntersections(nextVoteHistory, commits)'
            BY <1>base, <2>send, LiveIntersectionsTimeout, AppendSendElectionCertificatesFrame,
               AppendSendPreservesRequestCertificateIntersections, SMT
            DEF MembershipJointCore, JointMembershipWitnesses, LiveLeaderCertificateIntersections,
                LiveAncestryCertificateIntersections, CommitElectionIntersections, AppendEntries
        <3>protection.
                /\ JointCommitProtection(ancestry, commits)' /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
                /\ CommitLeaderProtection(commits)'
            BY <1>base, <2>send, JointProtectionTimeout, JointProtectionAppendSend, SMT
        <3> QED BY <3>metadata, <3>live, <3>protection, SMT DEF JointMembershipWitnesses, JointWitnessMetadata
    <2> QED BY <2>retire, <2>send, SMT
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>ack. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1> QED BY <1>witnesses, <1>causal, <1>ack, <1>structural, SMT
    DEF MembershipJointInv, MembershipJointCore

LEMMA MembershipHistoryPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, BecomeLeader(actor)
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>selected. JointOpportunityWitnesses(voteHistory, ancestry, commits)
                /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    BY CausalWitnessesDeriveOpportunityWitnesses, SMT DEF MembershipJointInv
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>live.
        /\ LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
        /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)' /\ CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>base, <1>selected, PromotionAdmitsLiveRelations, SMT DEF JointOpportunityWitnesses
<1>metadata. JointWitnessMetadata(nextVoteHistory, ancestry, commits)'
    BY <1>base, JointMetadataWithoutNewCommit, SMT DEF HistoricalEntryEdges, AppendRequests, BecomeLeader
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
    BY <1>base, ConfigurationEvidenceUnchangedWithLogsAndMessages, SMT DEF MembershipJointCore, BecomeLeader
<1>protection. JointCommitProtection(ancestry, commits)' /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
               /\ CommitLeaderProtection(commits)'
    BY <1>base, <1>selected, <1>targets, PromotionPreservesReadyPrefixes, SMT
    DEF JointOpportunityWitnesses, JointCandidateWitnesses, JointMembershipWitnesses,
        JointCommitProtection, JointEvidenceProtection, ProtectedAppendRequests, AppendRequests,
        RecordedAcknowledgersProtected, RecordedReplicationSupport, RecordedAcknowledgment, ProtectedVoters, BecomeLeader
<1>witnesses. JointMembershipWitnesses(nextVoteHistory, ancestry, commits)'
    BY <1>metadata, <1>live, <1>protection, SMT DEF JointMembershipWitnesses, JointWitnessMetadata
<1>causal. PICK fresh: CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns \cup {fresh})'
    BY <1>base, <1>selected, CausalMetadataPromotion, SMT
<1> QED BY <1>acknowledgment_history, <1>structural, <1>live, <1>witnesses, <1>causal, SMT
    DEF MembershipJointInv, MembershipJointCore

LEMMA MembershipHistoryClient ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload) /\ ConfigOf(log'[actor]) # {actor}
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>fresh. PICK fresh:
        /\ CertificateWitness(nextVoteHistory, fresh)' /\ fresh.prefix = log'[actor]
        /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
        /\ fresh.edge.term = currentTerm[actor] /\ fresh.owner = actor
        /\ JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)'
    BY <1>base, ClientAppendExtendsJointData, SMT
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
    BY <1>base, <1>fresh, CausalMetadataClientAppend, SMT
<1>witnesses. JointMembershipWitnesses(nextVoteHistory, ancestry \cup {fresh}, commits)'
    BY <1>base, <1>fresh, JointProtectionClientAppend, SMT
    DEF JointMembershipData, JointMembershipWitnesses
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>live. LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY <1>base, LiveIntersectionsClientAppend, SMT DEF MembershipJointCore, JointMembershipWitnesses
<1> QED BY <1>acknowledgment_history, <1>witnesses, <1>causal, <1>structural, <1>live, SMT
    DEF MembershipJointInv, MembershipJointCore

LEMMA MembershipHistorySingletonClient ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload) /\ ConfigOf(log'[actor]) = {actor}
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>selected. JointOpportunityWitnesses(voteHistory, ancestry, commits)
                /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    BY CausalWitnessesDeriveOpportunityWitnesses, SMT DEF MembershipJointInv
<1>chosen. JointCandidateWitnesses(voteHistory, ancestry, commits)
    BY <1>selected, SMT DEF JointOpportunityWitnesses
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY <1>chosen, SMT DEF JointCandidateWitnesses
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>fresh. PICK fresh:
    /\ CertificateWitness(nextVoteHistory, fresh)' /\ fresh.prefix = log'[actor]
    /\ fresh.edge = LogEntryEdge(log'[actor], Len(log[actor]) + 1)
    /\ fresh.edge.term = currentTerm[actor] /\ fresh.owner = actor
    /\ JointMembershipData(nextVoteHistory, ancestry \cup {fresh}, commits)'
    BY <1>base, <1>old, ClientAppendExtendsJointData, SMT
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry \cup {fresh}, commits, campaigns)'
    BY <1>base, <1>old, <1>selected, <1>fresh, CausalMetadataClientAppend, SMT
<1>witnesses. JointMembershipWitnesses(nextVoteHistory, ancestry \cup {fresh}, commits)'
    BY <1>base, <1>old, <1>selected, <1>fresh, <1>causal, SingletonClientClosesJointWitnesses, SMT
<1>intersections. LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY <1>base, <1>old, LiveIntersectionsClientAppend, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1> QED BY <1>structural, <1>acknowledgment_history,
    <1>witnesses, <1>causal, <1>intersections, SMT DEF MembershipJointInv, MembershipJointCore

LEMMA MembershipHistoryCommit ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW actor \in Server, AdvanceCommitIndex(actor) /\ commitIndex'[actor] > commitIndex[actor]
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>selected. JointOpportunityWitnesses(voteHistory, ancestry, commits)
                /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    BY CausalWitnessesDeriveOpportunityWitnesses, SMT DEF MembershipJointInv
<1>pending_derived. JointPendingProtection(voteHistory, ancestry)
    BY <1>base, <1>selected, CausalWitnessesSupplyPendingProtection, SMT
    DEF MembershipJointInv, CausalHistoryMetadata
<1>commit_base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ SendInvariant /\ TypeOK' /\ NextIndexBound
        /\ ReplicationEvidenceInv(voteHistory)
        /\ ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>old.
        /\ JointCandidateWitnesses(voteHistory, ancestry, commits)
        /\ JointMembershipWitnesses(voteHistory, ancestry, commits) /\ OpportunityRelations(voteHistory, ancestry, commits)
        /\ JointPendingProtection(voteHistory, ancestry)
    BY <1>selected, <1>pending_derived, SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses
<1>fresh. PICK fresh:
        /\ RetainedCommitCertificate(nextVoteHistory, fresh)'
        /\ fresh.leader = actor /\ fresh.term = currentTerm[actor]
        /\ fresh.entries = log[actor] /\ fresh.index = commitIndex'[actor]
    BY <1>commit_base, ChangedCommitIndexCapturesCertificate, SMT DEF MembershipJointCore
<1>before. RetainedCommitCertificate(voteHistory, fresh)
    BY <1>commit_base, <1>fresh, CommitCertificateStateFrame, SMT DEF AdvanceCommitIndex
<1>pending. PendingAgreement(actor, fresh.term, CommitTarget(fresh))
    BY <1>fresh, <1>before, OwnedCommitCertificateIsPending, SMT DEF AdvanceCommitIndex
<1>target_protection. PendingTargetProtection(nextVoteHistory, ancestry, actor, fresh.term, CommitTarget(fresh))'
    BY <1>commit_base, <1>old, <1>fresh, <1>before, <1>pending, CommitCertificateTargetProperties,
       PendingTargetCommitAdvanceFrame, SMT
    DEF JointPendingProtection, RetainedCommitCertificate
<1>retained.
        /\ CertificateFamily(nextVoteHistory, ancestry)' /\ RequestPrefixAncestry(nextVoteHistory, ancestry)'
        /\ CommitCertificateFamily(nextVoteHistory, commits)' /\ AdvertisedCommitEvidence(commits)'
    BY <1>commit_base, <1>old, CertificateFamilyNext, RequestPrefixAncestryNext,
       CommitCertificateFamilyNext, AdvertisedCommitEvidenceNext, SMT DEF JointMembershipWitnesses
<1>family. CommitCertificateFamily(nextVoteHistory, commits \cup {fresh})'
    BY <1>retained, <1>fresh, FS_AddElement, SMT DEF CommitCertificateFamily
<1>edges. HistoricalEntryEdges' = HistoricalEntryEdges
    BY SMT DEF HistoricalEntryEdges, AppendRequests, AdvanceCommitIndex
<1>metadata. JointWitnessMetadata(nextVoteHistory, ancestry, commits \cup {fresh})'
    BY <1>commit_base, <1>old, <1>retained, <1>family, <1>edges, <1>fresh, SMT
    DEF JointWitnessMetadata, JointMembershipWitnesses, CoversEntryEdges,
        LocalCommitEvidence, AdvertisedCommitEvidence, AdvanceCommitIndex,
        ConfigurationBarrierAncestry, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>old_activity. OpportunityRelations(nextVoteHistory, ancestry, commits)'
    BY <1>commit_base, <1>old, CommitAdvancePreservesOldOpportunities, SMT
<1>intersections. OpportunityCommitIntersections(nextVoteHistory, commits \cup {fresh})'
    BY <1>commit_base, <1>old, <1>fresh, <1>before, CommitAdvanceOpportunityIntersections, SMT
<1>prefixes. OpportunityCommitPrefixes(nextVoteHistory, commits \cup {fresh})'
    BY <1>old_activity, <1>target_protection, SMT
    DEF OpportunityRelations, OpportunityCommitPrefixes,
        PendingTargetProtection, EligibleCampaignsProtectTarget
<1>activity. OpportunityRelations(nextVoteHistory, ancestry, commits \cup {fresh})'
    BY <1>old_activity, <1>intersections, <1>prefixes, SMT DEF OpportunityRelations
<1>ready. ReadyMembershipRelations(nextVoteHistory, ancestry, commits \cup {fresh})'
    BY <1>activity, PostOpportunityRelationsSupplyReady, SMT
<1>protection.
        /\ JointCommitProtection(ancestry, commits \cup {fresh})'
        /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
    <2>frame. PendingEvidenceFrame
        BY <1>commit_base, SMT
        DEF PendingEvidenceFrame, ReplicationMessagesFrame, ContinuingLeadersKeepLogs,
            AppendRequests, AdvanceCommitIndex, TypeOK, ServerVarsTypeOK
    <2>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
        BY <1>commit_base, ConfigurationEvidenceUnchangedWithLogsAndMessages, SMT
        DEF MembershipJointCore, AdvanceCommitIndex
    <2>old. JointCommitProtection(ancestry, commits)' /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
        BY <1>old, <2>frame, <2>targets, JointProtectionPendingEvidenceFrame, SMT
    <2>commits. JointCommitProtection(ancestry, commits \cup {fresh})'
        BY <1>fresh, <1>target_protection, <2>old, SMT DEF JointCommitProtection, PendingTargetProtection
    <2> QED BY <2>old, <2>commits, SMT
<1>witnesses. JointCandidateWitnesses(nextVoteHistory, ancestry, commits \cup {fresh})'
    BY <1>commit_base, <1>metadata, <1>ready, <1>protection, AssembleCandidateWitnessesAfter, SMT
<1>live. LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY <1>commit_base, CommitAdvanceCurrentCertificatesFrame, UnchangedTermsKeepCampaignHistory, ElectionCertificateMessagesFrame, SMT
    DEF MembershipJointCore, LiveLeaderCertificateIntersections, CurrentRequestCertificateIntersections,
        AppendRequests, AdvanceCommitIndex
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry, commits \cup {fresh}, campaigns)'
    BY <1>base, <1>selected, <1>fresh, CausalMetadataCommitCapture, SMT DEF MembershipJointInv, JointOpportunityWitnesses, JointCandidateWitnesses
<1> QED BY <1>acknowledgment_history, <1>commit_base, <1>live, <1>witnesses, <1>causal, SMT
    DEF MembershipJointInv, MembershipJointCore, JointCandidateWitnesses

LEMMA MembershipHistoryVoteRequest ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW vote \in messages, vote.mtype = RequestVoteRequest
                /\ HandleRequestVoteRequest(vote.mdest, vote.msource, vote)
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>selected. JointOpportunityWitnesses(voteHistory, ancestry, commits)
                /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    BY CausalWitnessesDeriveOpportunityWitnesses, SMT DEF MembershipJointInv
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>live. LiveLeaderCertificateIntersections(nextVoteHistory)' /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY <1>base, VoteRequestPreservesLeaderIntersections, VoteRequestPreservesRequestIntersections, SMT
<1>requests. AppendRequests' = AppendRequests
    BY MessageTypesDistinct, SMT DEF AppendRequests, HandleRequestVoteRequest, Send, WithMessage, WithMessages
<1>metadata. JointWitnessMetadata(nextVoteHistory, ancestry, commits)'
    BY <1>base, <1>requests, JointMetadataWithoutNewCommit, SMT DEF HistoricalEntryEdges, HandleRequestVoteRequest
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
    BY <1>base, VoteRequestPreservesEvidenceTargets, SMT
<1>protection. JointCommitProtection(ancestry, commits)' /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
    BY <1>base, <1>targets, VoteRequestHasPendingEvidenceFrame, JointProtectionPendingEvidenceFrame, SMT
    DEF JointMembershipWitnesses
<1>opportunities. OpportunityRelations(nextVoteHistory, ancestry, commits)'
    BY <1>base, <1>selected, <1>targets, <1>requests, VoteRequestOpportunityCertificatesShrink,
       OpportunityRelationsTransport, SMT DEF JointOpportunityWitnesses, HandleRequestVoteRequest
<1>witnesses. JointCandidateWitnesses(nextVoteHistory, ancestry, commits)'
    BY <1>base, <1>metadata, <1>opportunities, <1>protection, PostOpportunityRelationsSupplyReady,
       AssembleCandidateWitnessesAfter, SMT
<1>no_promotion. ~\E actor \in Server: BecomeLeader(actor)
    BY <1>base, ServerStatesDistinct, SMT
    DEF HandleRequestVoteRequest, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>no_client. ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    BY <1>base, ContinuingLeadersExcludeClientAppend, SMT
    DEF ContinuingLeadersKeepLogs, HandleRequestVoteRequest
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>base, <1>selected, <1>no_promotion, <1>no_client, CausalMetadataWithoutPromotion, SMT
<1> QED BY <1>acknowledgment_history, <1>structural, <1>live, <1>witnesses, <1>causal, SMT
    DEF MembershipJointInv, MembershipJointCore, JointOpportunityWitnesses, JointCandidateWitnesses

LEMMA MembershipHistoryAppendReceive ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointInv(voteHistory), [Next]_vars, NEW ancestry, NEW commits, NEW campaigns,
           JointMembershipWitnesses(voteHistory, ancestry, commits), CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns),
           NEW request \in messages, request.mtype = AppendEntriesRequest
                /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE MembershipJointInv(nextVoteHistory)' /\ \E largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVoteHistory, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVoteHistory, largerAncestry, largerCommits, largerCampaigns)'
<1>base.
        /\ MembershipJointCore(voteHistory) /\ TypeOK /\ TypeOK' /\ SendInvariant
        /\ EntryEdgeBase /\ NextIndexBound /\ AppendRequestRootTerm /\ ReplicationEvidenceInv(voteHistory)
    BY JointHistoryStepBase, SMT
<1>acknowledgment_history. AcknowledgmentPrefixHistory' /\ AcknowledgmentVoteCutHistory(nextVoteHistory)'
    BY JointAcknowledgmentHistoryNext, SMT
<1>selected. JointOpportunityWitnesses(voteHistory, ancestry, commits)
                /\ CausalHistoryMetadata(voteHistory, ancestry, commits, campaigns)
    BY CausalWitnessesDeriveOpportunityWitnesses, SMT DEF MembershipJointInv
<1>old. JointMembershipWitnesses(voteHistory, ancestry, commits) BY SMT
<1>retained.
        /\ CertificateFamily(nextVoteHistory, ancestry)' /\ RequestPrefixAncestry(nextVoteHistory, ancestry)'
        /\ CommitCertificateFamily(nextVoteHistory, commits)' /\ AdvertisedCommitEvidence(commits)'
    BY <1>base, <1>old, CertificateFamilyNext, RequestPrefixAncestryNext,
       CommitCertificateFamilyNext, AdvertisedCommitEvidenceNext, SMT
    DEF JointMembershipWitnesses
<1>structural. ReplicationPrefixInv(nextVoteHistory)' /\ CandidateAppendFree' /\ SameTermAcknowledgmentPrefixes'
    BY <1>base, ReplicationPrefixInvNext, CandidateAppendFreeNext, OrderedTermPrefixesAreEdgeConsistent,
       RequestIntersectionsPreserveAcknowledgmentPrefixes, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>no_promotion. ~\E actor \in Server: BecomeLeader(actor)
    <2>frame. ContinuingLeadersKeepLogs
        BY <1>base, AppendReceiveElectionFrame, SMT
    <2> QED BY <1>base, <2>frame, ServerStatesDistinct, SMT
        DEF ContinuingLeadersKeepLogs, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>no_client. ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    BY <1>base, ContinuingLeadersExcludeClientAppend, AppendReceiveElectionFrame, SMT
    DEF ContinuingLeadersKeepLogs
<1>causal. CausalHistoryMetadata(nextVoteHistory, ancestry, commits, campaigns)'
    BY <1>base, <1>old, <1>selected, <1>no_promotion, <1>no_client, CausalMetadataWithoutPromotion, SMT
<1>fields. request.mdest \in Server /\ request.msource \in Server
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>coverage. CoversEntryEdges(ancestry, HistoricalEntryEdges)'
    BY <1>base, <1>old, <1>fields, EntryEdgeAppendReceiveSubset, SMT
    DEF JointMembershipWitnesses, CoversEntryEdges
<1>no_leader_commit. ~(\E leader \in Server:
        AdvanceCommitIndex(leader) /\ commitIndex'[leader] # commitIndex[leader])
    BY <1>base, <1>fields, SMT
    DEF HandleAppendEntriesRequest, AdvanceCommitIndex, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>local. LocalCommitEvidence(commits)'
    BY <1>base, <1>old, <1>no_leader_commit, LocalCommitEvidenceWithoutLeaderAdvance, SMT
    DEF JointMembershipWitnesses
<1>live.
        /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
        /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
        /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
        /\ CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>base, <1>old, AppendReceiveLiveIntersections, SMT
<1>protection. CommitLeaderProtection(commits)' /\ JointCommitProtection(ancestry, commits)'
    BY <1>base, <1>old, AppendReceivePreservesCommitProtection, SMT
<1>evidence_protection. JointEvidenceProtection(nextVoteHistory, ancestry)'
    BY <1>base, <1>selected, <1>causal, AppendReceiveAdmitsRawEvidenceProtection, SMT
<1>witnesses. JointMembershipWitnesses(nextVoteHistory, ancestry, commits)'
    BY <1>old, <1>retained, <1>coverage, <1>local, <1>live, <1>protection, <1>evidence_protection, SMT
    DEF JointMembershipWitnesses
<1> QED BY <1>structural, <1>acknowledgment_history, <1>causal,
    <1>live, <1>witnesses, SMT DEF MembershipJointInv, MembershipJointCore

LEMMA RaftEvidenceSuppliesSafety == RaftEvidenceSafetyRule
<1> SUFFICES ASSUME NEW votes, NEW ancestry, NEW commits, NEW campaigns,
                    RaftEvidence(votes, ancestry, commits, campaigns)
             PROVE RaftSafety BY SMT DEF RaftEvidenceSafetyRule
<1>core. MembershipJointCore(votes) BY SMT DEF RaftEvidence, MembershipJointInv
<1> QED BY <1>core, JointCoreBase, JointCoreImpliesElectionSafety, JointCoreImpliesGreatestCurrentTermIndex,
    JointCoreImpliesLogMatching, SelectedCommitsImplyLogInv, SelectedCommitsImplyQuorumLog,
    SelectedCommitsImplyLeaderCompleteness, SMT DEF RaftEvidence, RaftSafety, MembershipElectionSafety, MoreThanOneLeaderInv

LEMMA RaftInductiveInit == Init => RaftInductiveInv
<1> SUFFICES ASSUME Init PROVE RaftInductiveInv BY SMT
<1>joint. MembershipJointInv({}) BY MembershipJointInit, SMT
<1>history. PICK ancestry, commits, campaigns:
        JointMembershipWitnesses({}, ancestry, commits) /\ CausalHistoryMetadata({}, ancestry, commits, campaigns)
    BY <1>joint, SMT DEF MembershipJointInv
<1>local. LocalCommitPrefixEvidence(commits)
    BY EmptySeq, LenProperties, SMT DEF Init, InitLogVars, LocalCommitPrefixEvidence
<1>evidence. RaftEvidence({}, ancestry, commits, campaigns)
    BY <1>joint, <1>history, <1>local, AppendCommitIndexBoundInit, SMT DEF RaftEvidence
<1> QED BY <1>evidence, RaftEvidenceSuppliesSafety, SMT DEF RaftInductiveInv, RaftEvidenceSafetyRule

\* Close an action using its selected post-state witnesses, not a separate
\* temporal induction over local commits or derived agreement properties.
LEMMA RaftStepWithRetainedHistory ==
    ASSUME NEW votes, NEW nextVotes, NEW ancestry, NEW commits, NEW campaigns,
           RaftEvidence(votes, ancestry, commits, campaigns),
           CampaignHistoryContextStep(votes, nextVotes), [Next]_vars,
           MembershipJointInv(nextVotes)',
           \E largerAncestry, largerCommits, largerCampaigns:
               /\ commits \subseteq largerCommits
               /\ JointMembershipWitnesses(nextVotes, largerAncestry, largerCommits)'
               /\ CausalHistoryMetadata(nextVotes, largerAncestry, largerCommits, largerCampaigns)'
    PROVE RaftInductiveInv'
<1>history. PICK largerAncestry, largerCommits, largerCampaigns:
        /\ commits \subseteq largerCommits
        /\ JointMembershipWitnesses(nextVotes, largerAncestry, largerCommits)'
        /\ CausalHistoryMetadata(nextVotes, largerAncestry, largerCommits, largerCampaigns)'
    BY SMT
<1>bound. AppendCommitIndexBound' BY AppendCommitIndexBoundNext, SMT DEF RaftEvidence
<1>local. LocalCommitPrefixEvidence(largerCommits)'
    BY <1>history, SelectedHistoryPreservesLocalCommitPrefixes, SMT DEF RaftEvidence
<1>evidence. RaftEvidence(nextVotes, largerAncestry, largerCommits, largerCampaigns)'
    BY <1>history, <1>bound, <1>local, SMT DEF RaftEvidence
<1>safety. RaftEvidenceSafetyRule'
    BY RaftEvidenceSuppliesSafety, PTL
<1> QED BY <1>evidence, <1>safety, SMT DEF RaftInductiveInv, RaftEvidenceSafetyRule

\* Cases use the concrete actions of Next, including individual RPC handlers.
LEMMA RaftInductiveNext == RaftInductiveInv /\ [Next]_vars => RaftInductiveInv'
<1> SUFFICES ASSUME RaftInductiveInv, [Next]_vars PROVE RaftInductiveInv' BY SMT
<1>history. PICK votes, ancestry, commits, campaigns: RaftEvidence(votes, ancestry, commits, campaigns)
    BY SMT DEF RaftInductiveInv
<1>joint. /\ MembershipJointInv(votes)
          /\ JointMembershipWitnesses(votes, ancestry, commits)
          /\ CausalHistoryMetadata(votes, ancestry, commits, campaigns)
    BY <1>history, SMT DEF RaftEvidence
<1>context. PICK nextVotes: CampaignHistoryContextStep(votes, nextVotes)
    BY <1>joint, JointCoreBase, MembershipCampaignStepExists, SMT DEF MembershipJointInv
<1>types. TypeOK /\ TypeOK'
    BY <1>joint, <1>context, JointHistoryStepBase, SMT
<1>frame. CASE
        \/ UNCHANGED vars
        \/ \E actor \in Server: Restart(actor) \/ Timeout(actor) \/ LeaderStepDown(actor)
        \/ \E actor, peer \in Server: AppendEntries(actor, peer)
        \/ \E actor \in Server: AdvanceCommitIndex(actor) /\ commitIndex'[actor] <= commitIndex[actor]
        \/ \E m \in messages:
               \/ UpdateTerm(m.mdest, m.msource, m)
               \/ m.mtype = RequestVoteResponse /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
               \/ m.mtype = AppendEntriesResponse /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
    BY <1>history, <1>joint, <1>context, <1>frame,
       MembershipHistoryWithoutAdmission, RaftStepWithRetainedHistory, SMT DEF CandidateRetirementAction
<1>promotion. CASE \E actor \in Server: BecomeLeader(actor)
    BY <1>history, <1>joint, <1>context, <1>promotion,
       MembershipHistoryPromotion, RaftStepWithRetainedHistory, SMT
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>client, SMT
    <2>ordinary. CASE ConfigOf(log'[actor]) # {actor}
        BY <1>history, <1>joint, <1>context, <2>actor, <2>ordinary,
           MembershipHistoryClient, RaftStepWithRetainedHistory, SMT
    <2>singleton. CASE ConfigOf(log'[actor]) = {actor}
        BY <1>history, <1>joint, <1>context, <2>actor, <2>singleton,
           MembershipHistorySingletonClient, RaftStepWithRetainedHistory, SMT
    <2> QED BY <2>ordinary, <2>singleton, SMT
<1>commit. CASE \E actor \in Server: AdvanceCommitIndex(actor) /\ commitIndex'[actor] > commitIndex[actor]
    BY <1>history, <1>joint, <1>context, <1>commit,
       MembershipHistoryCommit, RaftStepWithRetainedHistory, SMT
<1>vote. CASE \E m \in messages: m.mtype = RequestVoteRequest /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
    BY <1>history, <1>joint, <1>context, <1>vote,
       MembershipHistoryVoteRequest, RaftStepWithRetainedHistory, SMT
<1>append. CASE \E m \in messages: m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>history, <1>joint, <1>context, <1>append,
       MembershipHistoryAppendReceive, RaftStepWithRetainedHistory, SMT
<1> QED BY <1>types, <1>frame, <1>promotion, <1>client, <1>commit, <1>vote, <1>append, SMT
    DEF Next, Receive, HandleMsg, TypeOK, LogVarsTypeOK

THEOREM RaftDirectInduction == Spec => []RaftInductiveInv
    BY RaftInductiveInit, RaftInductiveNext, PTL DEF Spec

THEOREM RaftDirectSafety == Spec => []RaftSafety
    BY RaftDirectInduction, PTL DEF RaftInductiveInv

=============================================================================
