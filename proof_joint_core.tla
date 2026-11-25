------------------------------ MODULE proof_joint_core ------------------------------
\* proof_joint_core.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_configuration_history

\* Core of the joint induction. The bounded activity and eligible-support
\* admission argument must still extend this core and close the growing cases.
\* There is deliberately no Spec => []MembershipJointCore claim here.
LiveLeaderCertificateIntersections(voteHistory) ==
    \A left, right \in Server: \A term \in Nat:
    \A leftSnapshot, rightSnapshot \in Seq(LogEntry):
    \A leftOccurrence, rightOccurrence, leftSupport, rightSupport:
        /\ CurrentElectionCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)
        /\ CurrentElectionCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)
        => leftSupport \cap rightSupport # {}

LiveAncestryCertificateIntersections(voteHistory, family) ==
    \A witness \in family: \A leader \in Server: \A term \in Nat:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
        /\ witness.edge.term = term
        => witness.support \cap support # {}

JointCommitProtection(ancestry, commits) ==
    \A certificate \in commits:
        /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
        /\ ProtectedAppendRequests(CommitTarget(certificate), certificate.term)
        /\ ProtectedLeaders(CommitTarget(certificate), certificate.term)
        /\ RecordedAcknowledgersProtected(certificate.leader, certificate.term, CommitTarget(certificate))

JointEvidenceProtection(voteHistory, ancestry) ==
    \A target \in EvidenceAgreementTargets(voteHistory):
        /\ LaterTermPrefixProtection(ancestry, target, LastTerm(target))
        /\ ProtectedAppendRequests(target, LastTerm(target))
        /\ ProtectedLeaders(target, LastTerm(target))

\* Every configuration append retains the actual committed barrier for its
\* predecessor. Election snapshots alone do not justify configuration admission.
ConfigurationBarrierFor(witness, certificate) ==
    /\ certificate.leader = witness.owner
    /\ certificate.term = witness.edge.term
    /\ certificate.index < witness.edge.index
    /\ certificate.configuration.index <= certificate.index
    /\ IsPrefix(certificate.entries, SubSeq(witness.prefix, 1, witness.edge.index - 1))
    /\ certificate.configuration =
           LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
    /\ SingleChange(certificate.configuration.members, ConfigOf(witness.prefix))

ConfigurationBarrierAncestry(ancestry, commits) ==
    \A witness \in ancestry: witness.edge.entry.members # Nil =>
        \E certificate \in commits: ConfigurationBarrierFor(witness, certificate)

JointMembershipData(voteHistory, ancestry, commits) ==
    /\ CertificateFamily(voteHistory, ancestry)
    /\ TermPrefixOrder(ancestry)
    /\ CoversEntryEdges(ancestry, HistoricalEntryEdges)
    /\ RequestPrefixAncestry(voteHistory, ancestry)
    /\ LiveAncestryCertificateIntersections(voteHistory, ancestry)
    /\ CommitCertificateFamily(voteHistory, commits)
    /\ LocalCommitEvidence(commits)
    /\ AdvertisedCommitEvidence(commits)
    /\ CommitLeaderProtection(commits)
    /\ CommitElectionIntersections(voteHistory, commits)
    /\ JointCommitProtection(ancestry, commits)
    /\ ConfigurationBarrierAncestry(ancestry, commits)

JointMembershipWitnesses(voteHistory, ancestry, commits) ==
    /\ CertificateFamily(voteHistory, ancestry)
    /\ TermPrefixOrder(ancestry)
    /\ CoversEntryEdges(ancestry, HistoricalEntryEdges)
    /\ RequestPrefixAncestry(voteHistory, ancestry)
    /\ LiveAncestryCertificateIntersections(voteHistory, ancestry)
    /\ CommitCertificateFamily(voteHistory, commits)
    /\ LocalCommitEvidence(commits)
    /\ AdvertisedCommitEvidence(commits)
    /\ CommitLeaderProtection(commits)
    /\ CommitElectionIntersections(voteHistory, commits)
    /\ JointCommitProtection(ancestry, commits)
    /\ JointEvidenceProtection(voteHistory, ancestry)
    /\ ConfigurationBarrierAncestry(ancestry, commits)

MembershipJointCore(voteHistory) ==
    /\ ReplicationPrefixInv(voteHistory)
    /\ CandidateAppendFree
    /\ SameTermAcknowledgmentPrefixes
    /\ LiveLeaderCertificateIntersections(voteHistory)
    /\ CurrentRequestCertificateIntersections(voteHistory)
    /\ \E ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)

MembershipElectionSafety ==
    \A left, right \in Server:
        state[left] = Leader /\ state[right] = Leader /\ currentTerm[left] = currentTerm[right]
        => left = right

\* This action description covers retirement and volatile-state updates.
\* It is proved for the actual model actions below, not assumed of all Next.
JointRetirementFrame ==
    /\ UNCHANGED <<log, messages>>
    /\ \A server \in Server:
           /\ currentTerm[server] <= currentTerm'[server]
           /\ commitIndex'[server] <= commitIndex[server]
           /\ (state'[server] = Leader =>
                   state[server] = Leader /\ currentTerm'[server] = currentTerm[server])

HigherAppendRequest(peer, term) ==
    \E request \in AppendRequests: request.mdest = peer /\ request.mterm > term

ConflictingHigherAppendRequest(peer, term, target) ==
    \E request \in AppendRequests:
        /\ request.mdest = peer /\ request.mterm > term
        /\ request.mterm <= currentTerm[peer]
        /\ ~RequestRespectsPrefix(request, target)

\* A raised epoch alone does not remove an acknowledged prefix. For a sender
\* that still leads in that epoch, loss requires a retained higher-term RPC.
AcknowledgmentPrefixHistory ==
    \A response \in messages:
        /\ SuccessfulAppendResponse(response) /\ state[response.mdest] = Leader
        /\ currentTerm[response.mdest] = response.mterm
        => \E prefix \in Seq(LogEntry):
               /\ Len(prefix) = response.mmatchIndex
               /\ IsPrefix(prefix, log[response.mdest])
               /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                      IsPrefix(target, log[response.msource])
                      \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)

VoteRequestCoversPrefix(request, prefix) ==
    \/ request.mlastLogTerm > LastTerm(prefix)
    \/ request.mlastLogTerm = LastTerm(prefix) /\ request.mlastLogIndex >= Len(prefix)



EqualOrAdjacentConfigurations(left, right) ==
    left = right \/ SingleChange(left, right)

ConflictingRequestBeforeVote(peer, term, later, target) ==
    \E request \in AppendRequests:
        /\ request.mdest = peer /\ term < request.mterm /\ request.mterm <= later
        /\ ~RequestRespectsPrefix(request, target)

AcknowledgmentVoteCuts(voteHistory, prefix, peer, term) ==
    \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
        \A candidate \in Server: \A later \in Nat:
            /\ term < later /\ RecordedCampaignVote(voteHistory, peer, candidate, later)
            => ConflictingRequestBeforeVote(peer, term, later, target)
               \/ \E request \in RecordedVoteRequests(voteHistory, candidate, later):
                      VoteRequestCoversPrefix(request, target)

AcknowledgmentVoteCutHistory(voteHistory) ==
    \A response \in messages:
        /\ SuccessfulAppendResponse(response) /\ state[response.mdest] = Leader
        /\ currentTerm[response.mdest] = response.mterm
        => \E prefix \in Seq(LogEntry):
               /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log[response.mdest])
               /\ AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
ElectionMessagesFrame ==
    /\ ~(\E actor \in Server: Timeout(actor))
    /\ {message \in messages': message.mtype = RequestVoteRequest}
         = {message \in messages: message.mtype = RequestVoteRequest}
    /\ {message \in messages':
            message.mtype = RequestVoteResponse /\ message.mvoteGranted}
         = {message \in messages:
            message.mtype = RequestVoteResponse /\ message.mvoteGranted}

ContinuingLeadersKeepLogs ==
    \A leader \in Server:
        state'[leader] = Leader =>
            /\ state[leader] = Leader
            /\ currentTerm'[leader] = currentTerm[leader]
            /\ log'[leader] = log[leader]

\* Readiness counts retained votes, including responses not yet delivered to
\* votesGranted. Promotion merely changes an already ready candidate's role.
ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) ==
    /\ candidate \in Server /\ term = currentTerm[candidate]
    /\ state[candidate] \in {Candidate, Leader}
    /\ snapshot = CampaignPrefix(log[candidate], term)
    /\ RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)

ReadyElectionIntersections(voteHistory) ==
    \A left, right \in Server: \A term \in Nat:
    \A leftSnapshot, rightSnapshot \in Seq(LogEntry):
    \A leftOccurrence, rightOccurrence, leftSupport, rightSupport:
        /\ ReadyElectionCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)
        /\ ReadyElectionCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)
        => leftSupport \cap rightSupport # {}

ReadyRequestIntersections(voteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A request \in AppendRequests:
                request.mterm = term =>
                    \E requestSnapshot \in Seq(LogEntry): \E requestOccurrence, requestSupport:
                        /\ RetainedElectionCertificate(voteHistory, request.msource, term,
                                requestSnapshot, requestOccurrence, requestSupport)
                        /\ support \cap requestSupport # {}

ReadyAncestryIntersections(voteHistory, ancestry) ==
    \A witness \in ancestry: \A candidate \in Server: \A term \in Nat:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        /\ witness.edge.term = term
        => witness.support \cap support # {}

ReadyCommitIntersections(voteHistory, commits) ==
    \A certificate \in commits: \A candidate \in Server: \A term \in Nat:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        /\ certificate.term = term
        => certificate.election \cap support # {}

ReadyCommitPrefixes(voteHistory, commits) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A certificate \in commits:
                certificate.term <= term => IsPrefix(CommitTarget(certificate), log[candidate])

ReadyEvidencePrefixes(voteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A target \in EvidenceAgreementTargets(voteHistory):
                LastTerm(target) <= term => IsPrefix(target, log[candidate])

ReadyMembershipRelations(voteHistory, ancestry, commits) ==
    /\ ReadyElectionIntersections(voteHistory) /\ ReadyRequestIntersections(voteHistory)
    /\ ReadyAncestryIntersections(voteHistory, ancestry) /\ ReadyCommitIntersections(voteHistory, commits)
    /\ ReadyCommitPrefixes(voteHistory, commits) /\ ReadyEvidencePrefixes(voteHistory)

JointCandidateWitnesses(voteHistory, ancestry, commits) ==
    /\ JointMembershipWitnesses(voteHistory, ancestry, commits)
    /\ ReadyMembershipRelations(voteHistory, ancestry, commits)

JointWitnessMetadata(voteHistory, ancestry, commits) ==
    /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    /\ CoversEntryEdges(ancestry, HistoricalEntryEdges) /\ RequestPrefixAncestry(voteHistory, ancestry)
    /\ CommitCertificateFamily(voteHistory, commits)
    /\ LocalCommitEvidence(commits) /\ AdvertisedCommitEvidence(commits)
    /\ ConfigurationBarrierAncestry(ancestry, commits)

NoNewReadyCertificates(voteHistory, nextVoteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        ReadyElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
        => ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)

ActiveLogsExtend ==
    \A candidate \in Server:
        state'[candidate] \in {Candidate, Leader} => IsPrefix(log[candidate], log'[candidate])

ActiveCampaignsRetire ==
    \A candidate \in Server:
        state'[candidate] \in {Candidate, Leader} =>
            /\ state[candidate] \in {Candidate, Leader}
            /\ currentTerm'[candidate] = currentTerm[candidate]

CandidateRetirementAction ==
    \/ UNCHANGED vars
    \/ \E server \in Server: Restart(server) \/ LeaderStepDown(server)
    \/ \E server \in Server:
           AdvanceCommitIndex(server) /\ commitIndex'[server] <= commitIndex[server]
    \/ \E message \in messages:
           \/ UpdateTerm(message.mdest, message.msource, message)
           \/ /\ message.mtype = RequestVoteResponse
              /\ HandleRequestVoteResponse(message.mdest, message.msource, message)
           \/ /\ message.mtype = AppendEntriesResponse
              /\ HandleAppendEntriesResponse(message.mdest, message.msource, message)

\* Election-side activity includes future campaigns from every server. A
\* leader can step down before campaigning, so its future snapshot is already
\* included. This is not yet the bounded joint election/replication family.
CampaignOpportunity(candidate, term, snapshot) ==
    /\ candidate \in Server /\ term \in Nat /\ snapshot \in Seq(LogEntry)
    /\ \/ /\ currentTerm[candidate] < term /\ snapshot = log[candidate]
       \/ /\ currentTerm[candidate] = term /\ state[candidate] \in {Candidate, Leader}
          /\ snapshot = CampaignPrefix(log[candidate], term)
          /\ RecordedCampaignRequests(candidate, term) = CampaignRequests(candidate, term, snapshot)

OpportunityVoters(voteHistory, candidate, term, snapshot, config) ==
    {voter \in config:
        \/ RecordedCampaignVote(voteHistory, voter, candidate, term)
        \/ voter = candidate /\ currentTerm[candidate] < term /\ snapshot = log[candidate]
        \/ NewPeerVoteEligible(voter, candidate, term, snapshot)}

OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support) ==
    /\ CampaignOpportunity(candidate, term, snapshot)
    /\ occurrence = LatestConfigurationOccurrence(snapshot)
    /\ occurrence.members \subseteq Server /\ occurrence.members # {}
    /\ support \in Quorums(occurrence.members)
    /\ support \subseteq OpportunityVoters(voteHistory, candidate, term, snapshot, occurrence.members)

OpportunityElectionIntersections(voteHistory) ==
    \A left, right \in Server: \A term \in Nat:
    \A leftSnapshot, rightSnapshot \in Seq(LogEntry):
    \A leftOccurrence, rightOccurrence, leftSupport, rightSupport:
        /\ OpportunityCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)
        /\ OpportunityCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)
        => leftSupport \cap rightSupport # {}

OpportunityRequestIntersections(voteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A request \in AppendRequests:
                request.mterm = term =>
                    \E requestSnapshot \in Seq(LogEntry): \E requestOccurrence, requestSupport:
                        /\ RetainedElectionCertificate(voteHistory, request.msource, term,
                                requestSnapshot, requestOccurrence, requestSupport)
                        /\ support \cap requestSupport # {}

OpportunityAncestryIntersections(voteHistory, ancestry) ==
    \A witness \in ancestry: \A candidate \in Server: \A term \in Nat:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        /\ witness.edge.term = term
        => witness.support \cap support # {}

OpportunityCommitIntersections(voteHistory, commits) ==
    \A certificate \in commits: \A candidate \in Server: \A term \in Nat:
    \A snapshot \in Seq(LogEntry): \A occurrence, support:
        /\ OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        /\ certificate.term = term
        => certificate.election \cap support # {}

OpportunityCommitPrefixes(voteHistory, commits) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A certificate \in commits:
                certificate.term <= term => IsPrefix(CommitTarget(certificate), log[candidate])

OpportunityEvidencePrefixes(voteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support) =>
            \A target \in EvidenceAgreementTargets(voteHistory):
                LastTerm(target) <= term => IsPrefix(target, log[candidate])

OpportunityRelations(voteHistory, ancestry, commits) ==
    /\ OpportunityElectionIntersections(voteHistory) /\ OpportunityRequestIntersections(voteHistory)
    /\ OpportunityAncestryIntersections(voteHistory, ancestry) /\ OpportunityCommitIntersections(voteHistory, commits)
    /\ OpportunityCommitPrefixes(voteHistory, commits) /\ OpportunityEvidencePrefixes(voteHistory)

JointOpportunityWitnesses(voteHistory, ancestry, commits) ==
    /\ JointCandidateWitnesses(voteHistory, ancestry, commits)
    /\ OpportunityRelations(voteHistory, ancestry, commits)

NoNewOpportunityCertificates(voteHistory, nextVoteHistory) ==
    \A candidate \in Server: \A term \in Nat: \A snapshot \in Seq(LogEntry):
    \A occurrence, support:
        OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
        => OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)

FrozenAcknowledgmentPrefixHistory(ancestry) ==
    \A response \in messages: SuccessfulAppendResponse(response) =>
        \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                   IsPrefix(target, log[response.msource])
                   \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)

FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry) ==
    \A response \in messages: SuccessfulAppendResponse(response) =>
        \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)

SnapshotCoversPrefix(snapshot, target) ==
    LastTerm(snapshot) > LastTerm(target)
    \/ (LastTerm(snapshot) = LastTerm(target) /\ Len(snapshot) >= Len(target))

EarlierConflictingRequest(peer, term, later, target) ==
    \E request \in AppendRequests:
        /\ request.mdest = peer /\ term < request.mterm /\ request.mterm < later
        /\ ~RequestRespectsPrefix(request, target)

\* The acknowledged words are frozen by retained requests. The quantification
\* includes retired senders and keeps the original election quorum usable.
FrozenElectionAcknowledgmentCut(ancestry, candidate, term, snapshot, support) ==
    \A response \in messages:
        /\ SuccessfulAppendResponse(response) /\ response.msource \in support /\ response.mterm < term
        => \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
               /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
               /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
               /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                      SnapshotCoversPrefix(snapshot, target)
                      \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)

CausalElectionCertificate(voteHistory, ancestry, candidate, term, snapshot, occurrence, support) ==
    /\ RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    /\ FrozenElectionAcknowledgmentCut(ancestry, candidate, term, snapshot, support)

AppendRequestOwnersUnique ==
    \A left, right \in AppendRequests:
        left.mterm = right.mterm => left.msource = right.msource

FrozenRequestPrefixesAgree(ancestry) ==
    \A left, right \in AppendRequests:
        left.mterm = right.mterm =>
            \A leftPrefix, rightPrefix \in Seq(LogEntry):
                /\ RequestPrefixData(left, leftPrefix) /\ CoveredPrefix(ancestry, leftPrefix)
                /\ RequestPrefixData(right, rightPrefix) /\ CoveredPrefix(ancestry, rightPrefix)
                => IsPrefix(leftPrefix, rightPrefix) \/ IsPrefix(rightPrefix, leftPrefix)

CertificateBlocksConfiguration(certificate, config) ==
    \A support \in Quorums(config): certificate.replication \cap support # {}


\* A role or term change can relax OwnerPrefix. Present agreement evidence
\* nevertheless cannot appear from that relaxation alone: current-term
\* leaders already have the actual request prefixes, and current candidates
\* have no successful append responses in their campaign term.

LEMMA PrefixAcknowledgmentBeforeEvidenceFrame ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CandidateAppendFree, UNCHANGED <<log, messages>>,
           NEW peer \in Server, NEW leader \in Server, NEW term \in Nat,
           term <= currentTerm[leader], NEW target \in Seq(LogEntry),
           IsPrefix(target, log[leader]), RecordedPrefixAcknowledgment(peer, leader, term, target)'
    PROVE RecordedPrefixAcknowledgment(peer, leader, term, target)
<1>base. TypeOK /\ SuccessfulResponseOriginInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>numeric. RecordedAcknowledgment(peer, leader, term, Len(target))
    BY SMT DEF RecordedPrefixAcknowledgment, RecordedAcknowledgment
<1>leader. CASE state[leader] = Leader /\ currentTerm[leader] = term
    BY <1>leader, <1>numeric, CurrentRecordedAcknowledgmentCoversPrefix, SMT
<1>candidate. CASE state[leader] = Candidate /\ currentTerm[leader] = term
    BY <1>base, <1>candidate, <1>numeric, CandidateHasNoCurrentAppendResponses, SMT
    DEF RecordedAcknowledgment
<1>inactive. CASE state[leader] \notin {Candidate, Leader} \/ currentTerm[leader] # term
    <2>frozen. PICK response, request, prefix:
            /\ response \in messages /\ request \in messages /\ prefix \in Seq(LogEntry)
            /\ SuccessfulAppendResponse(response)
            /\ response.msource = peer /\ response.mdest = leader
            /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
            /\ ResponseMatchesRequest(response, request)
            /\ RequestPrefixData(request, prefix) /\ IsPrefix(target, prefix)
        BY SMT DEF RecordedPrefixAcknowledgment
    <2>owner. OwnerPrefix(leader, term, prefix)
        BY <1>inactive, SMT DEF OwnerPrefix
    <2> QED BY <2>frozen, <2>owner, SMT DEF RecordedPrefixAcknowledgment
<1> QED BY <1>leader, <1>candidate, <1>inactive, SMT

LEMMA PresentCommitCertificateBeforeEvidenceFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), CandidateAppendFree, UNCHANGED <<log, messages>>,
           NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)',
           certificate.index = Len(certificate.entries),
           IsPrefix(certificate.entries, log'[certificate.leader])
    PROVE RetainedCommitCertificate(voteHistory, certificate)
<1>base. TypeOK /\ SendInvariant
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>election. RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
        certificate.snapshot, certificate.electionOccurrence, certificate.election)
    <2>bound. certificate.term <= currentTerm[certificate.leader]
        BY <1>base, <1>data, PrefixEntryEqual, LenProperties, SMT
        DEF RetainedCommitCertificate, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
            MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, LogStructureInv, EntryStructure,
            TypeOK, LogVarsTypeOK, IsPrefix
    <2> QED BY <1>base, <1>data, <2>bound, ExistingTermElectionCertificateMessagesFrame, SMT
        DEF RetainedCommitCertificate
<1>term. certificate.term <= currentTerm[certificate.leader]
    BY <1>base, <1>election, SMT DEF RetainedElectionCertificate, VoteSupport, Started, SendInvariant
<1>owner. OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    BY <1>term, SMT DEF OwnerPrefix
<1>target. CommitTarget(certificate) = certificate.entries
    BY <1>data, WholeSequencePrefix, SMT DEF CommitTarget
<1>acks. \A peer \in certificate.replication \ {certificate.leader}:
        RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>data, <1>term, <1>target, PrefixAcknowledgmentBeforeEvidenceFrame, SMT
    DEF RetainedCommitCertificate, Quorums
<1>origin. \A leader, term, entries:
        LocalAppendOrigin(nextVoteHistory, leader, term, entries) <=> LocalAppendOrigin(voteHistory, leader, term, entries)
    BY <1>base, UnchangedLogsExcludeClientAppend, LocalAppendOriginsFrameWithoutClient, SMT
<1> QED BY <1>owner, <1>election, <1>acks, <1>origin, SMT DEF RetainedCommitCertificate

LEMMA EvidenceTargetsUnchangedWithLogsAndMessages ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), CandidateAppendFree, [Next]_vars,
           UNCHANGED <<log, messages>>
    PROVE EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
<1>base. TypeOK /\ SendInvariant
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>forward. EvidenceAgreementTargets(voteHistory) \subseteq EvidenceAgreementTargets(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(voteHistory)
                 PROVE target \in EvidenceAgreementTargets(nextVoteHistory)'
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(voteHistory, certificate)
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>retained. RetainedCommitCertificate(nextVoteHistory, certificate)'
        BY <1>base, <2>certificate, RetainedCommitCertificateNext, SMT
    <2> QED BY <2>certificate, <2>retained, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget
<1>reverse. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory)
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)'
                 PROVE target \in EvidenceAgreementTargets(voteHistory)
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log'[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>before. RetainedCommitCertificate(voteHistory, certificate)
        BY <2>certificate, PresentCommitCertificateBeforeEvidenceFrame, SMT
    <2> QED BY <2>certificate, <2>before, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget
<1> QED BY <1>forward, <1>reverse, SMT

LEMMA ConfigurationEvidenceUnchangedWithLogsAndMessages ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), CandidateAppendFree, [Next]_vars,
           UNCHANGED <<log, messages>>
    PROVE ((<<EvidenceAgreementTargets(nextVoteHistory), EvidenceConfigurationHistory(nextVoteHistory), EvidenceWorkingConfiguration(nextVoteHistory)>>)' = <<EvidenceAgreementTargets(voteHistory), EvidenceConfigurationHistory(voteHistory), EvidenceWorkingConfiguration(voteHistory)>>)
    BY EvidenceTargetsUnchangedWithLogsAndMessages, SMT
    DEF EvidenceConfigurationHistory, ConfigurationHistory, EvidenceWorkingConfiguration

LEMMA JointCoreBase ==
    ASSUME NEW voteHistory
    PROVE MembershipJointCore(voteHistory) =>
        /\ TypeOK /\ SendInvariant /\ EntryEdgeBase /\ VoteRecordInv(voteHistory)
        /\ MembershipCampaignsInv(voteHistory) /\ ReplicationEvidenceInv(voteHistory)
    BY CampaignsSupplyEntryBounds, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv,
        MembershipStructureInv, ReplicationBoundsInv, EntryEdgeBase

LEMMA JointCoreImpliesElectionSafety ==
    ASSUME NEW voteHistory
    PROVE MembershipJointCore(voteHistory) => MembershipElectionSafety
<1> SUFFICES ASSUME MembershipJointCore(voteHistory), NEW left \in Server, NEW right \in Server,
                      state[left] = Leader, state[right] = Leader,
                      currentTerm[left] = currentTerm[right]
             PROVE left = right
    BY SMT DEF MembershipElectionSafety
<1>base. MembershipCampaignsInv(voteHistory) /\ VoteRecordInv(voteHistory) /\ currentTerm[left] \in Nat
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>left. PICK leftSnapshot, leftOccurrence, leftSupport:
        /\ leftSnapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, left, currentTerm[left], leftSnapshot, leftOccurrence, leftSupport)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT
<1>right. PICK rightSnapshot, rightOccurrence, rightSupport:
        /\ rightSnapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, right, currentTerm[left], rightSnapshot, rightOccurrence, rightSupport)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT
<1>intersect. leftSupport \cap rightSupport # {}
    BY <1>base, <1>left, <1>right, SMT
    DEF MembershipJointCore, LiveLeaderCertificateIntersections
<1> QED BY <1>base, <1>left, <1>right, <1>intersect, IntersectingVoteSupportsUnique, SMT
    DEF CurrentElectionCertificate

LEMMA JointCoreImpliesLogMatching ==
    ASSUME NEW voteHistory
    PROVE MembershipJointCore(voteHistory) => LogMatchingInv
<1> SUFFICES ASSUME MembershipJointCore(voteHistory) PROVE LogMatchingInv BY SMT
<1>witnesses. PICK ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF MembershipJointCore
<1>consistent. WitnessEdgeConsistency(ancestry)
    BY <1>witnesses, OrderedTermPrefixesAreEdgeConsistent, SMT DEF JointMembershipWitnesses
<1> QED BY <1>witnesses, <1>consistent, JointCoreBase, ConsistentFamilyImpliesLogMatching, SMT
    DEF JointMembershipWitnesses

LEMMA JointCoreImpliesCompatibleHistory ==
    ASSUME NEW voteHistory
    PROVE MembershipJointCore(voteHistory) => ConfigurationHistoryCompatible(EvidenceConfigurationHistory(voteHistory))
<1> SUFFICES ASSUME MembershipJointCore(voteHistory)
             PROVE ConfigurationHistoryCompatible(EvidenceConfigurationHistory(voteHistory)) BY SMT
<1>witnesses. PICK ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF MembershipJointCore
<1> QED BY <1>witnesses, JointCoreBase, EvidenceHistoryCompatibleFromHistoricalBoundaries, SMT
    DEF JointMembershipWitnesses, JointEvidenceProtection

LEMMA CurrentCertificateRetirementFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), JointRetirementFrame, NEW leader \in Server, state'[leader] = Leader,
           NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    BY SMT DEF JointRetirementFrame, CurrentElectionCertificate,
        RecordedCampaignRequests, VoteSupport, VoteFor, Grant, Started,
        CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord, HistoryCampaignSnapshot

LEMMA LiveIntersectionsRetirementFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), JointRetirementFrame, LiveLeaderCertificateIntersections(voteHistory),
           CurrentRequestCertificateIntersections(voteHistory), NEW ancestry, NEW commits,
           LiveAncestryCertificateIntersections(voteHistory, ancestry), CommitElectionIntersections(voteHistory, commits)
    PROVE /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
          /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
          /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
          /\ CommitElectionIntersections(nextVoteHistory, commits)'
<1>leaders. LiveLeaderCertificateIntersections(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW left \in Server, NEW right \in Server, NEW term \in Nat,
                          NEW leftSnapshot \in Seq(LogEntry), NEW rightSnapshot \in Seq(LogEntry),
                          NEW leftOccurrence, NEW rightOccurrence, NEW leftSupport, NEW rightSupport,
                          CurrentElectionCertificate(nextVoteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)',
                          CurrentElectionCertificate(nextVoteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)'
                 PROVE leftSupport \cap rightSupport # {}
        BY SMT DEF LiveLeaderCertificateIntersections
    <2>active. state'[left] = Leader /\ state'[right] = Leader
        BY SMT DEF CurrentElectionCertificate
    <2>before. /\ CurrentElectionCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)
                /\ CurrentElectionCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)
        BY <2>active, CurrentCertificateRetirementFrame, SMT
    <2> QED BY <2>before, SMT DEF LiveLeaderCertificateIntersections
<1>requests. CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY CurrentCertificateRetirementFrame, ElectionCertificateMessagesRetained, SMT
    DEF CurrentRequestCertificateIntersections, JointRetirementFrame, AppendRequests
<1>ancestry. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY CurrentCertificateRetirementFrame, SMT
    DEF LiveAncestryCertificateIntersections, CurrentElectionCertificate
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY CurrentCertificateRetirementFrame, SMT
    DEF CommitElectionIntersections, JointRetirementFrame, CurrentElectionCertificate
<1> QED BY <1>leaders, <1>requests, <1>ancestry, <1>commits, SMT

LEMMA JointProtectionRetirementFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), JointRetirementFrame, ((EvidenceAgreementTargets(nextVoteHistory))' = EvidenceAgreementTargets(voteHistory)),
           NEW ancestry, NEW commits, JointCommitProtection(ancestry, commits),
           JointEvidenceProtection(voteHistory, ancestry), CommitLeaderProtection(commits)
    PROVE /\ JointCommitProtection(ancestry, commits)'
          /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
          /\ CommitLeaderProtection(commits)'
    BY SMT
    DEF JointCommitProtection, JointEvidenceProtection, CommitLeaderProtection,
        JointRetirementFrame, ProtectedAppendRequests, ProtectedLeaders, AppendRequests,
        RecordedAcknowledgersProtected, RecordedReplicationSupport,
        RecordedAcknowledgment, ProtectedVoters

LEMMA JointWitnessesRetirementFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, JointRetirementFrame,
           NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits)
    PROVE JointMembershipWitnesses(nextVoteHistory, ancestry, commits)'
<1>base. TypeOK /\ SendInvariant /\ ReplicationEvidenceInv(voteHistory) /\ TypeOK'
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv,
        MembershipStructureInv, ReplicationBoundsInv
<1>families.
        /\ CertificateFamily(nextVoteHistory, ancestry)' /\ RequestPrefixAncestry(nextVoteHistory, ancestry)'
        /\ CommitCertificateFamily(nextVoteHistory, commits)'
    BY <1>base, CertificateFamilyNext, RequestPrefixAncestryNext,
       CommitCertificateFamilyNext, SMT DEF JointMembershipWitnesses
<1>before.
        /\ TermPrefixOrder(ancestry) /\ CoversEntryEdges(ancestry, HistoricalEntryEdges)
        /\ AdvertisedCommitEvidence(commits)
    BY SMT DEF JointMembershipWitnesses
<1>order. TermPrefixOrder(ancestry)'
    BY <1>before, SMT DEF TermPrefixOrder
<1>edges. HistoricalEntryEdges' = HistoricalEntryEdges
    BY SMT DEF JointRetirementFrame, HistoricalEntryEdges, AppendRequests
<1>coverage. CoversEntryEdges(ancestry, HistoricalEntryEdges)'
    BY <1>before, <1>edges, SMT DEF CoversEntryEdges
<1>advertised. AdvertisedCommitEvidence(commits)'
    BY <1>before, SMT DEF JointRetirementFrame,
        AppendRequests, AdvertisedCommitEvidence
<1>local. LocalCommitEvidence(commits)'
    BY <1>base, CommitCertificateFamilyTypes, SMT
    DEF JointMembershipWitnesses, JointRetirementFrame, LocalCommitEvidence,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>evidence. ((EvidenceAgreementTargets(nextVoteHistory))' = EvidenceAgreementTargets(voteHistory))
    BY ConfigurationEvidenceUnchangedWithLogsAndMessages, SMT
    DEF MembershipJointCore, JointRetirementFrame
<1>intersections.
        /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
        /\ CommitElectionIntersections(nextVoteHistory, commits)'
    BY LiveIntersectionsRetirementFrame, SMT DEF MembershipJointCore, JointMembershipWitnesses
<1>protection.
        /\ JointCommitProtection(ancestry, commits)'
        /\ JointEvidenceProtection(nextVoteHistory, ancestry)' /\ CommitLeaderProtection(commits)'
    BY <1>evidence, JointProtectionRetirementFrame, SMT DEF JointMembershipWitnesses
<1> QED BY <1>families, <1>order, <1>coverage, <1>advertised,
    <1>local, <1>intersections, <1>protection, SMT
    DEF JointMembershipWitnesses

LEMMA AcknowledgmentPrefixHistoryInit == Init => AcknowledgmentPrefixHistory
    BY SMT DEF Init, AcknowledgmentPrefixHistory


LEMMA ConflictingHigherAppendRequestRetained ==
    ASSUME TypeOK, [Next]_vars, NEW peer \in Server, NEW term \in Nat, NEW target,
           ConflictingHigherAppendRequest(peer, term, target)
    PROVE ConflictingHigherAppendRequest(peer, term, target)'
<1>request. PICK request \in AppendRequests:
        /\ request.mdest = peer /\ request.mterm > term
        /\ request.mterm <= currentTerm[peer] /\ ~RequestRespectsPrefix(request, target)
    BY SMT DEF ConflictingHigherAppendRequest
<1>epochs.
        /\ currentTerm[peer] \in Nat /\ currentTerm'[peer] \in Nat /\ request.mterm \in Nat
        /\ currentTerm[peer] <= currentTerm'[peer]
    BY <1>request, CurrentTermsMonotonicNext, ServerVarsTypeOKNext, MessageFieldsTypeOK, SMT
    DEF AppendRequests, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>retained. request \in AppendRequests'
    BY <1>request, MessagesMonotonicNext, SMT DEF AppendRequests
<1> QED BY <1>request, <1>epochs, <1>retained, SMT DEF ConflictingHigherAppendRequest

LEMMA AcknowledgedTargetNextUnlessConflictingRequest ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW leader \in Server, NEW peer \in Server,
           NEW term \in Nat, state[leader] = Leader, state'[leader] = Leader,
           currentTerm[leader] = term, currentTerm[peer] >= term, NEW target \in Seq(LogEntry),
           IsPrefix(target, log[leader]), IsPrefix(target, log[peer])
    PROVE IsPrefix(target, log'[peer]) \/ ConflictingHigherAppendRequest(peer, term, target)'
<1>base. TypeOK /\ EntryEdgeBase /\ ReplicationPrefixInv(voteHistory) /\ MembershipCampaignsInv(voteHistory)
    BY JointCoreBase, SMT DEF MembershipJointCore
<1>senders. CurrentRequestSendersUnique
    BY <1>base, IntersectingRequestCertificatesIdentifySenders, SMT DEF MembershipJointCore
<1>conflict. CASE ConflictingHigherAppendRequest(peer, term, target)'
    BY <1>conflict, SMT
<1>no_conflict. CASE ~ConflictingHigherAppendRequest(peer, term, target)'
    <2>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>base, <2>client, ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
        DEF ClientRequest, TypeOK, LogVarsTypeOK
    <2>receive. CASE \E request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        <3>request. PICK request \in messages:
                /\ request.mtype = AppendEntriesRequest
                /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
            BY <2>receive, SMT
        <3>fields.
                /\ request \in AppendRequests /\ request.mterm \in Nat
                /\ request.msource \in Server /\ request.mdest \in Server
            BY <1>base, <3>request, MessageFieldsTypeOK, SMT DEF AppendRequests, TypeOK, MsgTypeOK
        <3>recipient. CASE peer = request.mdest
            <4>same. request.mterm = term => RequestRespectsPrefix(request, target)
                BY <1>base, <1>senders, <3>fields, SameTermRequestRespectsLeaderPrefix, SMT
            <4>higher. request.mterm > term => RequestRespectsPrefix(request, target)
                BY <1>base, <1>no_conflict, <3>request, <3>fields, <3>recipient, MessagesMonotonicNext, SMT
                DEF ConflictingHigherAppendRequest, AppendRequests, HandleAppendEntriesRequest
            <4>received. IsPrefix(target, log'[peer])
                BY <1>base, <3>request, <3>fields, <3>recipient, <4>same, <4>higher,
                   AppendRequestPreservesProtectedPrefix, SMT
            <4> QED BY <4>received, SMT
        <3>other. CASE peer # request.mdest
            BY <1>base, <3>request, <3>other, SMT
            DEF HandleAppendEntriesRequest, TypeOK, LogVarsTypeOK
        <3> QED BY <3>recipient, <3>other, SMT
    <2>same. CASE UNCHANGED log
        BY <2>same, SMT
    <2> QED BY <1>base, <2>client, <2>receive, <2>same, LogChangingActionNext, SMT
<1> QED BY <1>conflict, <1>no_conflict, SMT

LEMMA AcknowledgmentPrefixHistoryNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), AcknowledgmentPrefixHistory, [Next]_vars
    PROVE AcknowledgmentPrefixHistory'
<1>base.
        /\ TypeOK /\ SendInvariant /\ ReplicationPrefixInv(voteHistory) /\ SuccessfulResponseOriginInv
        /\ CandidateAppendFree /\ TypeOK'
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv,
        MembershipStructureInv, ReplicationBoundsInv
<1>chosen. PICK ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF MembershipJointCore
<1>consistent. WitnessEdgeConsistency(ancestry)
    BY <1>chosen, OrderedTermPrefixesAreEdgeConsistent, SMT DEF JointMembershipWitnesses
<1> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response),
                      state'[response.mdest] = Leader, currentTerm'[response.mdest] = response.mterm
             PROVE \E prefix \in Seq(LogEntry):
                       /\ Len(prefix) = response.mmatchIndex
                       /\ IsPrefix(prefix, log'[response.mdest])
                       /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                              IsPrefix(target, log'[response.msource])
                              \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
    BY SMT DEF AcknowledgmentPrefixHistory
<1>fields.
        /\ response.msource \in Server /\ response.mdest \in Server /\ response.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>old. CASE response \in messages
    <2>continues. CASE state[response.mdest] = Leader
        <3>epoch. currentTerm[response.mdest] = response.mterm
            BY <1>base, <1>fields, <2>continues, ContinuingLeaderTermNext, SMT
        <3>prefix. PICK prefix \in Seq(LogEntry):
                /\ Len(prefix) = response.mmatchIndex
                /\ IsPrefix(prefix, log[response.mdest])
                /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                       IsPrefix(target, log[response.msource])
                       \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
            BY <1>old, <2>continues, <3>epoch, SMT DEF AcknowledgmentPrefixHistory
        <3>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                IsPrefix(target, log'[response.msource])
                \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
            <4> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix)
                         PROVE IsPrefix(target, log'[response.msource])
                               \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
                BY SMT
            <4>owner. IsPrefix(target, log[response.mdest])
                BY <1>base, <1>fields, <3>prefix, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
            <4>conflict. CASE ConflictingHigherAppendRequest(response.msource, response.mterm, target)
                BY <1>base, <1>fields, <4>conflict, ConflictingHigherAppendRequestRetained, SMT
            <4>physical. CASE IsPrefix(target, log[response.msource])
                <5>bound. response.mterm <= currentTerm[response.msource]
                    BY <1>base, <1>old, SMT DEF SendInvariant
                <5> QED BY <1>fields, <2>continues, <3>epoch, <4>owner, <4>physical, <5>bound,
                    AcknowledgedTargetNextUnlessConflictingRequest, SMT
            <4> QED BY <3>prefix, <4>conflict, <4>physical, SMT
        <3>owner. IsPrefix(prefix, log'[response.mdest])
            BY <1>base, <1>fields, <2>continues, <3>prefix, ContinuingLeaderPrefixNext, SMT
        <3> QED BY <3>prefix, <3>targets, <3>owner, SMT
    <2>promoted. CASE state[response.mdest] # Leader
        <3>action. BecomeLeader(response.mdest)
            BY <1>base, <1>fields, <2>promoted, NewLeaderUsesBecomeLeader, SMT
        <3>candidate. state[response.mdest] = Candidate /\ currentTerm[response.mdest] = response.mterm
            BY <3>action, SMT DEF BecomeLeader
        <3> QED BY <1>base, <1>fields, <1>old, <3>candidate, CandidateHasNoCurrentAppendResponses, SMT
    <2> QED BY <2>continues, <2>promoted, SMT
<1>new. CASE response \notin messages
    <2>prefix. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ OwnerPrefix(request.msource, request.mterm, prefix)
            /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log'[response.msource])
        BY <1>base, <1>chosen, <1>consistent, <1>new, NewAcknowledgmentHasPhysicalPrefix, SMT
        DEF JointMembershipWitnesses
    <2>fields. request.msource \in Server /\ request.mterm \in Nat
        BY <1>base, <2>prefix, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
    <2>owner. OwnerPrefix(request.msource, request.mterm, prefix)'
        BY <1>base, <2>prefix, <2>fields, OwnerPrefixNext, SMT
    <2>sender. IsPrefix(prefix, log'[response.mdest])
        BY <2>prefix, <2>owner, SMT DEF ResponseMatchesRequest, OwnerPrefix
    <2>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) => IsPrefix(target, log'[response.msource])
        BY <1>base, <1>fields, <2>prefix, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>prefix, <2>sender, <2>targets, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA NewRecordedVoteHasFreshRequest ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, TypeOK', SendInvariant', [Next]_vars,
           NEW peer \in Server, NEW candidate \in Server, NEW term \in Nat,
           RecordedCampaignVote(nextVoteHistory, peer, candidate, term)', ~RecordedCampaignVote(voteHistory, peer, candidate, term)
    PROVE \E request \in RecordedVoteRequests(nextVoteHistory, candidate, term)': VoteRequestFreshFor(request, peer)
<1>self. CASE peer = candidate
    <2>no_self_grant. ~Grant(candidate, candidate, term)'
        BY SMT DEF Grant, SendInvariant
    <2>starts. Started(nextVoteHistory, candidate, term)' /\ ~Started(voteHistory, candidate, term)
        BY <1>self, <2>no_self_grant, SMT DEF RecordedCampaignVote
    <2>started. HistoryStarted(nextVoteHistory, candidate, term) /\ ~HistoryStarted(voteHistory, candidate, term)
        BY <2>starts, CampaignHistoryStartIsStarted, SMT
        DEF Started, HistoryStarted, CampaignHistoryContextStep
    <2>origin. Timeout(candidate) /\ term = currentTerm[candidate] + 1
          /\ HistoryCampaignSnapshot(nextVoteHistory, candidate, term, log[candidate])
        BY <2>started, NewHistoricalCampaignIsTimeout, SMT
    <2>request. PICK request:
        request = [mtype |-> RequestVoteRequest, mterm |-> term,
                   mlastLogTerm |-> LastTerm(log[candidate]), mlastLogIndex |-> Len(log[candidate]),
                   msource |-> candidate, mdest |-> candidate]
        BY SMT
    <2> QED BY <1>self, <2>origin, <2>request, LastTermTypeOK, LenProperties, SMT
        DEF RecordedVoteRequests, HistoryCampaignSnapshot, VoteRequestFreshFor, TypeOK, LogVarsTypeOK
<1>peer. CASE peer # candidate
    <2>response. PICK response \in messages' \ messages:
            /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
            /\ response.msource = peer /\ response.mdest = candidate /\ response.mterm = term
        BY <1>peer, SMT DEF RecordedCampaignVote, Grant
    <2>request. PICK request \in messages:
            /\ request.mtype = RequestVoteRequest /\ request.msource = candidate
            /\ request.mterm = term /\ VoteRequestEligible(request, peer)
        BY <2>response, NewPositiveVoteHasEligibleRequest, SMT DEF VoteRequestEligible
    <2> QED BY <2>request, MessagesMonotonicNext, SMT
        DEF RecordedCampaignRequests, RecordedVoteRequests, VoteRequestEligible
<1> QED BY <1>self, <1>peer, SMT

LEMMA FreshRequestCoversHeldPrefix ==
    ASSUME NEW entries \in Seq(LogEntry), TermsOrdered(entries), NEW prefix \in Seq(LogEntry),
           IsPrefix(prefix, entries), NEW request, request.mlastLogTerm \in Nat,
           request.mlastLogIndex \in Nat,
           request.mlastLogTerm > LastTerm(entries)
               \/ (request.mlastLogTerm = LastTerm(entries) /\ request.mlastLogIndex >= Len(entries))
    PROVE VoteRequestCoversPrefix(request, prefix)
<1>types.
        /\ LastTerm(entries) \in Nat /\ LastTerm(prefix) \in Nat
        /\ Len(entries) \in Nat /\ Len(prefix) \in Nat /\ Len(prefix) <= Len(entries)
    BY LastTermTypeOK, LenProperties, SMT DEF IsPrefix
<1>empty. CASE Len(prefix) = 0
    BY <1>empty, SMT DEF VoteRequestCoversPrefix, LastTerm
<1>nonempty. CASE Len(prefix) > 0
    <2>bound. LastTerm(prefix) <= LastTerm(entries)
        BY <1>nonempty, OrderedPrefixLastTermBound, SMT
    <2> QED BY <1>types, <2>bound, SMT DEF VoteRequestCoversPrefix
<1> QED BY <1>types, <1>empty, <1>nonempty, SMT



LEMMA EqualOrAdjacentQuorumsIntersect ==
    ASSUME NEW left \in SUBSET Server, NEW right \in SUBSET Server,
           EqualOrAdjacentConfigurations(left, right),
           NEW first \in Quorums(left), NEW second \in Quorums(right)
    PROVE first \cap second # {}
    BY ServerOK, FiniteSetSubsetsAreFinite,
       SameConfigurationQuorumsIntersect, OneMemberExtensionQuorumsIntersect, SMT
    DEF EqualOrAdjacentConfigurations, SingleChange

LEMMA CoveredPrefixRestriction ==
    ASSUME NEW ancestry, NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries),
           NEW prefix \in Seq(LogEntry), IsPrefix(prefix, entries)
    PROVE CoveredPrefix(ancestry, prefix)
    BY PrefixEntryEdgesEqual, LenProperties, SMT DEF CoveredPrefix, IsPrefix

LEMMA AcknowledgmentVoteCutHistoryInit ==
    Init => AcknowledgmentVoteCutHistory({})
    BY SMT DEF Init, AcknowledgmentVoteCutHistory

LEMMA NewRecordedVotePreEpochBound ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, TypeOK', SendInvariant', [Next]_vars,
           NEW peer \in Server, NEW candidate \in Server, NEW term \in Nat,
           RecordedCampaignVote(nextVoteHistory, peer, candidate, term)', ~RecordedCampaignVote(voteHistory, peer, candidate, term)
    PROVE currentTerm[peer] <= term
<1>self. CASE peer = candidate
    <2>no_self_grant. ~Grant(candidate, candidate, term)'
        BY SMT DEF Grant, SendInvariant
    <2>starts. Started(nextVoteHistory, candidate, term)' /\ ~Started(voteHistory, candidate, term)
        BY <1>self, <2>no_self_grant, SMT DEF RecordedCampaignVote
    <2>started. HistoryStarted(nextVoteHistory, candidate, term) /\ ~HistoryStarted(voteHistory, candidate, term)
        BY <2>starts, CampaignHistoryStartIsStarted, SMT
        DEF Started, HistoryStarted, CampaignHistoryContextStep
    <2> QED BY <1>self, <2>started, NewHistoricalCampaignIsTimeout, SMT
        DEF TypeOK, ServerVarsTypeOK
<1>peer. CASE peer # candidate
    <2>response. PICK response \in messages' \ messages:
            /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
            /\ response.msource = peer /\ response.mdest = candidate /\ response.mterm = term
        BY <1>peer, SMT DEF RecordedCampaignVote, Grant
    <2>request. PICK request \in messages:
            /\ request.mtype = RequestVoteRequest /\ request.msource = candidate
            /\ request.mterm = term /\ VoteRequestEligible(request, peer)
        BY <2>response, NewPositiveVoteHasEligibleRequest, SMT DEF VoteRequestEligible
    <2> QED BY <2>request, SMT DEF VoteRequestEligible
<1> QED BY <1>self, <1>peer, SMT

LEMMA FixedAcknowledgmentTargetHistory ==
    ASSUME TypeOK, AcknowledgmentPrefixHistory, NEW response \in messages,
           SuccessfulAppendResponse(response), response.msource \in Server, response.mdest \in Server,
           state[response.mdest] = Leader, currentTerm[response.mdest] = response.mterm,
           NEW prefix \in Seq(LogEntry), Len(prefix) = response.mmatchIndex,
           IsPrefix(prefix, log[response.mdest]), NEW target \in Seq(LogEntry), IsPrefix(target, prefix)
    PROVE IsPrefix(target, log[response.msource])
          \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
<1>frozen. PICK frozen \in Seq(LogEntry):
        /\ Len(frozen) = response.mmatchIndex /\ IsPrefix(frozen, log[response.mdest])
        /\ \A part \in Seq(LogEntry): IsPrefix(part, frozen) =>
               IsPrefix(part, log[response.msource])
               \/ ConflictingHigherAppendRequest(response.msource, response.mterm, part)
    BY SMT DEF AcknowledgmentPrefixHistory
<1>equal. prefix = frozen
    BY <1>frozen, PrefixesWithBoundedLength, WholeSequencePrefix, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK, IsPrefix
<1> QED BY <1>frozen, <1>equal, SMT

LEMMA AcknowledgmentVoteCutsNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), AcknowledgmentPrefixHistory, [Next]_vars,
           NEW response \in messages, SuccessfulAppendResponse(response),
           state[response.mdest] = Leader, currentTerm[response.mdest] = response.mterm,
           NEW prefix \in Seq(LogEntry), Len(prefix) = response.mmatchIndex,
           IsPrefix(prefix, log[response.mdest]),
           AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
    PROVE AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
<1>base.
        /\ TypeOK /\ TypeOK' /\ SendInvariant'
        /\ response.msource \in Server /\ response.mdest \in Server /\ response.mterm \in Nat
        /\ TermsOrdered(log[response.msource])
    <2>pre. TypeOK /\ SendInvariant /\ ReplicationPrefixInv(voteHistory)
        BY JointCoreBase, SMT DEF MembershipJointCore
    <2>post. ReplicationPrefixInv(nextVoteHistory)'
        BY <2>pre, ReplicationPrefixInvNext, SMT
    <2>post_type. TypeOK' /\ SendInvariant'
        BY <2>post, SMT
        DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
            MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
    <2>fields. response.msource \in Server /\ response.mdest \in Server /\ response.mterm \in Nat
        BY <2>pre, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
    <2>terms. TermsOrdered(log[response.msource])
        BY <2>fields, JointCoreBase, SMT
        DEF MembershipCampaignsInv, MembershipVotesInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
    <2> QED BY <2>pre, <2>post_type, <2>fields, <2>terms, SMT
<1> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix),
                      NEW candidate \in Server, NEW later \in Nat,
                      later > response.mterm, RecordedCampaignVote(nextVoteHistory, response.msource, candidate, later)'
             PROVE ConflictingRequestBeforeVote(response.msource, response.mterm, later, target)'
                   \/ \E request \in RecordedVoteRequests(nextVoteHistory, candidate, later)':
                          VoteRequestCoversPrefix(request, target)
    BY SMT DEF AcknowledgmentVoteCuts
<1>old. CASE RecordedCampaignVote(voteHistory, response.msource, candidate, later)
    <2>before.
            ConflictingRequestBeforeVote(response.msource, response.mterm, later, target)
            \/ \E request \in RecordedVoteRequests(voteHistory, candidate, later):
                   VoteRequestCoversPrefix(request, target)
        BY <1>old, SMT DEF AcknowledgmentVoteCuts
    <2>messages. messages \subseteq messages'
        BY <1>base, MessagesMonotonicNext, SMT
    <2>history. voteHistory \subseteq nextVoteHistory
        BY CampaignHistoryContextMonotone, SMT
    <2>requests. RecordedVoteRequests(voteHistory, candidate, later)
            \subseteq RecordedVoteRequests(nextVoteHistory, candidate, later)'
        BY <2>messages, <2>history, RecordedVoteRequestsMonotone, SMT
    <2> QED BY <2>before, <2>messages, <2>requests, SMT
        DEF ConflictingRequestBeforeVote, AppendRequests
<1>new. CASE ~RecordedCampaignVote(voteHistory, response.msource, candidate, later)
    <2>epoch. currentTerm[response.msource] <= later
        BY <1>base, <1>new, NewRecordedVotePreEpochBound, SMT
    <2>history. IsPrefix(target, log[response.msource])
              \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
        BY <1>base, FixedAcknowledgmentTargetHistory, SMT
    <2>conflict. CASE ConflictingHigherAppendRequest(response.msource, response.mterm, target)
        BY <1>base, <2>epoch, <2>conflict, MessagesMonotonicNext, MessageFieldsTypeOK, SMT
        DEF ConflictingHigherAppendRequest, ConflictingRequestBeforeVote, AppendRequests, TypeOK, MsgTypeOK, ServerVarsTypeOK
    <2>physical. CASE IsPrefix(target, log[response.msource])
        <3>request. PICK request \in RecordedVoteRequests(nextVoteHistory, candidate, later)':
                VoteRequestFreshFor(request, response.msource)
            BY <1>base, <1>new, NewRecordedVoteHasFreshRequest, SMT
        <3>fields. request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
            BY <1>base, <3>request, RecordedVoteRequestFieldsAfter, SMT
            DEF CampaignHistoryContextStep
        <3>entries. log[response.msource] \in Seq(LogEntry)
            BY <1>base, SMT DEF TypeOK, LogVarsTypeOK
        <3>fresh.
                request.mlastLogTerm > LastTerm(log[response.msource])
                \/ (request.mlastLogTerm = LastTerm(log[response.msource])
                    /\ request.mlastLogIndex >= Len(log[response.msource]))
            BY <3>request, SMT DEF VoteRequestFreshFor
        <3>covers. VoteRequestCoversPrefix(request, target)
            BY <1>base, <2>physical, <3>entries, <3>fresh, <3>fields, FreshRequestCoversHeldPrefix, SMT
        <3> QED BY <3>request, <3>covers, SMT
    <2> QED BY <2>history, <2>conflict, <2>physical, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA AcknowledgmentVoteCutHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), AcknowledgmentPrefixHistory, AcknowledgmentVoteCutHistory(voteHistory), [Next]_vars
    PROVE AcknowledgmentVoteCutHistory(nextVoteHistory)'
<1>base.
        /\ TypeOK /\ TypeOK' /\ SendInvariant' /\ CandidateAppendFree /\ SuccessfulResponseOriginInv
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>chosen. PICK ancestry, commits: JointMembershipWitnesses(voteHistory, ancestry, commits)
    BY SMT DEF MembershipJointCore
<1>consistent. WitnessEdgeConsistency(ancestry)
    BY <1>chosen, OrderedTermPrefixesAreEdgeConsistent, SMT DEF JointMembershipWitnesses
<1> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response),
                      state'[response.mdest] = Leader, currentTerm'[response.mdest] = response.mterm
             PROVE \E prefix \in Seq(LogEntry):
                       /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log'[response.mdest])
                       /\ AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
    BY SMT DEF AcknowledgmentVoteCutHistory
<1>fields. response.msource \in Server /\ response.mdest \in Server /\ response.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>old. CASE response \in messages
    <2>continues. CASE state[response.mdest] = Leader
        <3>epoch. currentTerm[response.mdest] = response.mterm
            BY <1>base, <1>fields, <2>continues, ContinuingLeaderTermNext, SMT
        <3>prefix. PICK prefix \in Seq(LogEntry):
                /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log[response.mdest])
                /\ AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
            BY <1>old, <2>continues, <3>epoch, SMT DEF AcknowledgmentVoteCutHistory
        <3>owner. IsPrefix(prefix, log'[response.mdest])
            BY <1>base, <1>fields, <2>continues, <3>prefix, ContinuingLeaderPrefixNext, SMT
        <3>votes. AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
            BY <1>old, <2>continues, <3>epoch, <3>prefix, AcknowledgmentVoteCutsNext, SMT
        <3> QED BY <3>prefix, <3>owner, <3>votes, SMT
    <2>promoted. CASE state[response.mdest] # Leader
        <3>action. BecomeLeader(response.mdest)
            BY <1>base, <1>fields, <2>promoted, NewLeaderUsesBecomeLeader, SMT
        <3>candidate. state[response.mdest] = Candidate /\ currentTerm[response.mdest] = response.mterm
            BY <3>action, SMT DEF BecomeLeader
        <3> QED BY <1>base, <1>fields, <1>old, <3>candidate, CandidateHasNoCurrentAppendResponses, SMT
    <2> QED BY <2>continues, <2>promoted, SMT
<1>new. CASE response \notin messages
    <2>prefix. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ OwnerPrefix(request.msource, request.mterm, prefix)
            /\ Len(prefix) = response.mmatchIndex /\ IsPrefix(prefix, log'[response.msource])
        BY <1>base, <1>chosen, <1>consistent, <1>new, NewAcknowledgmentHasPhysicalPrefix, SMT
        DEF JointMembershipWitnesses
    <2>fields. request.msource \in Server /\ request.mterm \in Nat
        BY <1>base, <2>prefix, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
    <2>owner. OwnerPrefix(request.msource, request.mterm, prefix)'
        BY <1>base, <2>prefix, <2>fields, OwnerPrefixNext, SMT
    <2>sender. IsPrefix(prefix, log'[response.mdest])
        BY <2>prefix, <2>owner, SMT DEF ResponseMatchesRequest, OwnerPrefix
    <2>epoch. currentTerm'[response.msource] = response.mterm
        BY <1>base, <1>new, NewAcknowledgmentUsesPostTerm, SMT
    <2>votes. AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
        BY <1>base, <1>fields, <2>epoch, SMT
        DEF AcknowledgmentVoteCuts, RecordedCampaignVote, Grant, Started, SendInvariant,
            TypeOK, ServerVarsTypeOK
    <2> QED BY <2>prefix, <2>sender, <2>votes, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA ElectionMessagesFactsFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ElectionMessagesFrame
    PROVE /\ \A candidate, term, snapshot:
                 HistoryCampaignSnapshot(nextVoteHistory, candidate, term, snapshot)'
                     <=> HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
          /\ \A candidate, term:
                 Started(nextVoteHistory, candidate, term)' <=> Started(voteHistory, candidate, term)
          /\ \A voter, candidate, term:
                 Grant(voter, candidate, term)' <=> Grant(voter, candidate, term)
          /\ \A candidate, term:
                 RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
          /\ \A request:
                 request.mtype = RequestVoteRequest => (request \in messages' <=> request \in messages)
          /\ \A voter, candidate, term:
                 RecordedCampaignVote(nextVoteHistory, voter, candidate, term)'
                     <=> RecordedCampaignVote(voteHistory, voter, candidate, term)
<1>view. CampaignView(nextVoteHistory) = CampaignView(voteHistory)
    BY NoTimeoutKeepsCampaignView, SMT DEF ElectionMessagesFrame
<1>snapshots. \A candidate, term, snapshot:
        HistoryCampaignSnapshot(nextVoteHistory, candidate, term, snapshot)'
            <=> HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
    BY <1>view, CampaignSnapshotInView, SMT
<1>started. \A candidate, term:
        Started(nextVoteHistory, candidate, term)' <=> Started(voteHistory, candidate, term)
    BY <1>view, CampaignViewFramesStarted, SMT
<1>grants. \A voter, candidate, term:
        Grant(voter, candidate, term)' <=> Grant(voter, candidate, term)
    BY SMT DEF ElectionMessagesFrame, Grant
<1>requests. \A candidate, term:
        RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY SMT DEF ElectionMessagesFrame, RecordedCampaignRequests
<1>membership. \A request:
        request.mtype = RequestVoteRequest => (request \in messages' <=> request \in messages)
    BY SMT DEF ElectionMessagesFrame
<1>recorded. \A voter, candidate, term:
        RecordedCampaignVote(nextVoteHistory, voter, candidate, term)'
            <=> RecordedCampaignVote(voteHistory, voter, candidate, term)
    BY <1>started, <1>grants, SMT DEF RecordedCampaignVote
<1> QED BY <1>snapshots, <1>started, <1>grants, <1>requests, <1>membership, <1>recorded, SMT

LEMMA RetainedCertificateElectionMessagesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ElectionMessagesFrame, NEW candidate, NEW term, NEW snapshot,
           NEW occurrence, NEW support
    PROVE RetainedElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
          <=> RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY ElectionMessagesFactsFrame, SMT
    DEF RetainedElectionCertificate, CampaignRequests, VoteSupport, VoteFor,
        CampaignHistoryContextStep

LEMMA CurrentCertificateElectionMessagesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ElectionMessagesFrame, ContinuingLeadersKeepLogs,
           NEW leader \in Server, state'[leader] = Leader,
           NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    BY ElectionMessagesFactsFrame, SMT
    DEF ContinuingLeadersKeepLogs, CurrentElectionCertificate, CampaignRequests,
        VoteSupport, VoteFor, CampaignHistoryContextStep

LEMMA AppendReceiveElectionFrame ==
    ASSUME TypeOK, NEW request \in messages, request.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE /\ ElectionMessagesFrame /\ ContinuingLeadersKeepLogs
          /\ AppendRequests' = AppendRequests
<1>fields. request.mdest \in Server /\ request.msource \in Server
    BY StoredMessageFieldsTypeOK, SMT
<1>messages. ElectionMessagesFrame /\ AppendRequests' = AppendRequests
    BY UnchangedTermsExcludeTimeout, MessageTypesDistinct, SMT
    DEF ElectionMessagesFrame, AppendRequests, HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>leaders. ContinuingLeadersKeepLogs
    BY <1>fields, ServerStatesDistinct, SMT
    DEF ContinuingLeadersKeepLogs, HandleAppendEntriesRequest, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1> QED BY <1>messages, <1>leaders, SMT

LEMMA AppendReceiveLiveIntersections ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW request \in messages,
           request.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
          /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
          /\ CommitElectionIntersections(nextVoteHistory, commits)'
          /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
<1>base. TypeOK
    BY JointCoreBase, SMT
<1>frame. ElectionMessagesFrame /\ ContinuingLeadersKeepLogs /\ AppendRequests' = AppendRequests
    BY <1>base, AppendReceiveElectionFrame, SMT
<1>before.
        /\ LiveLeaderCertificateIntersections(voteHistory) /\ LiveAncestryCertificateIntersections(voteHistory, ancestry)
        /\ CommitElectionIntersections(voteHistory, commits) /\ CurrentRequestCertificateIntersections(voteHistory)
    BY SMT DEF MembershipJointCore, JointMembershipWitnesses
<1>leaders. LiveLeaderCertificateIntersections(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW left \in Server, NEW right \in Server, NEW term \in Nat,
                          NEW leftSnapshot \in Seq(LogEntry), NEW rightSnapshot \in Seq(LogEntry),
                          NEW leftOccurrence, NEW rightOccurrence, NEW leftSupport, NEW rightSupport,
                          CurrentElectionCertificate(nextVoteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)',
                          CurrentElectionCertificate(nextVoteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)'
                 PROVE leftSupport \cap rightSupport # {}
        BY SMT DEF LiveLeaderCertificateIntersections
    <2>left. CurrentElectionCertificate(voteHistory, left, term, leftSnapshot, leftOccurrence, leftSupport)
        BY <1>frame, CurrentCertificateElectionMessagesFrame, SMT DEF CurrentElectionCertificate
    <2>right. CurrentElectionCertificate(voteHistory, right, term, rightSnapshot, rightOccurrence, rightSupport)
        BY <1>frame, CurrentCertificateElectionMessagesFrame, SMT DEF CurrentElectionCertificate
    <2> QED BY <1>before, <2>left, <2>right, SMT DEF LiveLeaderCertificateIntersections
<1>ancestry. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY <1>before, <1>frame, CurrentCertificateElectionMessagesFrame, SMT
    DEF LiveAncestryCertificateIntersections, CurrentElectionCertificate
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>before, <1>frame, CurrentCertificateElectionMessagesFrame, SMT
    DEF CommitElectionIntersections,
        CurrentElectionCertificate, ContinuingLeadersKeepLogs
<1>requests. CurrentRequestCertificateIntersections(nextVoteHistory)'
    BY <1>before, <1>frame, CurrentCertificateElectionMessagesFrame, RetainedCertificateElectionMessagesFrame, SMT
    DEF CurrentRequestCertificateIntersections, ContinuingLeadersKeepLogs
<1> QED BY <1>leaders, <1>ancestry, <1>commits, <1>requests, SMT

\* A retained snapshot becomes canonical when its complete owner prefix is
\* still physically present at that owner in the same leadership term.
LEMMA OwnedElectionSnapshotMatchesCurrent ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), NEW leader \in Server, NEW term \in Nat,
           NEW entries \in Seq(LogEntry), NEW frozen \in Seq(LogEntry),
           NEW frozenOccurrence, NEW frozenSupport,
           OwnerPrefix(leader, term, entries), IsPrefix(frozen, entries),
           RetainedElectionCertificate(voteHistory, leader, term, frozen, frozenOccurrence, frozenSupport),
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    PROVE frozen = snapshot /\ frozenOccurrence = occurrence
<1>base.
        /\ TypeOK /\ log[leader] \in Seq(LogEntry) /\ TermsOrdered(log[leader])
        /\ IsPrefix(entries, log[leader])
    BY CampaignsSupplyEntryBounds, SMT
    DEF EntryEdgeBase, MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic,
        TermsOrdered, TypeOK, LogVarsTypeOK, OwnerPrefix, CurrentElectionCertificate
<1>captured. RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    BY CaptureCurrentElectionCertificate, SMT
<1>length. Len(frozen) = Len(snapshot)
    BY <1>captured, RetainedCampaignSnapshotLengthsEqual, SMT
<1>prefixes.
        /\ IsPrefix(frozen, log[leader]) /\ IsPrefix(snapshot, log[leader])
    BY <1>base, SequencePrefixTransitive, CampaignPrefixProperties, PreTermIndexProperties,
       WholeSequencePrefix, LenProperties, SMT
    DEF CurrentElectionCertificate, CampaignPrefix, IsPrefix
<1>same. frozen = snapshot
    BY <1>base, <1>length, <1>prefixes, PrefixesWithBoundedLength,
       WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
<1> QED BY <1>same, SMT DEF RetainedElectionCertificate, CurrentElectionCertificate

LEMMA LiveAncestryIdentifiesCurrentOwners ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW witness \in ancestry,
           NEW leader \in Server, state[leader] = Leader,
           witness.edge.term = currentTerm[leader]
    PROVE witness.owner = leader
<1>base. MembershipCampaignsInv(voteHistory) /\ VoteRecordInv(voteHistory) /\ currentTerm[leader] \in Nat
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
    BY <1>base, CurrentLeaderHasElectionCertificate, SMT
<1>votes.
        /\ witness.owner \in Server
        /\ VoteSupport(voteHistory, witness.owner, currentTerm[leader], witness.support)
        /\ VoteSupport(voteHistory, leader, currentTerm[leader], support)
        /\ witness.support \cap support # {}
    BY <1>campaign, SMT
    DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, WitnessPrefixData,
        RetainedElectionCertificate, CurrentElectionCertificate, LiveAncestryCertificateIntersections
<1> QED BY <1>base, <1>votes, IntersectingVoteSupportsUnique, SMT

LEMMA VoteRequestPreservesCurrentCertificate ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW request \in messages, request.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(request.mdest, request.msource, request),
           NEW leader \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>retained. RetainedElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
    BY <1>base, <1>next, CaptureCurrentElectionCertificate, RetainedElectionCertificateNext, SMT
<1> QED BY <1>retained, SMT
    DEF CurrentElectionCertificate, RetainedElectionCertificate, HandleRequestVoteRequest

LEMMA VoteRequestPreservesRequestIntersections ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW request \in messages, request.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(request.mdest, request.msource, request)
    PROVE CurrentRequestCertificateIntersections(nextVoteHistory)'
<1>base. MembershipCampaignsInv(voteHistory) /\ TypeOK
    BY JointCoreBase, SMT
<1>owners. CurrentRequestSendersUnique
    BY <1>base, IntersectingRequestCertificatesIdentifySenders, SMT DEF MembershipJointCore
<1>append_requests. AppendRequests' = AppendRequests
    BY MessageTypesDistinct, SMT
    DEF AppendRequests, HandleRequestVoteRequest, Send, WithMessage, WithMessages
<1> SUFFICES ASSUME NEW leader \in Server, NEW append \in AppendRequests',
                      state'[leader] = Leader, append.mterm = currentTerm'[leader]
             PROVE \E leaderSnapshot, requestSnapshot \in Seq(LogEntry):
                   \E leaderOccurrence, requestOccurrence, leaderSupport, requestSupport:
                       /\ CurrentElectionCertificate(nextVoteHistory, leader, append.mterm,
                               leaderSnapshot, leaderOccurrence, leaderSupport)'
                       /\ RetainedElectionCertificate(nextVoteHistory, append.msource, append.mterm,
                               requestSnapshot, requestOccurrence, requestSupport)'
                       /\ leaderSupport \cap requestSupport # {}
    BY SMT DEF CurrentRequestCertificateIntersections
<1>before.
        /\ state[leader] = Leader /\ append.mterm = currentTerm[leader]
        /\ append.mterm \in Nat /\ append.msource = leader
    BY <1>base, <1>owners, <1>append_requests, SMT
    DEF CurrentRequestSendersUnique, HandleRequestVoteRequest, TypeOK, ServerVarsTypeOK
<1>campaign. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, leader, append.mterm, snapshot, occurrence, support)
    BY <1>base, <1>before, CurrentLeaderHasElectionCertificate, SMT
<1>after. CurrentElectionCertificate(nextVoteHistory, leader, append.mterm, snapshot, occurrence, support)'
    BY <1>before, <1>campaign, VoteRequestPreservesCurrentCertificate, SMT
<1>captured. RetainedElectionCertificate(nextVoteHistory, leader, append.mterm, snapshot, occurrence, support)'
    BY <1>before, <1>after, SMT
    DEF RetainedElectionCertificate, CurrentElectionCertificate, HandleRequestVoteRequest
<1>nonempty. support # {}
    BY <1>campaign, ConfigurationQuorumNonempty, SMT DEF CurrentElectionCertificate
<1> QED BY <1>before, <1>campaign, <1>after, <1>captured, <1>nonempty, SMT

LEMMA PostUniqueLeadersHaveIntersectingCertificates ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipElectionSafety'
    PROVE LiveLeaderCertificateIntersections(nextVoteHistory)'
    BY ServerOK, FiniteSetSubsetsAreFinite, SameConfigurationQuorumsIntersect, SMT
    DEF MembershipElectionSafety, LiveLeaderCertificateIntersections, CurrentElectionCertificate

LEMMA VoteRequestPreservesLeaderIntersections ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW request \in messages, request.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(request.mdest, request.msource, request)
    PROVE LiveLeaderCertificateIntersections(nextVoteHistory)'
<1>safety. MembershipElectionSafety'
    BY JointCoreImpliesElectionSafety, SMT DEF MembershipElectionSafety, HandleRequestVoteRequest
<1> QED BY <1>safety, PostUniqueLeadersHaveIntersectingCertificates, SMT

LEMMA AppendReceivePreservesCommitProtection ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW request \in messages,
           request.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE CommitLeaderProtection(commits)' /\ JointCommitProtection(ancestry, commits)'
<1>base. TypeOK
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1>frame. ContinuingLeadersKeepLogs /\ AppendRequests' = AppendRequests
    BY <1>base, AppendReceiveElectionFrame, SMT
<1>leaders. CommitLeaderProtection(commits)'
    BY <1>frame, SMT DEF JointMembershipWitnesses, CommitLeaderProtection, ContinuingLeadersKeepLogs
<1>protection. JointCommitProtection(ancestry, commits)'
    <2> SUFFICES ASSUME NEW certificate \in commits
                 PROVE /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)'
                       /\ ProtectedAppendRequests(CommitTarget(certificate), certificate.term)'
                       /\ ProtectedLeaders(CommitTarget(certificate), certificate.term)'
                       /\ RecordedAcknowledgersProtected(certificate.leader, certificate.term, CommitTarget(certificate))'
        BY SMT DEF JointCommitProtection
    <2>data.
            /\ RetainedCommitCertificate(voteHistory, certificate)
            /\ CommitTarget(certificate) \in Seq(LogEntry) /\ certificate.term \in Nat
            /\ Len(CommitTarget(certificate)) > 0
            /\ LastTerm(CommitTarget(certificate)) = certificate.term
        BY CommitCertificateTargetProperties, LenProperties, SMT
        DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate, LastTerm
    <2>history. TargetHistory(voteHistory, ancestry, CommitTarget(certificate), certificate.term)
        BY <2>data, SMT DEF TargetHistory, JointMembershipWitnesses, JointCommitProtection
    <2>campaign. TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
        BY <2>data, CommitCertificateSuppliesTargetCampaignEvidence, SMT
    <2>holders. RecordedAcknowledgersProtected(certificate.leader, certificate.term, CommitTarget(certificate))'
        BY <1>next, <2>data, <2>history, <2>campaign, RecordedAcknowledgersProtectedNext, SMT
        DEF MembershipJointCore, JointMembershipWitnesses, JointCommitProtection, RetainedCommitCertificate
    <2> QED BY <1>frame, <2>holders, SMT
        DEF JointMembershipWitnesses, JointCommitProtection, ProtectedAppendRequests,
            ProtectedLeaders, ContinuingLeadersKeepLogs
<1> QED BY <1>leaders, <1>protection, SMT

LEMMA CommitCertificateStateFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, UNCHANGED <<log, messages, state, currentTerm>>, NEW certificate
    PROVE RetainedCommitCertificate(nextVoteHistory, certificate)' <=> RetainedCommitCertificate(voteHistory, certificate)
    BY UnchangedLogsAndTermsKeepSelectedHistory, ElectionCertificateMessagesFrame, SMT
    DEF RetainedCommitCertificate, RecordedPrefixAcknowledgment, OwnerPrefix

LEMMA ElectionCertificateBeforeTimeout ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipCampaignsInv(voteHistory), NEW actor \in Server, Timeout(actor),
           NEW candidate \in Server, NEW term \in Nat, term <= currentTerm[candidate],
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           RetainedElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    PROVE /\ RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
          /\ term <= currentTerm[candidate]
<1>base. TypeOK /\ SendInvariant /\ CampaignHistory(voteHistory)
    BY CampaignsSupplyEntryBounds, SMT DEF EntryEdgeBase, MembershipCampaignsInv, MembershipVotesInv
<1>history. HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
    BY <1>base, SMT
    DEF RetainedElectionCertificate, HistoryCampaignSnapshot, CampaignHistoryContextStep,
        CampaignHistoryStep, Timeout, TypeOK, ServerVarsTypeOK
<1>requests. RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY <1>base, HistoricalCampaignRequestsAreFixed, SMT DEF Next
<1>votes. VoteSupport(voteHistory, candidate, term, support)
    BY <1>base, <1>history, TimeoutGrantUnchanged, SMT
    DEF RetainedElectionCertificate, VoteSupport, VoteFor, Started, HistoryCampaignSnapshot
<1> QED BY <1>base, <1>history, <1>requests, <1>votes, SMT
    DEF RetainedElectionCertificate, RecordedCampaignRequests

LEMMA TimeoutCurrentCertificatesFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, Timeout(actor), NEW leader \in Server,
           NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE CurrentElectionCertificate(nextVoteHistory, leader, term, snapshot, occurrence, support)'
          <=> CurrentElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
<1>self. CASE leader = actor
    BY <1>self, ServerStatesDistinct, SMT
    DEF Timeout, CurrentElectionCertificate, TypeOK, ServerVarsTypeOK
<1>other. CASE leader # actor
    <2>frame.
            /\ state'[leader] = state[leader]
            /\ currentTerm'[leader] = currentTerm[leader]
            /\ log'[leader] = log[leader]
        BY <1>other, SMT DEF Timeout, TypeOK, ServerVarsTypeOK
    <2>history. HistoryCampaignSnapshot(nextVoteHistory, leader, term, snapshot)'
            <=> HistoryCampaignSnapshot(voteHistory, leader, term, snapshot)
        BY <1>other, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, HistoryCampaignSnapshot,
            Timeout, TypeOK, ServerVarsTypeOK
    <2>started. Started(nextVoteHistory, leader, term)' <=> Started(voteHistory, leader, term)
        BY <1>other, <2>frame, SMT
        DEF Started, CampaignHistoryContextStep, CampaignHistoryStep, Timeout,
            TypeOK, ServerVarsTypeOK
    <2>grants. \A voter, candidate, voteTerm:
            Grant(voter, candidate, voteTerm)' <=> Grant(voter, candidate, voteTerm)
        BY TimeoutGrantUnchanged, SMT
    <2>messages. \A request:
            request.msource = leader => (request \in messages' <=> request \in messages)
        BY <1>other, SMT DEF Timeout, WithMessages, RequestVoteRequests
    <2>requests. RecordedCampaignRequests(leader, term)' = RecordedCampaignRequests(leader, term)
        BY <1>other, SMT
        DEF RecordedCampaignRequests, Timeout, WithMessages, RequestVoteRequests
    <2> QED BY <2>frame, <2>history, <2>started, <2>grants, <2>messages, <2>requests, SMT
        DEF CurrentElectionCertificate, VoteSupport, VoteFor, CampaignRequests,
            CampaignHistoryContextStep
<1> QED BY <1>self, <1>other, SMT

LEMMA TimeoutAppendEvidenceFrame ==
    ASSUME NEW actor \in Server, Timeout(actor)
    PROVE /\ AppendRequests' = AppendRequests
          /\ \A voter, leader, term, index:
                 RecordedAcknowledgment(voter, leader, term, index)'
                 <=> RecordedAcknowledgment(voter, leader, term, index)
    BY MessageTypesDistinct, SMT
    DEF AppendRequests, RecordedAcknowledgment, SuccessfulAppendResponse,
        Timeout, WithMessages, RequestVoteRequests

LEMMA PrefixAcknowledgmentBeforeTimeout ==
    ASSUME NEW voteHistory, ReplicationPrefixInv(voteHistory), CandidateAppendFree, NEW actor \in Server, Timeout(actor),
           NEW voter \in Server, NEW leader \in Server, NEW term \in Nat,
           NEW target \in Seq(LogEntry), RecordedPrefixAcknowledgment(voter, leader, term, target)'
    PROVE RecordedPrefixAcknowledgment(voter, leader, term, target)
<1>base. TypeOK /\ SendInvariant /\ SuccessfulResponseOriginInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv, EntryEdgeBase
<1>frozen. PICK response, request, prefix:
        /\ response \in messages' /\ request \in messages' /\ prefix \in Seq(LogEntry)
        /\ SuccessfulAppendResponse(response)
        /\ response.msource = voter /\ response.mdest = leader
        /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
        /\ ResponseMatchesRequest(response, request)
        /\ RequestPrefixData(request, prefix) /\ OwnerPrefix(leader, term, prefix)'
        /\ IsPrefix(target, prefix)
    BY SMT DEF RecordedPrefixAcknowledgment
<1>old. response \in messages /\ request \in messages
    BY <1>frozen, MessageTypesDistinct, SMT
    DEF SuccessfulAppendResponse, ResponseMatchesRequest, Timeout, WithMessages, RequestVoteRequests
<1>bound. term <= currentTerm[leader]
    BY <1>base, <1>frozen, <1>old, SMT DEF SendInvariant, ResponseMatchesRequest
<1>candidate. CASE state[leader] = Candidate /\ currentTerm[leader] = term
    BY <1>base, <1>frozen, <1>old, <1>candidate, CandidateHasNoCurrentAppendResponses, SMT
<1>other. CASE ~(state[leader] = Candidate /\ currentTerm[leader] = term)
    <2>owner. OwnerPrefix(leader, term, prefix)
        BY <1>base, <1>frozen, <1>bound, <1>other, ServerStatesDistinct, SMT
        DEF OwnerPrefix, Timeout, TypeOK, ServerVarsTypeOK
    <2> QED BY <1>frozen, <1>old, <2>owner, SMT DEF RecordedPrefixAcknowledgment
<1> QED BY <1>candidate, <1>other, SMT

LEMMA PresentCommitCertificateBeforeTimeout ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), CandidateAppendFree, NEW actor \in Server, Timeout(actor),
           NEW certificate, RetainedCommitCertificate(nextVoteHistory, certificate)',
           certificate.index = Len(certificate.entries),
           IsPrefix(certificate.entries, log'[certificate.leader])
    PROVE RetainedCommitCertificate(voteHistory, certificate)
<1>base. MembershipCampaignsInv(voteHistory) /\ TypeOK /\ LogStructureInv
    BY CampaignsSupplyEntryBounds, SMT
    DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, EntryEdgeBase
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry) /\ certificate.snapshot \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>term_bound. certificate.term <= currentTerm[certificate.leader]
    BY <1>base, <1>data, PrefixEntryEqual, LenProperties, SMT
    DEF RetainedCommitCertificate, MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic,
        MembershipVotesInv, MembershipStructureInv, LogStructureInv, EntryStructure, LogTermBoundInv,
        IsPrefix, Timeout, TypeOK, LogVarsTypeOK
<1>election.
        /\ RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
                certificate.snapshot, certificate.electionOccurrence, certificate.election)
        /\ certificate.term <= currentTerm[certificate.leader]
    BY <1>base, <1>data, <1>term_bound, ElectionCertificateBeforeTimeout, SMT DEF RetainedCommitCertificate
<1>owner. OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    BY <1>election, SMT DEF OwnerPrefix, Timeout
<1>target. CommitTarget(certificate) = certificate.entries
    BY <1>data, WholeSequencePrefix, SMT DEF CommitTarget
<1>acks. \A voter \in certificate.replication \ {certificate.leader}:
        RecordedPrefixAcknowledgment(voter, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>data, <1>target, PrefixAcknowledgmentBeforeTimeout, SMT
    DEF RetainedCommitCertificate, Quorums
<1> QED BY <1>election, <1>owner, <1>acks, SMT
    DEF RetainedCommitCertificate, LocalAppendOrigin, LocalAppendRecord, CampaignHistoryContextStep, CampaignHistoryStep

LEMMA TimeoutPreservesEvidenceTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), ReplicationPrefixInv(voteHistory), CandidateAppendFree, NEW actor \in Server, Timeout(actor)
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
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, Timeout
<1>reverse. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory)
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)' PROVE target \in EvidenceAgreementTargets(voteHistory)
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log'[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>before. RetainedCommitCertificate(voteHistory, certificate)
        BY <2>certificate, PresentCommitCertificateBeforeTimeout, SMT
    <2> QED BY <2>certificate, <2>before, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, Timeout
<1> QED BY <1>forward, <1>reverse, SMT

LEMMA LiveIntersectionsTimeout ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server, Timeout(actor)
    PROVE /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
          /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
          /\ CommitElectionIntersections(nextVoteHistory, commits)'
          /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next
<1>leaders. LiveLeaderCertificateIntersections(nextVoteHistory)'
    BY <1>base, TimeoutCurrentCertificatesFrame, SMT
    DEF MembershipJointCore, LiveLeaderCertificateIntersections
<1>ancestry. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY <1>base, TimeoutCurrentCertificatesFrame, SMT
    DEF JointMembershipWitnesses, LiveAncestryCertificateIntersections
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>base, TimeoutCurrentCertificatesFrame, SMT
    DEF JointMembershipWitnesses, CommitElectionIntersections, CurrentElectionCertificate
<1>requests. CurrentRequestCertificateIntersections(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW leader \in Server, NEW request \in AppendRequests',
                          state'[leader] = Leader, request.mterm = currentTerm'[leader]
                 PROVE \E leaderSnapshot, requestSnapshot \in Seq(LogEntry):
                       \E leaderOccurrence, requestOccurrence, leaderSupport, requestSupport:
                           /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm,
                                   leaderSnapshot, leaderOccurrence, leaderSupport)'
                           /\ RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                                   requestSnapshot, requestOccurrence, requestSupport)'
                           /\ leaderSupport \cap requestSupport # {}
        BY SMT DEF CurrentRequestCertificateIntersections
    <2>before.
            /\ state[leader] = Leader /\ request.mterm = currentTerm[leader]
            /\ request \in AppendRequests
        BY <1>base, TimeoutAppendEvidenceFrame, ServerStatesDistinct, SMT
        DEF Timeout, TypeOK, ServerVarsTypeOK
    <2>pair. PICK leaderSnapshot, requestSnapshot, leaderOccurrence, requestOccurrence,
                  leaderSupport, requestSupport:
            /\ leaderSnapshot \in Seq(LogEntry) /\ requestSnapshot \in Seq(LogEntry)
            /\ CurrentElectionCertificate(voteHistory, leader, request.mterm,
                    leaderSnapshot, leaderOccurrence, leaderSupport)
            /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                    requestSnapshot, requestOccurrence, requestSupport)
            /\ leaderSupport \cap requestSupport # {}
        BY <2>before, SMT DEF MembershipJointCore, CurrentRequestCertificateIntersections
    <2>types. request.msource \in Server /\ request.mterm \in Nat
        BY <2>pair, SMT DEF RetainedElectionCertificate
    <2>after.
            /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm,
                    leaderSnapshot, leaderOccurrence, leaderSupport)'
            /\ RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                    requestSnapshot, requestOccurrence, requestSupport)'
        BY <1>base, <1>next, <2>pair, <2>types, TimeoutCurrentCertificatesFrame,
           RetainedElectionCertificateNext, SMT
    <2> QED BY <2>pair, <2>after, SMT
<1> QED BY <1>leaders, <1>ancestry, <1>commits, <1>requests, SMT

LEMMA JointProtectionTimeout ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW actor \in Server, Timeout(actor)
    PROVE /\ JointCommitProtection(ancestry, commits)'
          /\ JointEvidenceProtection(nextVoteHistory, ancestry)'
          /\ CommitLeaderProtection(commits)'
<1>base. TypeOK
    BY JointCoreBase, SMT
<1>targets. EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
    BY TimeoutPreservesEvidenceTargets, SMT DEF MembershipJointCore
<1> QED BY <1>base, <1>targets, TimeoutAppendEvidenceFrame, ServerStatesDistinct, SMT
    DEF JointMembershipWitnesses, JointCommitProtection, JointEvidenceProtection,
        CommitLeaderProtection, ProtectedAppendRequests, ProtectedLeaders,
        RecordedAcknowledgersProtected, RecordedReplicationSupport, ProtectedVoters,
        Timeout, TypeOK, ServerVarsTypeOK

LEMMA CurrentCertificateIsReady ==
    ASSUME NEW voteHistory, NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           CurrentElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY CaptureCurrentElectionCertificate, SMT DEF ReadyElectionCertificate, CurrentElectionCertificate

LEMMA PostCurrentCertificateIsReady ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           CurrentElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    PROVE ReadyElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    BY SMT DEF ReadyElectionCertificate, CurrentElectionCertificate, RetainedElectionCertificate

LEMMA ReadyCertificatesAtPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, BecomeLeader(actor), NEW candidate \in Server,
           NEW term, NEW snapshot, NEW occurrence, NEW support
    PROVE ReadyElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
          <=> ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY UnchangedTermsKeepCampaignHistory, ElectionCertificateMessagesFrame, ServerStatesDistinct, SMT
    DEF ReadyElectionCertificate, BecomeLeader, TypeOK, ServerVarsTypeOK

LEMMA WinningCandidateHasReadyCertificate ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), NEW actor \in Server, BecomeLeader(actor)
    PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
              ReadyElectionCertificate(voteHistory, actor, currentTerm[actor], snapshot, occurrence, support)
<1>base.
        /\ TypeOK /\ currentTerm[actor] \in Nat /\ log[actor] \in Seq(LogEntry)
        /\ state[actor] = Candidate
    BY CampaignsSupplyEntryBounds, SMT
    DEF EntryEdgeBase, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        TypeOK, ServerVarsTypeOK, LogVarsTypeOK, BecomeLeader
<1>snapshot. CampaignPrefix(log[actor], currentTerm[actor]) = log[actor]
    BY <1>base, CampaignPrefixBeforeTerm, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        MembershipElectionBase, CandidateCurrentTermFree
<1> DEFINE snapshot == log[actor]
           occurrence == LatestConfigurationOccurrence(snapshot)
           support == votesGranted[actor] \cap LastConfiguration(actor)
<1>configuration.
        /\ occurrence.members = LastConfiguration(actor)
        /\ occurrence.members \subseteq Server /\ occurrence.members # {}
        /\ support \in Quorums(occurrence.members)
    BY <1>base, ConfigurationType, SMT
    DEF snapshot, occurrence, support, LatestConfigurationOccurrence, LastConfiguration, BecomeLeader
<1>votes. VoteSupport(voteHistory, actor, currentTerm[actor], support)
    BY <1>base, SMT DEF support, MembershipCampaignsInv, MembershipVotesInv,
        VoteSupport, ActiveVotesInv, BecomeLeader, TypeOK, CandidateVarsTypeOK
<1>peers. \A voter \in support \ {actor}:
        \E request \in CampaignRequests(actor, currentTerm[actor], snapshot):
            /\ request \in messages /\ request.mdest = voter
    BY <1>base, <1>snapshot, <1>votes, PositivePeerGrantHasCampaignRequest, SMT
    DEF MembershipCampaignsInv, VoteSupport, VoteFor, snapshot
<1> QED BY <1>base, <1>snapshot, <1>configuration, <1>votes, <1>peers, SMT
    DEF ReadyElectionCertificate, RetainedElectionCertificate, MembershipCampaignsInv,
        CampaignSnapshotInv, MembershipVotesInv, MembershipStructureInv,
        MembershipElectionBase, CandidateCurrentTermFree,
        snapshot, occurrence, CampaignHistory, HistoryCampaignSnapshot

LEMMA PromotedLeadersWereReady ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW actor \in Server, BecomeLeader(actor),
           NEW leader \in Server, state'[leader] = Leader
    PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
              ReadyElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
<1>base. MembershipCampaignsInv(voteHistory) /\ TypeOK /\ currentTerm[leader] \in Nat
    BY JointCoreBase, SMT DEF TypeOK, ServerVarsTypeOK
<1>new. CASE leader = actor
    BY <1>base, <1>new, WinningCandidateHasReadyCertificate, SMT
<1>old. CASE leader # actor
    <2>before. state[leader] = Leader
        BY <1>base, <1>old, SMT DEF BecomeLeader, TypeOK, ServerVarsTypeOK
    <2>certificate. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ CurrentElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
        BY <1>base, <2>before, CurrentLeaderHasElectionCertificate, SMT
    <2> QED BY <1>base, <2>certificate, CurrentCertificateIsReady, SMT
<1> QED BY <1>new, <1>old, SMT

LEMMA CurrentAfterPromotionWasReady ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, BecomeLeader(actor), NEW candidate \in Server,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           CurrentElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    PROVE ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY ReadyCertificatesAtPromotion, PostCurrentCertificateIsReady, SMT

LEMMA ReadyBecomesCurrentAtPromotion ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW actor \in Server, BecomeLeader(actor), NEW candidate \in Server,
           state'[candidate] = Leader, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE CurrentElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    BY ReadyCertificatesAtPromotion, SMT
    DEF ReadyElectionCertificate, CurrentElectionCertificate, RetainedElectionCertificate

LEMMA PromotionAdmitsLiveRelations ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointCandidateWitnesses(voteHistory, ancestry, commits), NEW actor \in Server, BecomeLeader(actor)
    PROVE /\ LiveLeaderCertificateIntersections(nextVoteHistory)'
          /\ CurrentRequestCertificateIntersections(nextVoteHistory)'
          /\ LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
          /\ CommitElectionIntersections(nextVoteHistory, commits)'
<1>base. TypeOK
    BY JointCoreBase, SMT
<1>leaders. LiveLeaderCertificateIntersections(nextVoteHistory)'
    BY <1>base, CurrentAfterPromotionWasReady, SMT
    DEF JointCandidateWitnesses, ReadyMembershipRelations, ReadyElectionIntersections,
        LiveLeaderCertificateIntersections
<1>ancestry. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY <1>base, CurrentAfterPromotionWasReady, SMT
    DEF JointCandidateWitnesses, ReadyMembershipRelations,
        ReadyAncestryIntersections, LiveAncestryCertificateIntersections
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY <1>base, CurrentAfterPromotionWasReady, SMT
    DEF JointCandidateWitnesses, ReadyMembershipRelations, ReadyCommitIntersections,
        CommitElectionIntersections, CurrentElectionCertificate, BecomeLeader, TypeOK, ServerVarsTypeOK
<1>requests. CurrentRequestCertificateIntersections(nextVoteHistory)'
    <2> SUFFICES ASSUME NEW leader \in Server, NEW request \in AppendRequests',
                          state'[leader] = Leader, request.mterm = currentTerm'[leader]
                 PROVE \E leaderSnapshot, requestSnapshot \in Seq(LogEntry):
                       \E leaderOccurrence, requestOccurrence, leaderSupport, requestSupport:
                           /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm,
                                   leaderSnapshot, leaderOccurrence, leaderSupport)'
                           /\ RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                                   requestSnapshot, requestOccurrence, requestSupport)'
                           /\ leaderSupport \cap requestSupport # {}
        BY SMT DEF CurrentRequestCertificateIntersections
    <2>before. request \in AppendRequests /\ request.mterm = currentTerm[leader] /\ request.mterm \in Nat
        BY <1>base, SMT DEF AppendRequests, BecomeLeader, TypeOK, ServerVarsTypeOK
    <2>ready. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ ReadyElectionCertificate(voteHistory, leader, request.mterm, snapshot, occurrence, support)
        BY <2>before, PromotedLeadersWereReady, SMT
    <2>pair. PICK requestSnapshot, requestOccurrence, requestSupport:
            /\ requestSnapshot \in Seq(LogEntry)
            /\ RetainedElectionCertificate(voteHistory, request.msource, request.mterm,
                    requestSnapshot, requestOccurrence, requestSupport)
            /\ support \cap requestSupport # {}
        BY <2>before, <2>ready, SMT
        DEF JointCandidateWitnesses, ReadyMembershipRelations, ReadyRequestIntersections
    <2>after.
            /\ CurrentElectionCertificate(nextVoteHistory, leader, request.mterm, snapshot, occurrence, support)'
            /\ RetainedElectionCertificate(nextVoteHistory, request.msource, request.mterm,
                    requestSnapshot, requestOccurrence, requestSupport)'
        BY <1>base, <2>before, <2>ready, <2>pair, ReadyBecomesCurrentAtPromotion,
           UnchangedTermsKeepCampaignHistory, ElectionCertificateMessagesFrame, SMT DEF BecomeLeader
    <2> QED BY <2>ready, <2>pair, <2>after, SMT
<1> QED BY <1>leaders, <1>ancestry, <1>commits, <1>requests, SMT

LEMMA PromotionPreservesReadyPrefixes ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointCandidateWitnesses(voteHistory, ancestry, commits), NEW actor \in Server, BecomeLeader(actor)
    PROVE /\ CommitLeaderProtection(commits)'
          /\ \A certificate \in commits: ProtectedLeaders(CommitTarget(certificate), certificate.term)'
          /\ \A target \in EvidenceAgreementTargets(voteHistory): ProtectedLeaders(target, LastTerm(target))'
<1>base. TypeOK
    BY JointCoreBase, SMT
<1>holders. \A leader \in Server:
        state'[leader] = Leader =>
            /\ \A certificate \in commits:
                   certificate.term <= currentTerm'[leader] =>
                       IsPrefix(CommitTarget(certificate), log'[leader])
            /\ \A target \in EvidenceAgreementTargets(voteHistory):
                   LastTerm(target) <= currentTerm'[leader] => IsPrefix(target, log'[leader])
    <2> SUFFICES ASSUME NEW leader \in Server, state'[leader] = Leader
                 PROVE /\ \A certificate \in commits:
                              certificate.term <= currentTerm'[leader] =>
                                  IsPrefix(CommitTarget(certificate), log'[leader])
                       /\ \A target \in EvidenceAgreementTargets(voteHistory):
                              LastTerm(target) <= currentTerm'[leader] => IsPrefix(target, log'[leader])
        BY SMT
    <2>ready. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ ReadyElectionCertificate(voteHistory, leader, currentTerm[leader], snapshot, occurrence, support)
        BY PromotedLeadersWereReady, SMT
    <2>epoch. currentTerm[leader] \in Nat /\ currentTerm'[leader] = currentTerm[leader]
        BY <1>base, SMT DEF TypeOK, ServerVarsTypeOK, BecomeLeader
    <2> QED BY <2>ready, <2>epoch, SMT
        DEF JointCandidateWitnesses, ReadyMembershipRelations, ReadyCommitPrefixes,
            ReadyEvidencePrefixes, BecomeLeader
<1> QED BY <1>holders, SMT DEF CommitLeaderProtection, ProtectedLeaders

LEMMA AssembleCandidateWitnessesAfter ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK', NEW ancestry, NEW commits, JointWitnessMetadata(nextVoteHistory, ancestry, commits)',
           ReadyMembershipRelations(nextVoteHistory, ancestry, commits)',
           JointCommitProtection(ancestry, commits)', JointEvidenceProtection(nextVoteHistory, ancestry)'
    PROVE JointCandidateWitnesses(nextVoteHistory, ancestry, commits)'
<1>ancestry. LiveAncestryCertificateIntersections(nextVoteHistory, ancestry)'
    BY PostCurrentCertificateIsReady, SMT
    DEF ReadyMembershipRelations, ReadyAncestryIntersections, LiveAncestryCertificateIntersections
<1>commits. CommitElectionIntersections(nextVoteHistory, commits)'
    BY PostCurrentCertificateIsReady, SMT
    DEF ReadyMembershipRelations, ReadyCommitIntersections, CommitElectionIntersections,
        TypeOK, ServerVarsTypeOK
<1>leaders. CommitLeaderProtection(commits)'
    BY SMT DEF JointCommitProtection, CommitLeaderProtection, ProtectedLeaders
<1> QED BY <1>ancestry, <1>commits, <1>leaders, SMT
    DEF JointCandidateWitnesses, JointMembershipWitnesses, JointWitnessMetadata

LEMMA CandidateRetirementFrames ==
    ASSUME TypeOK, CandidateRetirementAction
    PROVE JointRetirementFrame /\ ActiveCampaignsRetire
    BY ServerStatesDistinct, StoredMessageFieldsTypeOK, SMT
    DEF CandidateRetirementAction, JointRetirementFrame, ActiveCampaignsRetire,
        vars, Restart, LeaderStepDown, AdvanceCommitIndex, UpdateTerm,
        HandleRequestVoteResponse, HandleAppendEntriesResponse,
        TypeOK, ServerVarsTypeOK, LogVarsTypeOK


LEMMA JointMetadataWithoutNewCommit ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits),
           HistoricalEntryEdges' \subseteq HistoricalEntryEdges, UNCHANGED commitIndex
    PROVE JointWitnessMetadata(nextVoteHistory, ancestry, commits)'
<1>base. TypeOK /\ SendInvariant /\ ReplicationEvidenceInv(voteHistory) /\ NextIndexBound /\ TypeOK'
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, EntryEdgeBase, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv,
        MembershipStructureInv, ReplicationBoundsInv
<1>retained.
        /\ CertificateFamily(nextVoteHistory, ancestry)' /\ RequestPrefixAncestry(nextVoteHistory, ancestry)'
        /\ CommitCertificateFamily(nextVoteHistory, commits)' /\ AdvertisedCommitEvidence(commits)'
    BY <1>base, CertificateFamilyNext, RequestPrefixAncestryNext,
       CommitCertificateFamilyNext, AdvertisedCommitEvidenceNext, SMT DEF JointMembershipWitnesses
<1>local. LocalCommitEvidence(commits)'
    BY <1>base, LocalCommitEvidenceWithoutLeaderAdvance, SMT DEF JointMembershipWitnesses
<1> QED BY <1>retained, <1>local, SMT
    DEF JointWitnessMetadata, JointMembershipWitnesses, CoversEntryEdges

LEMMA ReadyAppendReceiveFrame ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK, NEW request \in messages, request.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE NoNewReadyCertificates(voteHistory, nextVoteHistory) /\ ActiveLogsExtend
<1>fields. request.mdest \in Server /\ request.msource \in Server
    BY StoredMessageFieldsTypeOK, SMT
<1>active. \A candidate \in Server:
        state'[candidate] \in {Candidate, Leader} =>
            /\ state[candidate] \in {Candidate, Leader}
            /\ currentTerm'[candidate] = currentTerm[candidate]
            /\ log'[candidate] = log[candidate]
    BY <1>fields, ServerStatesDistinct, SMT
    DEF HandleAppendEntriesRequest, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>messages. ElectionMessagesFrame
    BY AppendReceiveElectionFrame, SMT
<1>ready. NoNewReadyCertificates(voteHistory, nextVoteHistory)
    BY <1>active, <1>messages, RetainedCertificateElectionMessagesFrame, SMT
    DEF NoNewReadyCertificates, ReadyElectionCertificate
<1>logs. ActiveLogsExtend
    BY <1>active, WholeSequencePrefix, LenProperties, SMT
    DEF ActiveLogsExtend, IsPrefix, TypeOK, LogVarsTypeOK
<1> QED BY <1>ready, <1>logs, SMT

LEMMA VoteRequestSnapshotLengthsAgree ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW request \in messages, request.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(request.mdest, request.msource, request),
           NEW candidate \in Server, NEW term \in Nat,
           NEW oldSnapshot \in Seq(LogEntry), NEW newSnapshot \in Seq(LogEntry),
           NEW oldOccurrence, NEW newOccurrence, NEW oldSupport, NEW newSupport,
           RetainedElectionCertificate(voteHistory, candidate, term, oldSnapshot, oldOccurrence, oldSupport),
           RetainedElectionCertificate(nextVoteHistory, candidate, term, newSnapshot, newOccurrence, newSupport)'
    PROVE Len(oldSnapshot) = Len(newSnapshot)
    BY GrowingCampaignHistoriesKeepSnapshots, LenProperties, SMT
    DEF RetainedElectionCertificate

LEMMA VoteRequestPrefixAcknowledgmentsFrame ==
    ASSUME NEW request \in messages, request.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(request.mdest, request.msource, request),
           NEW peer, NEW leader, NEW term, NEW target
    PROVE RecordedPrefixAcknowledgment(peer, leader, term, target)'
          <=> RecordedPrefixAcknowledgment(peer, leader, term, target)
    BY MessageTypesDistinct, SMT
    DEF RecordedPrefixAcknowledgment, SuccessfulAppendResponse, ResponseMatchesRequest,
        OwnerPrefix, HandleRequestVoteRequest, Send, WithMessage, WithMessages

\* A peer acknowledgment supplies an earlier election certificate. The
\* canonical snapshot attached to its frozen request is anchored in the same
\* ancestry as the physically present target, even for an inactive sender.
LEMMA PresentAgreementHasPreexistingElection ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW vote \in messages,
           vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote), NEW certificate,
           RetainedCommitCertificate(nextVoteHistory, certificate)', certificate.index = Len(certificate.entries),
           IsPrefix(certificate.entries, log'[certificate.leader])
    PROVE \E support:
              RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
                  certificate.snapshot, certificate.electionOccurrence, support)
<1>base.
        /\ TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
        /\ CoversEntryEdges(ancestry, HistoricalEntryEdges) /\ RequestPrefixAncestry(voteHistory, ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry) /\ certificate.snapshot \in Seq(LogEntry)
        /\ Len(certificate.entries) > 0 /\ LastTerm(certificate.entries) = certificate.term
        /\ Len(certificate.snapshot) < Len(certificate.entries)
        /\ IsPrefix(certificate.snapshot, certificate.entries)
        /\ IsPrefix(certificate.entries, log[certificate.leader])
        /\ log[certificate.leader] \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    <2>fields.
            /\ certificate.leader \in Server /\ certificate.term \in Nat
            /\ certificate.entries \in Seq(LogEntry) /\ certificate.snapshot \in Seq(LogEntry)
            /\ certificate.index \in 1..Len(certificate.entries)
            /\ certificate.entries[certificate.index].term = certificate.term
            /\ Len(certificate.snapshot) < certificate.index
            /\ IsPrefix(certificate.snapshot, certificate.entries)
            /\ certificate.configuration.members \subseteq Server
            /\ certificate.replication \in Quorums(certificate.configuration.members)
        BY SMT DEF RetainedCommitCertificate
    <2>lengths.
            /\ Len(certificate.entries) > 0
            /\ LastTerm(certificate.entries) = certificate.term
            /\ Len(certificate.snapshot) < Len(certificate.entries)
        BY <2>fields, LenProperties, SMT DEF LastTerm
    <2>log_frame. UNCHANGED log
        BY SMT DEF HandleRequestVoteRequest
    <2>prefix.
            /\ IsPrefix(certificate.entries, log[certificate.leader])
            /\ log[certificate.leader] \in Seq(LogEntry)
        BY <1>base, <2>fields, <2>log_frame, SMT DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>fields, <2>lengths, <2>prefix, SMT
<1>covered. CoveredPrefix(ancestry, certificate.entries)
    BY <1>base, <1>data, CurrentLogPrefixCovered, SMT
<1>history. nextVoteHistory = voteHistory
    BY <1>base, UnchangedLogsAndTermsKeepSelectedHistory, SMT DEF HandleRequestVoteRequest
<1>wire. CASE certificate.replication \ {certificate.leader} # {}
    <2>peer. PICK peer \in certificate.replication \ {certificate.leader}: TRUE
        BY <1>wire, SMT
    <2>target. CommitTarget(certificate) = certificate.entries
        BY <1>data, WholeSequencePrefix, SMT DEF CommitTarget
    <2>ack. RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, certificate.entries)'
        BY <2>peer, <2>target, SMT DEF RetainedCommitCertificate
    <2>pair. PICK response, request:
            /\ response \in messages' /\ request \in messages'
            /\ SuccessfulAppendResponse(response)
            /\ response.msource = peer /\ response.mdest = certificate.leader
            /\ response.mterm = certificate.term
            /\ response.mmatchIndex >= Len(certificate.entries)
            /\ ResponseMatchesRequest(response, request)
        BY <2>ack, SMT DEF RecordedPrefixAcknowledgment
    <2>old. response \in messages /\ request \in AppendRequests
        BY <2>pair, MessageTypesDistinct, SMT
        DEF AppendRequests, SuccessfulAppendResponse, ResponseMatchesRequest,
            HandleRequestVoteRequest, Send, WithMessage, WithMessages
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
            /\ RequestCampaignBoundary(voteHistory, request, prefix)
        BY <1>base, <2>old, SMT DEF RequestPrefixAncestry, AncestralRequestPrefix
    <2>campaign. PICK snapshot, occurrence, support:
            /\ snapshot \in Seq(LogEntry)
            /\ RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term, snapshot, occurrence, support)
            /\ (IsPrefix(snapshot, prefix) \/ IsPrefix(prefix, snapshot))
        BY <2>pair, <2>prefix, SMT DEF RequestCampaignBoundary, ResponseMatchesRequest
    <2>length.
            /\ Len(snapshot) = Len(certificate.snapshot)
            /\ Len(certificate.entries) <= Len(prefix)
        BY <1>data, <2>pair, <2>prefix, <2>campaign, VoteRequestSnapshotLengthsAgree, SMT
        DEF RetainedCommitCertificate, RequestPrefixData, ResponseMatchesRequest
    <2>target_campaign. TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, certificate.entries)
        BY <1>data, <2>campaign, <2>length, SMT DEF TargetCampaignEvidence
    <2>contains. IsPrefix(certificate.entries, prefix)
        BY <1>base, <1>data, <1>covered, <2>pair, <2>prefix, <2>length,
           <2>target_campaign, FrozenRequestPrefixContainsTarget, SMT DEF ResponseMatchesRequest
    <2>snapshots.
            /\ IsPrefix(snapshot, prefix) /\ IsPrefix(certificate.snapshot, prefix)
        BY <1>data, <2>prefix, <2>campaign, <2>length, <2>contains,
           SequencePrefixTransitive, LenProperties, SMT DEF IsPrefix
    <2>same. snapshot = certificate.snapshot
        BY <1>data, <2>prefix, <2>campaign, <2>length, <2>snapshots,
           PrefixesWithBoundedLength, WholeSequencePrefix, LenProperties, SMT DEF IsPrefix
    <2>occurrence. occurrence = certificate.electionOccurrence
        BY <2>campaign, <2>same, SMT DEF RetainedElectionCertificate, RetainedCommitCertificate
    <2> QED BY <2>campaign, <2>same, <2>occurrence, SMT
    
<1>local. CASE certificate.replication \ {certificate.leader} = {}
    <2>origin. LocalAppendOrigin(voteHistory, certificate.leader, certificate.term, certificate.entries)
        BY <1>history, <1>data, <1>local, WholeSequencePrefix, SMT DEF RetainedCommitCertificate, CommitTarget
    <2>election. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term, snapshot, occurrence, support)
        BY <1>base, <1>data, <2>origin, LocalAppendOriginHasRetainedElection, SMT DEF CertificateFamily
    <2>same. snapshot = certificate.snapshot /\ occurrence = certificate.electionOccurrence
        BY <1>history, <2>election, HistorySnapshotIsUnique, SMT
        DEF RetainedCommitCertificate, RetainedElectionCertificate
    <2> QED BY <2>election, <2>same, SMT
<1> QED BY <1>wire, <1>local, SMT

LEMMA PresentCertificateBeforeVoteRequest ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW vote \in messages,
           vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote), NEW certificate,
           RetainedCommitCertificate(nextVoteHistory, certificate)', certificate.index = Len(certificate.entries),
           IsPrefix(certificate.entries, log'[certificate.leader])
    PROVE \E previous:
              /\ RetainedCommitCertificate(voteHistory, previous)
              /\ previous.leader = certificate.leader
              /\ previous.entries = certificate.entries /\ previous.index = certificate.index
<1>election. PICK support:
        RetainedElectionCertificate(voteHistory, certificate.leader, certificate.term,
            certificate.snapshot, certificate.electionOccurrence, support)
    BY PresentAgreementHasPreexistingElection, SMT
<1>data.
        /\ certificate.leader \in Server /\ certificate.term \in Nat
        /\ certificate.entries \in Seq(LogEntry)
        /\ certificate.configuration.members \subseteq Server
        /\ certificate.replication \in Quorums(certificate.configuration.members)
    BY SMT DEF RetainedCommitCertificate
<1>target. CommitTarget(certificate) \in Seq(LogEntry)
    BY <1>data, SubSeqTypeOK, LenProperties, SMT DEF CommitTarget, RetainedCommitCertificate
<1>acks. \A peer \in certificate.replication \ {certificate.leader}:
        RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))
    BY <1>data, <1>target, VoteRequestPrefixAcknowledgmentsFrame, SMT
    DEF RetainedCommitCertificate, Quorums
<1>owner. OwnerPrefix(certificate.leader, certificate.term, certificate.entries)
    BY SMT DEF RetainedCommitCertificate, OwnerPrefix, HandleRequestVoteRequest
<1> DEFINE previous ==
        [leader |-> certificate.leader, term |-> certificate.term,
         entries |-> certificate.entries, index |-> certificate.index,
         snapshot |-> certificate.snapshot, electionOccurrence |-> certificate.electionOccurrence,
         election |-> support, configuration |-> certificate.configuration,
         replication |-> certificate.replication]
<1>same_target. CommitTarget(previous) = CommitTarget(certificate)
    BY SMT DEF previous, CommitTarget
<1>history. nextVoteHistory = voteHistory
    BY JointCoreBase, UnchangedLogsAndTermsKeepSelectedHistory, SMT DEF HandleRequestVoteRequest
<1>valid. RetainedCommitCertificate(voteHistory, previous)
    BY <1>election, <1>acks, <1>owner, <1>same_target, <1>history, SMT DEF previous, RetainedCommitCertificate
<1> QED BY <1>valid, SMT DEF previous

LEMMA VoteRequestPreservesEvidenceTargets ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW vote \in messages,
           vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote)
    PROVE EvidenceAgreementTargets(nextVoteHistory)' = EvidenceAgreementTargets(voteHistory)
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
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
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, HandleRequestVoteRequest
<1>reverse. EvidenceAgreementTargets(nextVoteHistory)' \subseteq EvidenceAgreementTargets(voteHistory)
    <2> SUFFICES ASSUME NEW target \in EvidenceAgreementTargets(nextVoteHistory)' PROVE target \in EvidenceAgreementTargets(voteHistory)
        BY SMT
    <2>certificate. PICK certificate:
            /\ RetainedCommitCertificate(nextVoteHistory, certificate)'
            /\ certificate.entries = target /\ certificate.index = Len(target)
            /\ IsPrefix(target, log'[certificate.leader])
        BY SMT DEF EvidenceAgreementTargets, SupportedAgreementTarget
    <2>previous. PICK previous:
            /\ RetainedCommitCertificate(voteHistory, previous)
            /\ previous.leader = certificate.leader
            /\ previous.entries = certificate.entries /\ previous.index = certificate.index
        BY <2>certificate, PresentCertificateBeforeVoteRequest, SMT
    <2> QED BY <2>certificate, <2>previous, SMT
        DEF EvidenceAgreementTargets, SupportedAgreementTarget, HandleRequestVoteRequest
<1> QED BY <1>forward, <1>reverse, SMT

LEMMA ReadyCertificateUsesOpportunity ==
    ASSUME NEW voteHistory, NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY SMT
    DEF ReadyElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor,
        RecordedCampaignVote, OpportunityCertificate, CampaignOpportunity, OpportunityVoters, Quorums

LEMMA PostReadyCertificateUsesOpportunity ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           ReadyElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    PROVE OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    BY SMT
    DEF ReadyElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor,
        RecordedCampaignVote, OpportunityCertificate, CampaignOpportunity, OpportunityVoters, Quorums

LEMMA PostOpportunityRelationsSupplyReady ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry, NEW commits, OpportunityRelations(nextVoteHistory, ancestry, commits)'
    PROVE ReadyMembershipRelations(nextVoteHistory, ancestry, commits)'
    BY PostReadyCertificateUsesOpportunity, SMT
    DEF OpportunityRelations, ReadyMembershipRelations,
        OpportunityElectionIntersections, ReadyElectionIntersections,
        OpportunityRequestIntersections, ReadyRequestIntersections,
        OpportunityAncestryIntersections, ReadyAncestryIntersections,
        OpportunityCommitIntersections, ReadyCommitIntersections,
        OpportunityCommitPrefixes, ReadyCommitPrefixes,
        OpportunityEvidencePrefixes, ReadyEvidencePrefixes

\* A vote can narrow eligibility, but cannot add a peer who was ineligible
\* before the receive. Current and future campaigns use the same rule.
LEMMA VoteRequestCannotEnablePeerEligibility ==
    ASSUME TypeOK, NEW vote \in messages, vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote),
           NEW peer \in Server, NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), NewPeerVoteEligible(peer, candidate, term, snapshot)'
    PROVE NewPeerVoteEligible(peer, candidate, term, snapshot)
    BY StoredMessageFieldsTypeOK, NilNotServer, SMT
    DEF NewPeerVoteEligible, SnapshotFreshFor, HandleRequestVoteRequest,
        TypeOK, ServerVarsTypeOK, LogVarsTypeOK

LEMMA VoteRequestOpportunityCertificatesShrink ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW vote \in messages, vote.mtype = RequestVoteRequest,
           HandleRequestVoteRequest(vote.mdest, vote.msource, vote)
    PROVE NoNewOpportunityCertificates(voteHistory, nextVoteHistory)
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>next. [Next]_vars BY SMT DEF Next, Receive, HandleMsg
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
                      NEW occurrence, NEW support,
                      OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
             PROVE OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY SMT DEF NoNewOpportunityCertificates
<1>history. nextVoteHistory = voteHistory
    BY <1>base, UnchangedLogsAndTermsKeepSelectedHistory, SMT DEF HandleRequestVoteRequest
<1>campaign. CampaignOpportunity(candidate, term, snapshot)
    BY MessageTypesDistinct, SMT
    DEF OpportunityCertificate, CampaignOpportunity, RecordedCampaignRequests,
        HandleRequestVoteRequest, Send, WithMessage, WithMessages
<1>quorum.
        /\ occurrence = LatestConfigurationOccurrence(snapshot)
        /\ occurrence.members \subseteq Server /\ occurrence.members # {}
        /\ support \in Quorums(occurrence.members) /\ support \subseteq occurrence.members
    BY SMT DEF OpportunityCertificate, OpportunityVoters
<1>voters. support \subseteq OpportunityVoters(voteHistory, candidate, term, snapshot, occurrence.members)
    <2> SUFFICES ASSUME NEW voter \in support
                 PROVE voter \in OpportunityVoters(voteHistory, candidate, term, snapshot, occurrence.members)
        BY SMT
    <2>typed. voter \in Server /\ voter \in occurrence.members
        BY <1>quorum, SMT
    <2>recorded. CASE RecordedCampaignVote(nextVoteHistory, voter, candidate, term)'
        <3>old. CASE RecordedCampaignVote(voteHistory, voter, candidate, term)
            BY <2>typed, <3>old, SMT DEF OpportunityVoters
        <3>new. CASE ~RecordedCampaignVote(voteHistory, voter, candidate, term)
            <4>peer. voter # candidate /\ ~Grant(voter, candidate, term)
                BY <1>base, <1>history, <2>recorded, <3>new, MessageTypesDistinct, SMT
                DEF RecordedCampaignVote, Started, Grant, SendInvariant, HandleRequestVoteRequest,
                    Send, WithMessage, WithMessages
            <4>response. PICK response \in messages' \ messages:
                    /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
                    /\ response.msource = voter /\ response.mdest = candidate /\ response.mterm = term
                BY <2>recorded, <4>peer, SMT DEF RecordedCampaignVote, Grant
            <4>request. PICK request \in messages:
                    /\ request.msource = candidate /\ request.mdest = voter /\ request.mterm = term
                    /\ VoteRequestEligible(request, voter)
                BY <1>base, <1>next, <4>response, NewPositiveVoteHasEligibleRequest, SMT
            <4>bound. term <= currentTerm[candidate]
                BY <1>base, <4>request, SMT DEF SendInvariant
            <4>registered. request \in CampaignRequests(candidate, term, snapshot)
                BY <1>base, <1>campaign, <4>request, <4>bound, SMT
                DEF CampaignOpportunity, VoteRequestEligible, RecordedCampaignRequests,
                    TypeOK, ServerVarsTypeOK
            <4>eligible. NewPeerVoteEligible(voter, candidate, term, snapshot)
                BY <1>base, <2>typed, <4>request, <4>registered, CampaignRequestEligibilityUsesSnapshot, SMT
            <4> QED BY <2>typed, <4>eligible, SMT DEF OpportunityVoters
        <3> QED BY <3>old, <3>new, SMT
    <2>self. CASE voter = candidate /\ currentTerm'[candidate] < term /\ snapshot = log'[candidate]
        BY <2>typed, <2>self, SMT DEF OpportunityVoters, HandleRequestVoteRequest
    <2>peer. CASE NewPeerVoteEligible(voter, candidate, term, snapshot)'
        BY <1>base, <2>typed, <2>peer, VoteRequestCannotEnablePeerEligibility, SMT DEF OpportunityVoters
    <2> QED BY <2>recorded, <2>self, <2>peer, SMT DEF OpportunityCertificate, OpportunityVoters
<1> QED BY <1>campaign, <1>quorum, <1>voters, SMT DEF OpportunityCertificate

\* Recorded votes constrain fresh eligibility even after their recipient or
\* sender advances its term. A potential vote is not a second recorded vote.
LEMMA RecordedAndEligibleCampaignVotesIdentifyCandidate ==
    ASSUME NEW voteHistory, TypeOK, SendInvariant, VoteRecordInv(voteHistory),
           NEW voter \in Server, NEW owner \in Server, NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), RecordedCampaignVote(voteHistory, voter, owner, term),
           RecordedCampaignVote(voteHistory, voter, candidate, term)
               \/ (voter = candidate /\ currentTerm[candidate] < term)
               \/ NewPeerVoteEligible(voter, candidate, term, snapshot)
    PROVE owner = candidate
<1>recorded. CASE RecordedCampaignVote(voteHistory, voter, candidate, term)
    BY <1>recorded, SMT
    DEF VoteRecordInv, VoteUniqueInv, StartedGrantInv, RecordedCampaignVote
<1>self. CASE voter = candidate /\ currentTerm[candidate] < term
    BY <1>self, RecordedCampaignVoteTermBound, SMT DEF TypeOK, ServerVarsTypeOK
<1>fresh. CASE NewPeerVoteEligible(voter, candidate, term, snapshot)
    <2>epoch. currentTerm[voter] = term
        BY <1>fresh, RecordedCampaignVoteTermBound, SMT
        DEF NewPeerVoteEligible, TypeOK, ServerVarsTypeOK
    <2>vote. votedFor[voter] = owner
        BY <2>epoch, SMT
        DEF VoteRecordInv, VoteCurrentInv, StartedCurrentInv, RecordedCampaignVote
    <2> QED BY <1>fresh, <2>epoch, <2>vote, NilNotServer, SMT DEF NewPeerVoteEligible
<1> QED BY <1>recorded, <1>self, <1>fresh, SMT

\* Freshness itself is irrelevant to uniqueness at a shared voter. Keeping
\* the snapshot arbitrary lets the lemma cover pending and future campaigns.
LEMMA RecordedSupportMeetsOpportunityOnlyForOwner ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW owner \in Server, NEW candidate \in Server,
           NEW term \in Nat, NEW recorded, VoteSupport(voteHistory, owner, term, recorded),
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW eligible,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, eligible),
           recorded \cap eligible # {}
    PROVE owner = candidate
<1>base. TypeOK /\ SendInvariant /\ VoteRecordInv(voteHistory) BY JointCoreBase, SMT
<1>shared. PICK voter \in recorded \cap eligible: TRUE BY SMT
<1>votes.
        /\ voter \in Server /\ RecordedCampaignVote(voteHistory, voter, owner, term)
        /\ RecordedCampaignVote(voteHistory, voter, candidate, term)
           \/ (voter = candidate /\ currentTerm[candidate] < term)
           \/ NewPeerVoteEligible(voter, candidate, term, snapshot)
    BY <1>shared, SMT
    DEF VoteSupport, VoteFor, RecordedCampaignVote, OpportunityCertificate, OpportunityVoters
<1> QED BY <1>base, <1>votes, RecordedAndEligibleCampaignVotesIdentifyCandidate, SMT

LEMMA FreshCoveredSequenceContainsTarget ==
    ASSUME NEW voteHistory, NEW ancestry, CertificateFamily(voteHistory, ancestry), TermPrefixOrder(ancestry),
           NEW target \in Seq(LogEntry), NEW term \in Nat,
           Len(target) > 0, LastTerm(target) = term,
           LaterTermPrefixProtection(ancestry, target, term),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           IsPrefix(target, entries), NEW snapshot \in Seq(LogEntry), CoveredPrefix(ancestry, snapshot),
           LastTerm(snapshot) > LastTerm(entries)
               \/ (LastTerm(snapshot) = LastTerm(entries) /\ Len(snapshot) >= Len(entries))
    PROVE IsPrefix(target, snapshot)
<1>types.
        /\ Len(target) \in Nat /\ Len(entries) \in Nat /\ Len(snapshot) \in Nat
        /\ Len(entries) > 0 /\ LastTerm(entries) \in Nat /\ LastTerm(snapshot) \in Nat
    BY LenProperties, LastTermTypeOK, SMT DEF IsPrefix
<1>bound. term <= LastTerm(entries) BY OrderedPrefixLastTermBound, SMT
<1>newer. CASE LastTerm(snapshot) > term
    <2>nonempty. Len(snapshot) > 0 BY <1>types, <1>newer, SMT DEF LastTerm
    <2>tip. PICK witness \in ancestry:
            /\ witness.prefix = snapshot /\ witness.edge.term = LastTerm(snapshot)
        BY <2>nonempty, OrderedTermPrefixesAreEdgeConsistent, CoveredSequenceHasLastWitness, SMT
    <2> QED BY <1>newer, <2>tip, SMT DEF LaterTermPrefixProtection
<1>older. CASE LastTerm(snapshot) <= term
    <2>fresh.
            /\ LastTerm(snapshot) = LastTerm(entries) /\ Len(entries) <= Len(snapshot)
            /\ Len(snapshot) > 0
        BY <1>types, <1>bound, <1>older, SMT
    <2>prefix. IsPrefix(entries, snapshot)
        BY <1>types, <2>fresh, CoveredSequencesWithSameLastTermAreOrdered, SMT
    <2> QED BY <2>prefix, SequencePrefixTransitive, SMT
<1> QED BY <1>types, <1>newer, <1>older, SMT

LEMMA CampaignOpportunitySnapshotCovered ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW candidate \in Server,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), CampaignOpportunity(candidate, term, snapshot)
    PROVE IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot)
<1>base. TypeOK /\ log[candidate] \in Seq(LogEntry) /\ TermsOrdered(log[candidate])
    BY JointCoreBase, SMT
    DEF TypeOK, LogVarsTypeOK, MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>prefix. IsPrefix(snapshot, log[candidate])
    BY <1>base, CampaignPrefixProperties, PreTermIndexProperties, WholeSequencePrefix, LenProperties, SMT
    DEF CampaignOpportunity, CampaignPrefix, IsPrefix
<1> QED BY <1>base, <1>prefix, CurrentLogPrefixCovered, SMT DEF JointMembershipWitnesses

LEMMA AppendReceiveLogsCoveredByPreAncestry ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW request \in messages,
           request.mtype = AppendEntriesRequest,
           HandleAppendEntriesRequest(request.mdest, request.msource, request)
    PROVE \A server \in Server: CoveredPrefix(ancestry, log'[server])
<1>base. TypeOK /\ EntryEdgeBase /\ AppendRequestRootTerm
    BY JointCoreBase, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv
<1>fields. request.mdest \in Server /\ request.msource \in Server
    BY <1>base, StoredMessageFieldsTypeOK, SMT
<1>edges. HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    BY <1>base, <1>fields, EntryEdgeAppendReceiveSubset, SMT
<1> SUFFICES ASSUME NEW server \in Server, NEW index \in DOMAIN log'[server]
             PROVE \E witness \in ancestry: witness.edge = LogEntryEdge(log'[server], index)
    BY SMT DEF CoveredPrefix
<1>edge. LogEntryEdge(log'[server], index) \in HistoricalEntryEdges'
    BY SMT DEF HistoricalEntryEdges, LogEntryEdge
<1> QED BY <1>edges, <1>edge, SMT DEF JointMembershipWitnesses, CoversEntryEdges

LEMMA AppendRequestOwnersUniqueInit == Init => AppendRequestOwnersUnique
    BY SMT DEF Init, AppendRequestOwnersUnique, AppendRequests

LEMMA AppendRequestOwnersUniqueNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), AppendRequestOwnersUnique, [Next]_vars
    PROVE AppendRequestOwnersUnique'
<1>base. TypeOK /\ EntryEdgeBase /\ CurrentRequestSendersUnique
    BY JointCoreBase, IntersectingRequestCertificatesIdentifySenders, SMT DEF MembershipJointCore
<1> SUFFICES ASSUME NEW left \in AppendRequests', NEW right \in AppendRequests', left.mterm = right.mterm
             PROVE left.msource = right.msource BY SMT DEF AppendRequestOwnersUnique
<1>old. CASE left \in messages /\ right \in messages
    BY <1>old, SMT DEF AppendRequestOwnersUnique, AppendRequests
<1>left. CASE left \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer) /\ left = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>left, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>right_old. CASE right \in messages
        BY <1>base, <2>origin, <2>right_old, SMT
        DEF CurrentRequestSendersUnique, AppendEntries, AppendEntriesMessage, AppendRequests
    <2>right_new. CASE right \notin messages
        BY <2>origin, <2>right_new, SMT
        DEF AppendEntries, Send, WithMessage, WithMessages, AppendRequests
    <2> QED BY <2>right_old, <2>right_new, SMT
<1>right. CASE right \notin messages
    <2>origin. PICK leader, peer \in Server:
            /\ AppendEntries(leader, peer) /\ right = AppendEntriesMessage(leader, peer)
        BY <1>base, <1>right, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>left_old. CASE left \in messages
        BY <1>base, <2>origin, <2>left_old, SMT
        DEF CurrentRequestSendersUnique, AppendEntries, AppendEntriesMessage, AppendRequests
    <2>left_new. CASE left \notin messages
        BY <2>origin, <2>left_new, SMT DEF AppendEntries, Send, WithMessage, WithMessages, AppendRequests
    <2> QED BY <2>left_old, <2>left_new, SMT
<1> QED BY <1>old, <1>left, <1>right, SMT

LEMMA CoveredRequestPrefixIsUnique ==
    ASSUME NEW voteHistory, NEW ancestry, CertificateFamily(voteHistory, ancestry), TermPrefixOrder(ancestry), NEW request, request.mentries \in Seq(LogEntry),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           RequestPrefixData(request, left), RequestPrefixData(request, right),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right)
    PROVE left = right
<1>length. Len(left) = Len(right) /\ Len(left) \in Nat
    BY LenProperties, SMT DEF RequestPrefixData
<1>empty. CASE Len(left) = 0
    BY <1>length, <1>empty, EmptySeq, SMT
<1>entries. CASE Len(request.mentries) > 0
    <2>seq. request.mentries \in Seq(LogEntry)
        BY SMT
    <2>last. LastTerm(left) = LastTerm(right)
        BY <1>length, <1>entries, <2>seq, LenProperties, SMT DEF RequestPrefixData, LastTerm
    <2>order. IsPrefix(left, right)
        BY <1>length, <1>entries, <2>seq, <2>last, LenProperties, CoveredSequencesWithSameLastTermAreOrdered, SMT
        DEF RequestPrefixData
    <2> QED BY <1>length, <2>order, WholeSequencePrefix, SMT DEF IsPrefix
<1>anchor. CASE Len(left) > 0 /\ Len(request.mentries) = 0
    <2>last. LastTerm(left) = LastTerm(right)
        BY <1>length, <1>anchor, SMT DEF RequestPrefixData, LastTerm
    <2>order. IsPrefix(left, right)
        BY <1>length, <1>anchor, <2>last, CoveredSequencesWithSameLastTermAreOrdered, SMT
        DEF RequestPrefixData
    <2> QED BY <1>length, <2>order, WholeSequencePrefix, SMT DEF IsPrefix
<1> QED BY <1>empty, <1>entries, <1>anchor, LenProperties, SMT DEF RequestPrefixData

LEMMA CurrentRequestCoveredPrefixBelongsToLeader ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW leader \in Server, state[leader] = Leader, NEW request \in AppendRequests,
           request.mterm = currentTerm[leader], NEW prefix \in Seq(LogEntry),
           RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix)
    PROVE IsPrefix(prefix, log[leader])
<1>base. TypeOK /\ CurrentRequestSendersUnique /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, IntersectingRequestCertificatesIdentifySenders, SMT
    DEF MembershipJointCore, JointMembershipWitnesses
<1>owner. request.msource = leader BY <1>base, SMT DEF CurrentRequestSendersUnique
<1>frozen. PICK frozen \in Seq(LogEntry):
        /\ RequestPrefixData(request, frozen) /\ CoveredPrefix(ancestry, frozen)
        /\ OwnerPrefix(request.msource, request.mterm, frozen)
    BY SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
<1>equal. prefix = frozen BY <1>base, <1>frozen, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
    DEF TypeOK, MsgTypeOK, AppendRequests
<1> QED BY <1>owner, <1>frozen, <1>equal, SMT DEF OwnerPrefix

LEMMA AppendSendPreservesFrozenRequestAgreement ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenRequestPrefixesAgree(ancestry), NEW leader \in Server, NEW peer \in Server,
           AppendEntries(leader, peer)
    PROVE FrozenRequestPrefixesAgree(ancestry)'
<1>next. [Next]_vars BY SMT DEF Next
<1>base. TypeOK /\ TypeOK' /\ ReplicationEvidenceInv(voteHistory) /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, <1>next, TypeOKNext, ReplicationPrefixInvNext, SMT DEF MembershipJointCore, ReplicationPrefixInv, JointMembershipWitnesses, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>sent. PICK sent: sent = AppendEntriesMessage(leader, peer) BY SMT
<1>new. AncestralRequestPrefix(nextVoteHistory, ancestry, sent)'
    BY <1>base, <1>sent, NewAppendRequestHasAncestralPrefix, SMT DEF JointMembershipWitnesses
<1> SUFFICES ASSUME NEW left \in AppendRequests', NEW right \in AppendRequests', left.mterm = right.mterm,
                      NEW leftPrefix \in Seq(LogEntry), NEW rightPrefix \in Seq(LogEntry),
                      RequestPrefixData(left, leftPrefix), CoveredPrefix(ancestry, leftPrefix),
                      RequestPrefixData(right, rightPrefix), CoveredPrefix(ancestry, rightPrefix)
             PROVE IsPrefix(leftPrefix, rightPrefix) \/ IsPrefix(rightPrefix, leftPrefix)
    BY SMT DEF FrozenRequestPrefixesAgree, RequestPrefixData, CoveredPrefix
<1>old. CASE left \in messages /\ right \in messages
    BY <1>old, SMT DEF FrozenRequestPrefixesAgree, AppendRequests
<1>new_case. CASE left \notin messages \/ right \notin messages
    <2>epoch. left.mterm = currentTerm[leader] /\ right.mterm = currentTerm[leader]
        BY <1>new_case, SMT DEF AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages, AppendRequests
    <2>left. IsPrefix(leftPrefix, log[leader])
        <3>old. CASE left \in messages
            BY <1>base, <2>epoch, <3>old, CurrentRequestCoveredPrefixBelongsToLeader, SMT
            DEF AppendEntries, AppendRequests
        <3>new. CASE left \notin messages
            <4>frozen. PICK frozen \in Seq(LogEntry):
                    /\ RequestPrefixData(left, frozen) /\ CoveredPrefix(ancestry, frozen)
                    /\ OwnerPrefix(leader, currentTerm[leader], frozen)'
                BY <1>sent, <1>new, <3>new, SMT
                DEF AncestralRequestPrefix, RequestPrefixData, CoveredPrefix, AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages, AppendRequests
            <4>equal. frozen = leftPrefix BY <1>base, <4>frozen, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
                DEF TypeOK, MsgTypeOK, AppendRequests
            <4> QED BY <4>frozen, <4>equal, SMT DEF OwnerPrefix, AppendEntries
        <3> QED BY <3>old, <3>new, SMT
    <2>right. IsPrefix(rightPrefix, log[leader])
        <3>old. CASE right \in messages
            BY <1>base, <2>epoch, <3>old, CurrentRequestCoveredPrefixBelongsToLeader, SMT
            DEF AppendEntries, AppendRequests
        <3>new. CASE right \notin messages
            <4>frozen. PICK frozen \in Seq(LogEntry):
                    /\ RequestPrefixData(right, frozen) /\ CoveredPrefix(ancestry, frozen)
                    /\ OwnerPrefix(leader, currentTerm[leader], frozen)'
                BY <1>sent, <1>new, <3>new, SMT
                DEF AncestralRequestPrefix, RequestPrefixData, CoveredPrefix, AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages, AppendRequests
            <4>equal. frozen = rightPrefix BY <1>base, <4>frozen, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
                DEF TypeOK, MsgTypeOK, AppendRequests
            <4> QED BY <4>frozen, <4>equal, SMT DEF OwnerPrefix, AppendEntries
        <3> QED BY <3>old, <3>new, SMT
    <2> QED BY <1>base, <2>left, <2>right, PrefixesWithBoundedLength, SMT DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>old, <1>new_case, SMT

LEMMA ComparableRequestPrefixRespectsTarget ==
    ASSUME NEW request, request.mentries \in Seq(LogEntry), NEW sent \in Seq(LogEntry),
           RequestPrefixData(request, sent), NEW original \in Seq(LogEntry),
           IsPrefix(sent, original) \/ IsPrefix(original, sent),
           NEW target \in Seq(LogEntry), IsPrefix(target, original)
    PROVE RequestRespectsPrefix(request, target)
<1> SUFFICES ASSUME NEW offset \in DOMAIN request.mentries,
                      request.mprevLogIndex + offset \in DOMAIN target
             PROVE request.mentries[offset] = target[request.mprevLogIndex + offset]
    BY SMT DEF RequestRespectsPrefix
<1>index. request.mprevLogIndex + offset \in DOMAIN sent
    BY LenProperties, SMT DEF RequestPrefixData
<1>left. CASE IsPrefix(sent, original)
    <2>same. sent[request.mprevLogIndex + offset] = original[request.mprevLogIndex + offset]
        BY <1>index, <1>left, PrefixEntryEqual, LenProperties, SMT
    <2>target. target[request.mprevLogIndex + offset] = original[request.mprevLogIndex + offset]
        BY PrefixEntryEqual, LenProperties, SMT
    <2> QED BY <2>same, <2>target, SMT DEF RequestPrefixData
<1>right. CASE IsPrefix(original, sent)
    <2>prefix. IsPrefix(target, sent) BY <1>right, SequencePrefixTransitive, SMT
    <2>same. target[request.mprevLogIndex + offset] = sent[request.mprevLogIndex + offset]
        BY <2>prefix, PrefixEntryEqual, LenProperties, SMT
    <2> QED BY <2>same, SMT DEF RequestPrefixData
<1> QED BY <1>left, <1>right, SMT

LEMMA FrozenAcknowledgedTargetNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), FrozenRequestPrefixesAgree(ancestry),
           NEW response \in messages, SuccessfulAppendResponse(response), NEW original \in AppendRequests,
           ResponseMatchesRequest(response, original), NEW prefix \in Seq(LogEntry),
           RequestPrefixData(original, prefix), CoveredPrefix(ancestry, prefix),
           NEW target \in Seq(LogEntry), IsPrefix(target, prefix),
           IsPrefix(target, log[response.msource]), currentTerm[response.msource] >= response.mterm
    PROVE IsPrefix(target, log'[response.msource])
          \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
<1>base. TypeOK /\ EntryEdgeBase /\ response.msource \in Server /\ response.mterm \in Nat
    BY JointCoreBase, MessageFieldsTypeOK, SMT DEF MembershipJointCore, TypeOK, MsgTypeOK
<1>conflict. CASE ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
    BY <1>conflict, SMT
<1>no_conflict. CASE ~ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
    <2>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>base, <2>client, ClientRequestAppendsCurrentTerm, PrefixOnAppend, SMT
        DEF ClientRequest, TypeOK, LogVarsTypeOK
    <2>receive. CASE \E request \in messages:
            /\ request.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
        <3>request. PICK request \in messages:
                /\ request.mtype = AppendEntriesRequest
                /\ HandleAppendEntriesRequest(request.mdest, request.msource, request)
            BY <2>receive, SMT
        <3>fields. request \in AppendRequests /\ request.msource \in Server
                  /\ request.mdest \in Server /\ request.mterm \in Nat /\ request.mentries \in Seq(LogEntry)
            BY <1>base, <3>request, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
        <3>recipient. CASE request.mdest = response.msource
            <4>same. request.mterm = response.mterm => RequestRespectsPrefix(request, target)
                <5> SUFFICES ASSUME request.mterm = response.mterm PROVE RequestRespectsPrefix(request, target) BY SMT
                <5>sent. PICK sent \in Seq(LogEntry): RequestPrefixData(request, sent) /\ CoveredPrefix(ancestry, sent)
                    BY <3>fields, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
                <5>order. IsPrefix(sent, prefix) \/ IsPrefix(prefix, sent)
                    BY <3>fields, <5>sent, SMT DEF FrozenRequestPrefixesAgree, ResponseMatchesRequest
                <5>numbers.
                        /\ request.mprevLogIndex \in Nat
                        /\ Len(sent) \in Nat /\ Len(prefix) \in Nat /\ Len(target) \in Nat
                    BY <3>fields, <5>sent, LenProperties, SMT DEF RequestPrefixData
                <5> QED BY <3>fields, <5>sent, <5>order, <5>numbers,
                    ComparableRequestPrefixRespectsTarget, SMT
            <4>higher. request.mterm > response.mterm => RequestRespectsPrefix(request, target)
                <5> SUFFICES ASSUME request.mterm > response.mterm
                             PROVE RequestRespectsPrefix(request, target) BY SMT
                <5>retained. request \in AppendRequests'
                    BY <1>base, <3>fields, MessagesMonotonicNext, SMT DEF AppendRequests
                <5>epoch. request.mterm <= currentTerm'[response.msource]
                    BY <1>base, <3>request, <3>fields, <3>recipient, SMT
                    DEF HandleAppendEntriesRequest, TypeOK, ServerVarsTypeOK
                <5> QED BY <1>no_conflict, <3>recipient, <5>retained, <5>epoch, SMT
                    DEF ConflictingHigherAppendRequest
            <4> QED BY <1>base, <3>request, <3>fields, <3>recipient, <4>same, <4>higher,
                AppendRequestPreservesProtectedPrefix, SMT
        <3>other. CASE request.mdest # response.msource
            BY <1>base, <3>request, <3>other, HandleAppendEntriesRequestPreservesOtherServer, SMT
        <3> QED BY <3>recipient, <3>other, SMT
    <2>same. CASE UNCHANGED log BY <2>same, SMT
    <2> QED BY <1>base, <2>client, <2>receive, <2>same, LogChangingActionNext, SMT
<1> QED BY <1>conflict, <1>no_conflict, SMT

LEMMA FrozenAcknowledgmentPrefixHistoryInit == Init => FrozenAcknowledgmentPrefixHistory({})
    BY SMT DEF Init, FrozenAcknowledgmentPrefixHistory

LEMMA FrozenAcknowledgmentPrefixHistoryNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), FrozenRequestPrefixesAgree(ancestry),
           FrozenAcknowledgmentPrefixHistory(ancestry)
    PROVE FrozenAcknowledgmentPrefixHistory(ancestry)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ SendInvariant' /\ WitnessEdgeConsistency(ancestry)
    BY JointCoreBase, TypeOKNext, SendInvariantNext, OrderedTermPrefixesAreEdgeConsistent, SMT
    DEF MembershipJointCore, JointMembershipWitnesses, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response)
             PROVE \E request \in AppendRequests': \E prefix \in Seq(LogEntry):
                       /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                       /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                       /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                              IsPrefix(target, log'[response.msource])
                              \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
    BY SMT DEF FrozenAcknowledgmentPrefixHistory, ResponseMatchesRequest, RequestPrefixData, CoveredPrefix
<1>fields. response.msource \in Server /\ response.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>old. CASE response \in messages
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                   IsPrefix(target, log[response.msource])
                   \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
        BY <1>old, SMT DEF FrozenAcknowledgmentPrefixHistory
    <2>epoch. currentTerm[response.msource] >= response.mterm
        BY <1>base, <1>old, <1>fields, SMT DEF SendInvariant
    <2>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
            IsPrefix(target, log'[response.msource])
            \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)'
        BY <1>base, <1>fields, <1>old, <2>frozen, <2>epoch, FrozenAcknowledgedTargetNext,
           ConflictingHigherAppendRequestRetained, SMT
    <2> QED BY <2>frozen, <2>targets, MessagesMonotonicNext, SMT DEF AppendRequests
<1>new. CASE response \notin messages
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ IsPrefix(prefix, log'[response.msource])
        BY <1>base, <1>new, NewAcknowledgmentHasPhysicalPrefix, SMT DEF JointMembershipWitnesses
    <2>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) => IsPrefix(target, log'[response.msource])
        BY <1>base, <1>fields, <2>frozen, SequencePrefixTransitive, SMT DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>frozen, <2>targets, MessagesMonotonicNext, SMT DEF AppendRequests
<1> QED BY <1>old, <1>new, SMT

LEMMA FrozenResponsePrefixesEqual ==
    ASSUME NEW ancestry, FrozenRequestPrefixesAgree(ancestry), NEW response,
           NEW leftRequest \in AppendRequests, NEW rightRequest \in AppendRequests,
           ResponseMatchesRequest(response, leftRequest), ResponseMatchesRequest(response, rightRequest),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           RequestPrefixData(leftRequest, left), RequestPrefixData(rightRequest, right),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right)
    PROVE left = right
<1>order. IsPrefix(left, right) \/ IsPrefix(right, left)
    BY SMT DEF FrozenRequestPrefixesAgree, ResponseMatchesRequest
<1>length. Len(left) = Len(right)
    BY SMT DEF RequestPrefixData, ResponseMatchesRequest
<1> QED BY <1>order, <1>length, WholeSequencePrefix, SMT DEF IsPrefix

LEMMA FrozenAcknowledgmentFixedTargetHistory ==
    ASSUME NEW ancestry, FrozenAcknowledgmentPrefixHistory(ancestry), FrozenRequestPrefixesAgree(ancestry),
           NEW response \in messages, SuccessfulAppendResponse(response), NEW request \in AppendRequests,
           ResponseMatchesRequest(response, request), NEW prefix \in Seq(LogEntry),
           RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix),
           NEW target \in Seq(LogEntry), IsPrefix(target, prefix)
    PROVE IsPrefix(target, log[response.msource])
          \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
<1>frozen. PICK original, frozen:
        /\ original \in AppendRequests /\ frozen \in Seq(LogEntry)
        /\ ResponseMatchesRequest(response, original) /\ RequestPrefixData(original, frozen)
        /\ CoveredPrefix(ancestry, frozen)
        /\ \A part \in Seq(LogEntry): IsPrefix(part, frozen) =>
               IsPrefix(part, log[response.msource])
               \/ ConflictingHigherAppendRequest(response.msource, response.mterm, part)
    BY SMT DEF FrozenAcknowledgmentPrefixHistory
<1>equal. prefix = frozen BY <1>frozen, FrozenResponsePrefixesEqual, SMT
<1> QED BY <1>frozen, <1>equal, SMT

LEMMA FrozenAcknowledgmentVoteCutsNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), FrozenRequestPrefixesAgree(ancestry),
           FrozenAcknowledgmentPrefixHistory(ancestry),
           NEW response \in messages, SuccessfulAppendResponse(response), NEW request \in AppendRequests,
           ResponseMatchesRequest(response, request), NEW prefix \in Seq(LogEntry),
           RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix),
           AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
    PROVE AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
<1>base.
        /\ TypeOK /\ TypeOK' /\ SendInvariant'
        /\ response.msource \in Server /\ response.mterm \in Nat
        /\ TermsOrdered(log[response.msource])
    <2>pre. TypeOK /\ SendInvariant /\ ReplicationPrefixInv(voteHistory)
        BY JointCoreBase, SMT DEF MembershipJointCore
    <2>post. ReplicationPrefixInv(nextVoteHistory)'
        BY <2>pre, ReplicationPrefixInvNext, SMT
    <2>post_type. TypeOK' /\ SendInvariant'
        BY <2>post, SMT
        DEF ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
            MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
    <2>fields. response.msource \in Server /\ response.mterm \in Nat
        BY <2>pre, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
    <2>terms. TermsOrdered(log[response.msource])
        BY <2>fields, JointCoreBase, SMT
        DEF MembershipCampaignsInv, MembershipVotesInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
    <2> QED BY <2>pre, <2>post_type, <2>fields, <2>terms, SMT
<1> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix),
                      NEW candidate \in Server, NEW later \in Nat,
                      later > response.mterm, RecordedCampaignVote(nextVoteHistory, response.msource, candidate, later)'
             PROVE ConflictingRequestBeforeVote(response.msource, response.mterm, later, target)'
                   \/ \E voteRequest \in RecordedVoteRequests(nextVoteHistory, candidate, later)':
                          VoteRequestCoversPrefix(voteRequest, target)
    BY SMT DEF AcknowledgmentVoteCuts
<1>old. CASE RecordedCampaignVote(voteHistory, response.msource, candidate, later)
    BY <1>old, MessagesMonotonicNext, SMT
    DEF AcknowledgmentVoteCuts, ConflictingRequestBeforeVote, AppendRequests, RecordedCampaignRequests, RecordedVoteRequests, CampaignHistoryContextStep, CampaignHistoryStep
<1>new. CASE ~RecordedCampaignVote(voteHistory, response.msource, candidate, later)
    <2>epoch. currentTerm[response.msource] <= later
        BY <1>base, <1>new, NewRecordedVotePreEpochBound, SMT
    <2>history. IsPrefix(target, log[response.msource])
              \/ ConflictingHigherAppendRequest(response.msource, response.mterm, target)
        BY FrozenAcknowledgmentFixedTargetHistory, SMT
    <2>conflict. CASE ConflictingHigherAppendRequest(response.msource, response.mterm, target)
        BY <1>base, <2>epoch, <2>conflict, MessagesMonotonicNext, MessageFieldsTypeOK, SMT
        DEF ConflictingHigherAppendRequest, ConflictingRequestBeforeVote, AppendRequests, TypeOK, MsgTypeOK, ServerVarsTypeOK
    <2>physical. CASE IsPrefix(target, log[response.msource])
        <3>vote. PICK voteRequest \in RecordedVoteRequests(nextVoteHistory, candidate, later)':
                VoteRequestFreshFor(voteRequest, response.msource)
            BY <1>base, <1>new, NewRecordedVoteHasFreshRequest, SMT
        <3>history. CampaignHistory(nextVoteHistory)'
            BY SMT DEF CampaignHistoryContextStep
        <3>fields. voteRequest.mlastLogTerm \in Nat /\ voteRequest.mlastLogIndex \in Nat
            BY <1>base, <3>history, <3>vote, RecordedVoteRequestFieldsAfter, Zenon
        <3>entries. log[response.msource] \in Seq(LogEntry)
            BY <1>base, SMT DEF TypeOK, LogVarsTypeOK
        <3>fresh.
                voteRequest.mlastLogTerm > LastTerm(log[response.msource])
                \/ (voteRequest.mlastLogTerm = LastTerm(log[response.msource])
                    /\ voteRequest.mlastLogIndex >= Len(log[response.msource]))
            BY <3>vote, SMT DEF VoteRequestFreshFor
        <3>covers. VoteRequestCoversPrefix(voteRequest, target)
            BY <1>base, <2>physical, <3>entries, <3>fresh, <3>fields, FreshRequestCoversHeldPrefix, SMT
        <3> QED BY <3>vote, <3>covers, SMT
    <2> QED BY <2>history, <2>conflict, <2>physical, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA FrozenAcknowledgmentVoteCutHistoryInit ==
    Init => FrozenAcknowledgmentVoteCutHistory({}, {})
    BY SMT DEF Init, FrozenAcknowledgmentVoteCutHistory

LEMMA FrozenAcknowledgmentVoteCutHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), FrozenRequestPrefixesAgree(ancestry),
           FrozenAcknowledgmentPrefixHistory(ancestry), FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry)
    PROVE FrozenAcknowledgmentVoteCutHistory(nextVoteHistory, ancestry)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant' /\ WitnessEdgeConsistency(ancestry)
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, OrderedTermPrefixesAreEdgeConsistent, SMT
    DEF MembershipJointCore, JointMembershipWitnesses, ReplicationPrefixInv, ReplicationEvidenceInv,
        MembershipEntryAncestryInv, MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response)
             PROVE \E request \in AppendRequests': \E prefix \in Seq(LogEntry):
                       /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                       /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                       /\ AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
    BY SMT DEF FrozenAcknowledgmentVoteCutHistory, ResponseMatchesRequest, RequestPrefixData, CoveredPrefix
<1>fields. response.msource \in Server /\ response.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
<1>old. CASE response \in messages
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
        BY <1>old, SMT DEF FrozenAcknowledgmentVoteCutHistory
    <2>votes. AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
        BY <1>old, <2>frozen, FrozenAcknowledgmentVoteCutsNext, SMT
    <2> QED BY <2>frozen, <2>votes, MessagesMonotonicNext, SMT DEF AppendRequests
<1>new. CASE response \notin messages
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
        BY <1>base, <1>new, NewAcknowledgmentHasPhysicalPrefix, SMT DEF JointMembershipWitnesses
    <2>epoch. currentTerm'[response.msource] = response.mterm
        BY <1>base, <1>new, NewAcknowledgmentUsesPostTerm, SMT
    <2>votes. AcknowledgmentVoteCuts(nextVoteHistory, prefix, response.msource, response.mterm)'
        BY <1>base, <1>fields, <2>epoch, SMT
        DEF AcknowledgmentVoteCuts, RecordedCampaignVote, Grant, Started, SendInvariant, TypeOK, ServerVarsTypeOK
    <2> QED BY <2>frozen, <2>votes, MessagesMonotonicNext, SMT DEF AppendRequests
<1> QED BY <1>old, <1>new, SMT

LEMMA ReadyCandidateHasNoSameTermAppendRequests ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), OpportunityRequestIntersections(voteHistory), NEW candidate \in Server,
           state[candidate] = Candidate, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support, ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE \A request \in AppendRequests: request.mterm # term
<1>opportunity. OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY ReadyCertificateUsesOpportunity, SMT
<1> SUFFICES ASSUME NEW request \in AppendRequests, request.mterm = term PROVE FALSE BY SMT
<1>certificate. PICK requestSnapshot, requestOccurrence, requestSupport:
        /\ requestSnapshot \in Seq(LogEntry)
        /\ RetainedElectionCertificate(voteHistory, request.msource, term, requestSnapshot, requestOccurrence, requestSupport)
        /\ support \cap requestSupport # {}
    BY <1>opportunity, SMT DEF OpportunityRequestIntersections
<1>source. request.msource = candidate
    BY <1>opportunity, <1>certificate, RecordedSupportMeetsOpportunityOnlyForOwner, SMT
    DEF RetainedElectionCertificate
<1> QED BY <1>source, SMT DEF MembershipJointCore, CandidateAppendFree, ReadyElectionCertificate

LEMMA ReadyCandidateCapturesCausalCertificate ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, FrozenAcknowledgmentVoteCutHistory(voteHistory, ancestry),
           OpportunityRequestIntersections(voteHistory), NEW candidate \in Server, state[candidate] = Candidate,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE CausalElectionCertificate(voteHistory, ancestry, candidate, term, snapshot, occurrence, support)
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1>no_append. \A request \in AppendRequests: request.mterm # term
    BY ReadyCandidateHasNoSameTermAppendRequests, SMT
<1>cut. FrozenElectionAcknowledgmentCut(ancestry, candidate, term, snapshot, support)
    <2> SUFFICES ASSUME NEW response \in messages, SuccessfulAppendResponse(response),
                          response.msource \in support, response.mterm < term
                 PROVE \E request \in AppendRequests: \E prefix \in Seq(LogEntry):
                           /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                           /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                           /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                                  SnapshotCoversPrefix(snapshot, target)
                                  \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)
        BY SMT DEF FrozenElectionAcknowledgmentCut
    <2>fields. response.msource \in Server /\ response.mterm \in Nat
        BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
    <2>vote. RecordedCampaignVote(voteHistory, response.msource, candidate, term)
        BY SMT DEF ReadyElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
            /\ AcknowledgmentVoteCuts(voteHistory, prefix, response.msource, response.mterm)
        BY SMT DEF FrozenAcknowledgmentVoteCutHistory
    <2>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
            SnapshotCoversPrefix(snapshot, target)
            \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)
        <3> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix)
                     PROVE SnapshotCoversPrefix(snapshot, target)
                           \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)
            BY SMT
        <3>history. ConflictingRequestBeforeVote(response.msource, response.mterm, term, target)
                    \/ \E voteRequest \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(voteRequest, target)
            BY <2>fields, <2>vote, <2>frozen, SMT DEF AcknowledgmentVoteCuts
        <3>conflict. CASE ConflictingRequestBeforeVote(response.msource, response.mterm, term, target)
            BY <1>base, <1>no_append, <2>fields, <3>conflict, MessageFieldsTypeOK, SMT
            DEF ConflictingRequestBeforeVote, EarlierConflictingRequest, AppendRequests, TypeOK, MsgTypeOK
        <3>fresh. CASE \E voteRequest \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(voteRequest, target)
            <4>request. PICK voteRequest \in RecordedVoteRequests(voteHistory, candidate, term):
                    VoteRequestCoversPrefix(voteRequest, target)
                BY <3>fresh, SMT
            <4>history. CampaignHistory(voteHistory) /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
                BY SMT DEF ReadyElectionCertificate, RetainedElectionCertificate
            <4>fields.
                    /\ voteRequest.mlastLogTerm = LastTerm(snapshot)
                    /\ voteRequest.mlastLogIndex = Len(snapshot)
                BY <4>request, <4>history, RecordedVoteRequestsUseSnapshot, Zenon
            <4> QED BY <4>request, <4>fields, SMT DEF SnapshotCoversPrefix, VoteRequestCoversPrefix
        <3> QED BY <3>history, <3>conflict, <3>fresh, SMT
    <2> QED BY <2>frozen, <2>targets, SMT
<1> QED BY <1>cut, SMT DEF CausalElectionCertificate, ReadyElectionCertificate

LEMMA CausalElectionCertificateNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW candidate \in Server,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           CausalElectionCertificate(voteHistory, ancestry, candidate, term, snapshot, occurrence, support)
    PROVE CausalElectionCertificate(nextVoteHistory, ancestry, candidate, term, snapshot, occurrence, support)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ SendInvariant'
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1>retained. RetainedElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    BY <1>base, RetainedElectionCertificateNext, SMT DEF CausalElectionCertificate
<1>cut. FrozenElectionAcknowledgmentCut(ancestry, candidate, term, snapshot, support)'
    <2> SUFFICES ASSUME NEW response \in messages', SuccessfulAppendResponse(response),
                          response.msource \in support, response.mterm < term
                 PROVE \E request \in AppendRequests': \E prefix \in Seq(LogEntry):
                           /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                           /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                           /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                                  SnapshotCoversPrefix(snapshot, target)
                                  \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)'
        BY SMT DEF FrozenElectionAcknowledgmentCut, ResponseMatchesRequest, RequestPrefixData, CoveredPrefix
    <2>fields. response.msource \in Server /\ response.mterm \in Nat
        BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK
    <2>old. CASE response \in messages
        <3>frozen. PICK request, prefix:
                /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
                /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                       SnapshotCoversPrefix(snapshot, target)
                       \/ EarlierConflictingRequest(response.msource, response.mterm, term, target)
            BY <2>old, SMT DEF CausalElectionCertificate, FrozenElectionAcknowledgmentCut
        <3> QED BY <3>frozen, MessagesMonotonicNext, SMT DEF AppendRequests, EarlierConflictingRequest
    <2>new. CASE response \notin messages
        <3>epoch. currentTerm'[response.msource] = response.mterm
            BY <1>base, <2>new, NewAcknowledgmentUsesPostTerm, SMT
        <3> QED BY <1>base, <1>retained, <2>fields, <3>epoch, SMT
            DEF RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote,
                Grant, Started, SendInvariant, TypeOK, ServerVarsTypeOK
    <2> QED BY <2>old, <2>new, SMT
<1> QED BY <1>retained, <1>cut, SMT DEF CausalElectionCertificate

LEMMA OlderPrefixInsideCampaignSnapshot ==
    ASSUME NEW entries \in Seq(LogEntry), NEW prefix \in Seq(LogEntry),
           IsPrefix(prefix, entries), Len(prefix) > 0, NEW term \in Nat, LastTerm(prefix) < term
    PROVE IsPrefix(prefix, CampaignPrefix(entries, term))
<1>last. Len(prefix) \in DOMAIN entries /\ entries[Len(prefix)].term = LastTerm(prefix)
    BY PrefixEntryEqual, LenProperties, SMT DEF IsPrefix, LastTerm
<1>index. Len(prefix) \in PreTermIndexes(entries, term)
    BY <1>last, SMT DEF PreTermIndexes
<1>bound. Len(prefix) <= CampaignPrefixIndex(entries, term)
    BY <1>index, PreTermIndexProperties, SMT
<1>snapshot.
        /\ CampaignPrefix(entries, term) \in Seq(LogEntry)
        /\ IsPrefix(CampaignPrefix(entries, term), entries)
        /\ Len(CampaignPrefix(entries, term)) = CampaignPrefixIndex(entries, term)
    BY PreTermIndexProperties, SubSeqTypeOK, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF CampaignPrefix, IsPrefix
<1> QED BY <1>bound, <1>snapshot, PrefixesWithBoundedLength, SMT

LEMMA CampaignContainsOlderProtectedPrefix ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), CampaignOpportunity(candidate, term, snapshot),
           NEW prefix \in Seq(LogEntry), IsPrefix(prefix, log[candidate]),
           Len(prefix) > 0, LastTerm(prefix) < term
    PROVE IsPrefix(prefix, snapshot)
<1>base. log[candidate] \in Seq(LogEntry) BY JointCoreBase, SMT DEF TypeOK, LogVarsTypeOK
<1>future. CASE currentTerm[candidate] < term
    BY <1>future, SMT DEF CampaignOpportunity
<1>current. CASE currentTerm[candidate] = term
    BY <1>base, <1>current, OlderPrefixInsideCampaignSnapshot, SMT DEF CampaignOpportunity
<1> QED BY <1>future, <1>current, SMT DEF CampaignOpportunity

LEMMA RetainedCommitReplicasHoldTarget ==
    ASSUME NEW voteHistory, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW certificate \in commits
    PROVE /\ CommitTarget(certificate) \in Seq(LogEntry)
          /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
<1>certificate. RetainedCommitCertificate(voteHistory, certificate)
    BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>target.
        /\ CommitTarget(certificate) \in Seq(LogEntry)
        /\ Len(CommitTarget(certificate)) = certificate.index
        /\ Len(CommitTarget(certificate)) > 0
        /\ LastTerm(CommitTarget(certificate)) = certificate.term
    BY <1>certificate, CommitCertificateTargetProperties, LenProperties, SMT
    DEF RetainedCommitCertificate, LastTerm
<1>recorded. certificate.replication \subseteq
        RecordedReplicationSupport(certificate.leader, certificate.term, certificate.index)
    BY <1>certificate, CommitCertificateSuppliesRecordedSupport, SMT DEF CommitCertificateRecordedSupport
<1> QED BY <1>target, <1>recorded, SMT
    DEF JointMembershipWitnesses, JointCommitProtection, RecordedAcknowledgersProtected

\* The predecessor configuration of every retained configuration edge has
\* global evidence, even if its original leader has since retired.
LEMMA ConfigurationBarrierPredecessorIsAgreed ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits,
           JointMembershipWitnesses(voteHistory, ancestry, commits), NEW witness \in ancestry,
           witness.edge.entry.members # Nil
    PROVE LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
              \in EvidenceConfigurationHistory(voteHistory)
<1>base. TypeOK BY JointCoreBase, SMT
<1>barrier. PICK certificate \in commits: ConfigurationBarrierFor(witness, certificate)
    BY SMT DEF JointMembershipWitnesses, ConfigurationBarrierAncestry
<1>certificate. RetainedCommitCertificate(voteHistory, certificate)
    BY <1>barrier, SMT DEF JointMembershipWitnesses, CommitCertificateFamily
<1>holds. IsPrefix(CommitTarget(certificate), log[certificate.leader])
    BY <1>barrier, <1>certificate, SMT
    DEF JointMembershipWitnesses, JointCommitProtection, RecordedAcknowledgersProtected,
        RecordedReplicationSupport, ProtectedVoters, RetainedCommitCertificate
<1>trimmed. PICK reduced:
        /\ RetainedCommitCertificate(voteHistory, reduced) /\ reduced.leader = certificate.leader
        /\ reduced.entries = CommitTarget(certificate)
        /\ reduced.index = Len(CommitTarget(certificate))
        /\ reduced.configuration = certificate.configuration
    BY <1>base, <1>barrier, <1>certificate, CertificateTargetWithConfigurationCanBeTrimmed, SMT
    DEF ConfigurationBarrierFor
<1>supported. SupportedAgreementTarget(voteHistory, CommitTarget(certificate))
    BY <1>holds, <1>trimmed, <1>certificate, CommitCertificateTargetProperties, SMT
    DEF SupportedAgreementTarget
<1>target. CommitTarget(certificate) \in EvidenceAgreementTargets(voteHistory)
    BY <1>base, <1>certificate, <1>supported, CommitCertificateTargetProperties,
       SupportedTargetInEvidenceSet, SMT
<1>configuration. LatestConfigurationOccurrence(CommitTarget(certificate)) = certificate.configuration
    BY <1>certificate, <1>trimmed, SMT DEF RetainedCommitCertificate
<1> QED BY <1>barrier, <1>target, <1>configuration, SMT
    DEF ConfigurationBarrierFor, EvidenceConfigurationHistory, ConfigurationHistory

LEMMA RecordedCampaignVoteCandidateTermBound ==
    ASSUME NEW voteHistory, TypeOK, SendInvariant, PositiveVoteResponseRequestInv,
           NEW voter \in Server, NEW candidate \in Server, NEW term \in Nat,
           RecordedCampaignVote(voteHistory, voter, candidate, term)
    PROVE term <= currentTerm[candidate]
    BY SMT DEF RecordedCampaignVote, Grant, Started, PositiveVoteResponseRequestInv, SendInvariant

LEMMA RecordedOpportunityUsesHistorySnapshot ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW peer \in Server,
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
           RecordedCampaignVote(voteHistory, peer, candidate, term)
    PROVE HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
<1>base. TypeOK /\ SendInvariant /\ PositiveVoteResponseRequestInv /\ CampaignHistory(voteHistory)
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv
<1>epoch. term <= currentTerm[candidate]
    BY <1>base, RecordedCampaignVoteCandidateTermBound, SMT
<1> QED BY <1>base, <1>epoch, SMT
    DEF OpportunityCertificate, CampaignOpportunity, CampaignHistory, HistoryCampaignSnapshot, TypeOK, ServerVarsTypeOK

LEMMA OlderConfigurationCannotContainNewerParentTarget ==
    ASSUME NEW entries \in Seq(LogEntry), TermsOrdered(entries),
           NEW target \in Seq(LogEntry), Len(target) > 0, NEW parent,
           ConfigurationOccurrenceData(parent), LatestConfigurationOccurrence(target) = parent,
           LatestConfigurationOccurrence(entries).index > parent.index,
           LastTerm(LatestConfigurationOccurrence(entries).prefix) < LastTerm(target),
           IsPrefix(target, entries)
    PROVE FALSE
<1>latest.
        /\ ConfigurationOccurrenceData(LatestConfigurationOccurrence(entries))
        /\ IsPrefix(LatestConfigurationOccurrence(entries).prefix, entries)
        /\ LastConfigChangeIndex(LatestConfigurationOccurrence(entries).prefix) =
               LatestConfigurationOccurrence(entries).index
    BY LatestConfigurationOccurrenceData, ConfigurationOccurrencePrefixIndex,
       ConfigurationIndexProperties, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF LatestConfigurationOccurrence, IsPrefix
<1>types.
        /\ Len(target) \in Nat /\ LastTerm(target) \in Nat
        /\ LatestConfigurationOccurrence(entries).index \in Nat
        /\ LastTerm(LatestConfigurationOccurrence(entries).prefix) \in Nat
        /\ parent.index \in Nat
    BY <1>latest, LenProperties, LastTermTypeOK, SMT DEF ConfigurationOccurrenceData
<1>long. CASE LatestConfigurationOccurrence(entries).index <= Len(target)
    <2>prefix. IsPrefix(LatestConfigurationOccurrence(entries).prefix, target)
        BY <1>latest, <1>long, PrefixesWithBoundedLength, SMT DEF ConfigurationOccurrenceData
    <2>order. LatestConfigurationOccurrence(entries).index <= parent.index
        BY <1>latest, <2>prefix, PrefixConfigurationIndexMonotonic, SMT
        DEF LatestConfigurationOccurrence, ConfigurationOccurrenceData
    <2> QED BY <1>types, <2>order, SMT
<1>short. CASE Len(target) < LatestConfigurationOccurrence(entries).index
    <2>prefix. IsPrefix(target, LatestConfigurationOccurrence(entries).prefix)
        BY <1>latest, <1>short, PrefixesWithBoundedLength, SMT DEF ConfigurationOccurrenceData
    <2>ordered. TermsOrdered(LatestConfigurationOccurrence(entries).prefix)
        BY <1>latest, TermsOrderedOnPrefix, LenProperties, SMT
        DEF ConfigurationOccurrenceData, IsPrefix
    <2> QED BY <1>latest, <1>types, <2>prefix, <2>ordered, OrderedPrefixLastTermBound, SMT
        DEF ConfigurationOccurrenceData
<1> QED BY <1>types, <1>long, <1>short, SMT

LEMMA ConfigurationPrefixesWithSameParentAreUnique ==
    ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           Len(left) > 0, Len(right) > 0, LastConfigChangeIndex(left) = Len(left),
           LatestConfigurationOccurrence(SubSeq(left, 1, Len(left) - 1)) =
               LatestConfigurationOccurrence(SubSeq(right, 1, Len(right) - 1)),
           IsPrefix(left, right)
    PROVE left = right
<1>lengths. Len(left) \in Nat /\ Len(right) \in Nat /\ Len(left) <= Len(right)
    BY LenProperties, SMT DEF IsPrefix
<1>before. PICK before \in Seq(LogEntry): before = SubSeq(right, 1, Len(right) - 1)
    BY SubSeqTypeOK, LenProperties, SMT
<1>upper. LastConfigChangeIndex(before) < Len(left)
    BY <1>before, ConfigurationIndexProperties, SubSeqTypeOK, LenProperties, SMT
    DEF LatestConfigurationOccurrence
<1>shorter. CASE Len(left) < Len(right)
    <2>prefix. IsPrefix(left, before)
        BY <1>lengths, <1>before, <1>shorter, SubSeqProperties, ElementOfSeq,
           PrefixesWithBoundedLength, LenProperties, SMT DEF IsPrefix
    <2>lower. Len(left) <= LastConfigChangeIndex(before)
        BY <1>before, <2>prefix, PrefixConfigurationIndexMonotonic, SMT
    <2> QED BY <1>lengths, <1>before, <1>upper, <2>lower,
        ConfigurationIndexProperties, SMT
<1>same. CASE Len(left) = Len(right)
    BY <1>same, WholeSequencePrefix, SMT DEF IsPrefix
<1> QED BY <1>lengths, <1>shorter, <1>same, SMT

=======================================================================
