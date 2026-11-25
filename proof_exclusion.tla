------------------------------ MODULE proof_exclusion ------------------------------
\* proof_exclusion.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_joint_core

LOCAL INSTANCE NaturalsInduction

RequestSourcePrefixHistory(ancestry) ==
    \A request \in AppendRequests: \E prefix \in Seq(LogEntry):
        /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
               IsPrefix(target, log[request.msource])
               \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)

RequestSourceVoteCutHistory(voteHistory, ancestry) ==
    \A request \in AppendRequests: \E prefix \in Seq(LogEntry):
        /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ AcknowledgmentVoteCuts(voteHistory, prefix, request.msource, request.mterm)


LocalAppendRecordsCovered(voteHistory, ancestry) ==
    \A record \in voteHistory: LocalAppendRecord(record) =>
        /\ record.prefix \in Seq(LogEntry)
        /\ \E witness \in ancestry:
               /\ witness.prefix = record.prefix /\ witness.owner = record.candidate
               /\ witness.edge.term = record.term /\ witness.snapshot = record.snapshot

LocalAppendRequestOwnersUnique(voteHistory) ==
    \A record \in voteHistory: LocalAppendRecord(record) =>
        \A request \in AppendRequests:
            request.mterm = record.term => request.msource = record.candidate

LocalAppendPrefixHistory(voteHistory) ==
    \A record \in voteHistory: LocalAppendRecord(record) =>
        \A target \in Seq(LogEntry): IsPrefix(target, record.prefix) =>
            IsPrefix(target, log[record.candidate])
            \/ ConflictingHigherAppendRequest(record.candidate, record.term, target)

LocalAppendVoteCutHistory(voteHistory) ==
    \A record \in voteHistory: LocalAppendRecord(record) =>
        AcknowledgmentVoteCuts(voteHistory, record.prefix, record.candidate, record.term)

LocalAppendElectionCut(voteHistory, term, snapshot, support) ==
    \A record \in voteHistory:
        /\ LocalAppendRecord(record) /\ record.candidate \in support /\ record.term < term
        => \A target \in Seq(LogEntry): IsPrefix(target, record.prefix) =>
               SnapshotCoversPrefix(snapshot, target)
               \/ EarlierConflictingRequest(record.candidate, record.term, term, target)

RequestSourceElectionCut(ancestry, candidate, term, snapshot, support) ==
    \A original \in AppendRequests:
        original.msource \in support /\ original.mterm < term =>
            \E prefix \in Seq(LogEntry):
                /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
                /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                       SnapshotCoversPrefix(snapshot, target)
                       \/ EarlierConflictingRequest(original.msource, original.mterm, term, target)

PrefixWitnessFamilyData(ancestry) ==
    /\ \A witness \in ancestry: WitnessPrefixData(witness)
    /\ \A witness \in ancestry: \A index \in DOMAIN witness.prefix:
           \E ancestor \in ancestry: ancestor.edge = LogEntryEdge(witness.prefix, index)

CommitPrefixData(certificate) ==
    /\ certificate.entries \in Seq(LogEntry) /\ certificate.term \in Nat
    /\ certificate.index \in 1..Len(certificate.entries)
    /\ certificate.entries[certificate.index].term = certificate.term
    /\ TermsOrdered(certificate.entries)
    /\ certificate.configuration = LatestConfigurationOccurrence(certificate.entries)

BarrierFrontierData(ancestry, commits, working) ==
    /\ PrefixWitnessFamilyData(ancestry) /\ TermPrefixOrder(ancestry)
    /\ ConfigurationOccurrenceData(working)
    /\ LastConfigChangeIndex(working.prefix) = working.index
    /\ ConfigurationBarrierAncestry(ancestry, commits)
    /\ \A certificate \in commits: CommitPrefixData(certificate)
    /\ \A witness \in ancestry: witness.edge.entry.members # Nil =>
           LET predecessor == LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
           IN /\ predecessor.index <= working.index
              /\ IsPrefix(predecessor.prefix, working.prefix)

TermAncestry(ancestry, term) == {witness \in ancestry: witness.edge.term <= term}

TermCommits(commits, term) == {certificate \in commits: certificate.term <= term}

TermBarrierHistory(ancestry, term) ==
    {InitialConfigurationOccurrence} \cup
    {LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1)):
        witness \in {entry \in TermAncestry(ancestry, term): entry.edge.entry.members # Nil}}

TermWorkingConfiguration(ancestry, term) == LatestEvidenceOccurrence(TermBarrierHistory(ancestry, term))

TermProtectedPrefix(ancestry, commits, term, entries) ==
    /\ entries \in Seq(LogEntry) /\ TermsOrdered(entries) /\ CoveredPrefix(ancestry, entries)
    /\ \A index \in DOMAIN entries: entries[index].term <= term
    /\ \A certificate \in TermCommits(commits, term): IsPrefix(CommitTarget(certificate), entries)

CausalCampaignData(voteHistory, ancestry, campaign) ==
    /\ campaign.candidate \in Server /\ campaign.term \in Nat /\ campaign.snapshot \in Seq(LogEntry)
    /\ CausalElectionCertificate(voteHistory, ancestry, campaign.candidate, campaign.term,
                                campaign.snapshot, campaign.occurrence, campaign.support)
    /\ RequestSourceElectionCut(ancestry, campaign.candidate, campaign.term, campaign.snapshot, campaign.support)
    /\ LocalAppendElectionCut(voteHistory, campaign.term, campaign.snapshot, campaign.support)
    /\ CoveredPrefix(ancestry, campaign.snapshot) /\ TermsOrdered(campaign.snapshot)

CreatorCampaignCoverage(ancestry, campaigns) ==
    \A witness \in ancestry: \E campaign \in campaigns:
        /\ campaign.candidate = witness.owner /\ campaign.term = witness.edge.term
        /\ campaign.snapshot = witness.snapshot

RequestCampaignCoverage(ancestry, campaigns) ==
    \A request \in AppendRequests: \E campaign \in campaigns: \E prefix \in Seq(LogEntry):
        /\ campaign.candidate = request.msource /\ campaign.term = request.mterm
        /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ (IsPrefix(campaign.snapshot, prefix) \/ IsPrefix(prefix, campaign.snapshot))

CampaignCommitPrefixes(commits, campaigns) ==
    \A certificate \in commits: \A campaign \in campaigns:
        certificate.term < campaign.term => IsPrefix(CommitTarget(certificate), campaign.snapshot)

CommitPrefixCoverage(ancestry, commits) ==
    \A certificate \in commits: CoveredPrefix(ancestry, certificate.entries)

CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns) ==
    /\ \A campaign \in campaigns: CausalCampaignData(voteHistory, ancestry, campaign)
    /\ CreatorCampaignCoverage(ancestry, campaigns)
    /\ RequestCampaignCoverage(ancestry, campaigns)
    /\ CampaignCommitPrefixes(commits, campaigns)
    /\ CommitPrefixCoverage(ancestry, commits)

RecordedTargetCampaignIntersections(leader, term, target, support, campaigns) ==
    \A campaign \in campaigns: term < campaign.term =>
        \A peer \in support \cap campaign.support:
            \E response \in messages:
                /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
                /\ response.mterm = term /\ response.mmatchIndex >= Len(target)

CommitLogData(certificate) ==
    /\ CommitPrefixData(certificate) /\ EntryStructure(certificate.entries, certificate.term)
    /\ certificate.configuration.members \subseteq Server
    /\ certificate.replication \in Quorums(certificate.configuration.members)

PairAncestry(ancestry, left, right) ==
    {witness \in ancestry: IsPrefix(witness.prefix, left) \/ IsPrefix(witness.prefix, right)}

FamilyBarriers(ancestry, commits) ==
    {certificate \in commits: \E witness \in ancestry:
        witness.edge.entry.members # Nil /\ ConfigurationBarrierFor(witness, certificate)}

FamilyParentHistory(ancestry) ==
    {InitialConfigurationOccurrence} \cup
    {LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1)):
        witness \in {entry \in ancestry: entry.edge.entry.members # Nil}}

BarrierExclusionData(ancestry, commits) ==
    /\ IsFiniteSet(ancestry) /\ PrefixWitnessFamilyData(ancestry) /\ TermPrefixOrder(ancestry)
    /\ ConfigurationBarrierAncestry(ancestry, commits)
    /\ \A certificate \in commits:
           /\ CommitLogData(certificate) /\ CoveredPrefix(ancestry, certificate.entries)
           /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)

LEMMA RequestSourceHistoriesInit ==
    Init => RequestSourcePrefixHistory({}) /\ RequestSourceVoteCutHistory({}, {})
    BY SMT DEF Init, RequestSourcePrefixHistory, RequestSourceVoteCutHistory, AppendRequests

LEMMA RequestSourceTargetNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, AppendRequestOwnersUnique,
           NEW original \in AppendRequests, NEW target \in Seq(LogEntry),
           IsPrefix(target, log[original.msource]), currentTerm[original.msource] >= original.mterm
    PROVE IsPrefix(target, log'[original.msource])
          \/ ConflictingHigherAppendRequest(original.msource, original.mterm, target)'
<1>base. TypeOK /\ EntryEdgeBase /\ SendInvariant /\ original.msource \in Server /\ original.mterm \in Nat
    BY JointCoreBase, MessageFieldsTypeOK, SMT DEF MembershipJointCore, AppendRequests, TypeOK, MsgTypeOK
<1>conflict. CASE ConflictingHigherAppendRequest(original.msource, original.mterm, target)'
    BY <1>conflict, SMT
<1>no_conflict. CASE ~ConflictingHigherAppendRequest(original.msource, original.mterm, target)'
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
        <3>fields. request \in AppendRequests /\ request.msource \in Server /\ request.mdest \in Server /\ request.mterm \in Nat
            BY <1>base, <3>request, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
        <3>recipient. CASE request.mdest = original.msource
            <4>different. request.mterm # original.mterm
                BY <1>base, <3>fields, <3>recipient, SMT DEF AppendRequestOwnersUnique, SendInvariant, AppendRequests
            <4>higher. request.mterm > original.mterm => RequestRespectsPrefix(request, target)
                <5> SUFFICES ASSUME request.mterm > original.mterm
                             PROVE RequestRespectsPrefix(request, target) BY SMT
                <5>retained. request \in AppendRequests'
                    BY <1>base, <3>fields, MessagesMonotonicNext, SMT DEF AppendRequests
                <5>epoch. request.mterm <= currentTerm'[original.msource]
                    BY <1>base, <3>request, <3>fields, <3>recipient, SMT
                    DEF HandleAppendEntriesRequest, TypeOK, ServerVarsTypeOK
                <5> QED BY <1>no_conflict, <3>recipient, <5>retained, <5>epoch, SMT
                    DEF ConflictingHigherAppendRequest
            <4> QED BY <1>base, <3>request, <3>fields, <3>recipient, <4>different, <4>higher,
                AppendRequestPreservesProtectedPrefix, SMT
        <3>other. CASE request.mdest # original.msource
            BY <1>base, <3>request, <3>other, HandleAppendEntriesRequestPreservesOtherServer, SMT
        <3> QED BY <3>recipient, <3>other, SMT
    <2>same. CASE UNCHANGED log BY <2>same, SMT
    <2> QED BY <1>base, <2>client, <2>receive, <2>same, LogChangingActionNext, SMT
<1> QED BY <1>conflict, <1>no_conflict, SMT

LEMMA VoteCutsWithPrefixHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW peer \in Server, NEW term \in Nat, NEW prefix \in Seq(LogEntry),
           AcknowledgmentVoteCuts(voteHistory, prefix, peer, term),
           \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
               IsPrefix(target, log[peer]) \/ ConflictingHigherAppendRequest(peer, term, target)
    PROVE AcknowledgmentVoteCuts(nextVoteHistory, prefix, peer, term)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant' /\ TermsOrdered(log[peer])
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix), NEW candidate \in Server,
                      NEW later \in Nat, term < later, RecordedCampaignVote(nextVoteHistory, peer, candidate, later)'
             PROVE ConflictingRequestBeforeVote(peer, term, later, target)'
                   \/ \E request \in RecordedVoteRequests(nextVoteHistory, candidate, later)': VoteRequestCoversPrefix(request, target)
    BY SMT DEF AcknowledgmentVoteCuts
<1>old. CASE RecordedCampaignVote(voteHistory, peer, candidate, later)
    BY <1>old, MessagesMonotonicNext, SMT
    DEF AcknowledgmentVoteCuts, ConflictingRequestBeforeVote, AppendRequests, RecordedCampaignRequests, RecordedVoteRequests, CampaignHistoryContextStep, CampaignHistoryStep
<1>new. CASE ~RecordedCampaignVote(voteHistory, peer, candidate, later)
    <2>epoch. currentTerm[peer] <= later BY <1>base, <1>new, NewRecordedVotePreEpochBound, SMT
    <2>conflict. CASE ConflictingHigherAppendRequest(peer, term, target)
        BY <1>base, <2>epoch, <2>conflict, MessageFieldsTypeOK, MessagesMonotonicNext, SMT
        DEF ConflictingHigherAppendRequest, ConflictingRequestBeforeVote, AppendRequests, TypeOK, MsgTypeOK, ServerVarsTypeOK
    <2>physical. CASE IsPrefix(target, log[peer])
        <3>request. PICK request \in RecordedVoteRequests(nextVoteHistory, candidate, later)': VoteRequestFreshFor(request, peer)
            BY <1>base, <1>new, NewRecordedVoteHasFreshRequest, SMT
        <3>types. log[peer] \in Seq(LogEntry) /\ request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
            <4>history. CampaignHistory(nextVoteHistory)'
                BY SMT DEF CampaignHistoryContextStep
            <4>fields. request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
                BY <1>base, <4>history, <3>request, RecordedVoteRequestFieldsAfter, Zenon
            <4>entries. log[peer] \in Seq(LogEntry)
                BY <1>base, SMT DEF TypeOK, LogVarsTypeOK
            <4> QED BY <4>fields, <4>entries, SMT
        <3>covers. VoteRequestCoversPrefix(request, target)
            BY <1>base, <2>physical, <3>request, <3>types, FreshRequestCoversHeldPrefix, SMT DEF VoteRequestFreshFor
        <3> QED BY <3>request, <3>covers, SMT
    <2> QED BY <2>conflict, <2>physical, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA RequestSourceFixedTargetHistory ==
    ASSUME NEW voteHistory, TypeOK, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits), RequestSourcePrefixHistory(ancestry),
           NEW request \in AppendRequests, NEW prefix \in Seq(LogEntry), RequestPrefixData(request, prefix), CoveredPrefix(ancestry, prefix)
    PROVE \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
               IsPrefix(target, log[request.msource]) \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)
<1>frozen. PICK frozen \in Seq(LogEntry):
        /\ RequestPrefixData(request, frozen) /\ CoveredPrefix(ancestry, frozen)
        /\ \A target \in Seq(LogEntry): IsPrefix(target, frozen) =>
               IsPrefix(target, log[request.msource]) \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)
    BY SMT DEF RequestSourcePrefixHistory
<1>equal. prefix = frozen
    BY <1>frozen, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
    DEF JointMembershipWitnesses, TypeOK, MsgTypeOK, AppendRequests
<1> QED BY <1>frozen, <1>equal, SMT

LEMMA RequestSourceHistoriesNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           AppendRequestOwnersUnique, RequestSourcePrefixHistory(ancestry), RequestSourceVoteCutHistory(voteHistory, ancestry)
    PROVE RequestSourcePrefixHistory(ancestry)' /\ RequestSourceVoteCutHistory(nextVoteHistory, ancestry)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant /\ SendInvariant' /\ EntryEdgeBase /\ ReplicationEvidenceInv(voteHistory)
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW request \in AppendRequests'
             PROVE /\ \E prefix \in Seq(LogEntry):
                          /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
                          /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                                 IsPrefix(target, log'[request.msource])
                                 \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)'
                   /\ \E prefix \in Seq(LogEntry):
                          /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
                          /\ AcknowledgmentVoteCuts(nextVoteHistory, prefix, request.msource, request.mterm)'
    BY Isa DEF RequestSourcePrefixHistory, RequestSourceVoteCutHistory, RequestPrefixData, CoveredPrefix
<1>old. CASE request \in messages
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
            /\ AcknowledgmentVoteCuts(voteHistory, prefix, request.msource, request.mterm)
        BY <1>old, SMT DEF RequestSourceVoteCutHistory, AppendRequests
    <2>fields. request \in AppendRequests /\ request.msource \in Server /\ request.mterm \in Nat
                /\ request.mterm <= currentTerm[request.msource]
        BY <1>base, <1>old, MessageFieldsTypeOK, SMT DEF AppendRequests, TypeOK, MsgTypeOK, SendInvariant
    <2>history. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
            IsPrefix(target, log[request.msource]) \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)
        BY <1>base, <2>prefix, <2>fields, RequestSourceFixedTargetHistory, SMT
    <2>after. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
            IsPrefix(target, log'[request.msource]) \/ ConflictingHigherAppendRequest(request.msource, request.mterm, target)'
        BY <1>base, <2>fields, <2>history, RequestSourceTargetNext, ConflictingHigherAppendRequestRetained, SMT
    <2>cuts. AcknowledgmentVoteCuts(nextVoteHistory, prefix, request.msource, request.mterm)'
        BY <2>prefix, <2>fields, <2>history, VoteCutsWithPrefixHistoryNext, SMT
    <2> QED BY <2>prefix, <2>after, <2>cuts, SMT
<1>new. CASE request \notin messages
    <2>origin. PICK actor, peer \in Server:
            /\ AppendEntries(actor, peer) /\ request = AppendEntriesMessage(actor, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>ancestry. AncestralRequestPrefix(nextVoteHistory, ancestry, request)'
        BY <1>base, <2>origin, NewAppendRequestHasAncestralPrefix, SMT DEF JointMembershipWitnesses
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(request, prefix) /\ CoveredPrefix(ancestry, prefix)
            /\ IsPrefix(prefix, log'[request.msource])
        BY <2>ancestry, <2>origin, SMT
        DEF AncestralRequestPrefix, OwnerPrefix, AppendEntries, AppendEntriesMessage, RequestPrefixData, CoveredPrefix
    <2>cuts. AcknowledgmentVoteCuts(nextVoteHistory, prefix, request.msource, request.mterm)'
        BY <1>base, <2>origin, SMT
        DEF AcknowledgmentVoteCuts, RecordedCampaignVote, Grant, Started, SendInvariant,
            AppendEntries, AppendEntriesMessage, TypeOK, ServerVarsTypeOK
    <2>after. \A target \in Seq(LogEntry): IsPrefix(target, prefix) => IsPrefix(target, log'[request.msource])
        BY <1>base, <2>origin, <2>prefix, SequencePrefixTransitive, SMT
        DEF AppendEntriesMessage, TypeOK, LogVarsTypeOK
    <2> QED BY <2>prefix, <2>cuts, <2>after, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA LocalAppendHistoriesInit ==
    Init => /\ LocalAppendRecordsCovered({}, {}) /\ LocalAppendRequestOwnersUnique({})
            /\ LocalAppendPrefixHistory({}) /\ LocalAppendVoteCutHistory({})
    BY SMT DEF LocalAppendRecordsCovered, LocalAppendRequestOwnersUnique,
        LocalAppendPrefixHistory, LocalAppendVoteCutHistory

LEMMA NewLocalAppendRecordOrigin ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           NEW record \in nextVoteHistory \ voteHistory, LocalAppendRecord(record)
    PROVE \E actor \in Server, payload \in ClientPayload:
        /\ ClientRequest(actor, payload) /\ record.candidate = actor /\ record.term = currentTerm[actor]
        /\ record.snapshot = CampaignPrefix(log[actor], currentTerm[actor]) /\ record.prefix = log'[actor]
    BY SMT DEF CampaignHistoryContextStep, CampaignHistoryStep, LocalAppendRecord

LEMMA ContinuingLeadersExcludeClientAppend ==
    ASSUME TypeOK, ContinuingLeadersKeepLogs
    PROVE ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
<1> SUFFICES ASSUME NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
             PROVE FALSE BY SMT
<1>length. Len(log'[actor]) = Len(log[actor]) + 1 /\ Len(log[actor]) \in Nat
    BY ClientRequestAppendsCurrentTerm, AppendProperties, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>length, SMT DEF ContinuingLeadersKeepLogs, ClientRequest

LEMMA LocalSourceTargetNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW owner \in Server, NEW term \in Nat,
           \A request \in AppendRequests: request.mterm = term => request.msource = owner,
           NEW target \in Seq(LogEntry),
           IsPrefix(target, log[owner]), currentTerm[owner] >= term
    PROVE IsPrefix(target, log'[owner])
          \/ ConflictingHigherAppendRequest(owner, term, target)'
<1>base. TypeOK /\ EntryEdgeBase /\ SendInvariant
    BY JointCoreBase, SMT DEF MembershipJointCore
<1>conflict. CASE ConflictingHigherAppendRequest(owner, term, target)'
    BY <1>conflict, SMT
<1>no_conflict. CASE ~ConflictingHigherAppendRequest(owner, term, target)'
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
        <3>fields. request \in AppendRequests /\ request.msource \in Server /\ request.mdest \in Server /\ request.mterm \in Nat
            BY <1>base, <3>request, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
        <3>recipient. CASE request.mdest = owner
            <4>different. request.mterm # term
                BY <1>base, <3>fields, <3>recipient, SMT DEF SendInvariant, AppendRequests
            <4>higher. request.mterm > term => RequestRespectsPrefix(request, target)
                <5> SUFFICES ASSUME request.mterm > term
                             PROVE RequestRespectsPrefix(request, target) BY SMT
                <5>retained. request \in AppendRequests'
                    BY <1>base, <3>fields, MessagesMonotonicNext, SMT DEF AppendRequests
                <5>epoch. request.mterm <= currentTerm'[owner]
                    BY <1>base, <3>request, <3>fields, <3>recipient, SMT
                    DEF HandleAppendEntriesRequest, TypeOK, ServerVarsTypeOK
                <5> QED BY <1>no_conflict, <3>recipient, <5>retained, <5>epoch, SMT
                    DEF ConflictingHigherAppendRequest
            <4> QED BY <1>base, <3>request, <3>fields, <3>recipient, <4>different, <4>higher,
                AppendRequestPreservesProtectedPrefix, SMT
        <3>other. CASE request.mdest # owner
            BY <1>base, <3>request, <3>other, HandleAppendEntriesRequestPreservesOtherServer, SMT
        <3> QED BY <3>recipient, <3>other, SMT
    <2>same. CASE UNCHANGED log BY <2>same, SMT
    <2> QED BY <1>base, <2>client, <2>receive, <2>same, LogChangingActionNext, SMT
<1> QED BY <1>conflict, <1>no_conflict, SMT

LEMMA LocalAppendOwnersNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars,
           NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           LocalAppendRecordsCovered(voteHistory, ancestry), LocalAppendRequestOwnersUnique(voteHistory)
    PROVE LocalAppendRequestOwnersUnique(nextVoteHistory)'
<1>base. TypeOK /\ EntryEdgeBase /\ CurrentRequestSendersUnique
    BY JointCoreBase, IntersectingRequestCertificatesIdentifySenders, SMT DEF MembershipJointCore
<1> SUFFICES ASSUME NEW record \in nextVoteHistory, LocalAppendRecord(record),
                      NEW request \in AppendRequests', request.mterm = record.term
             PROVE request.msource = record.candidate
    BY SMT DEF LocalAppendRequestOwnersUnique
<1>old. CASE record \in voteHistory
    <2>old_request. CASE request \in messages
        BY <1>old, <2>old_request, SMT DEF LocalAppendRequestOwnersUnique, AppendRequests
    <2>new_request. CASE request \notin messages
        <3>origin. PICK leader, peer \in Server:
            AppendEntries(leader, peer) /\ request = AppendEntriesMessage(leader, peer)
            BY <1>base, <2>new_request, NewAppendRequestOrigin, SMT DEF AppendRequests
        <3>witness. PICK witness \in ancestry:
            /\ witness.prefix = record.prefix /\ witness.owner = record.candidate
            /\ witness.edge.term = record.term
            BY <1>old, SMT DEF LocalAppendRecordsCovered
        <3>owner. witness.owner = leader
            BY <3>origin, <3>witness, LiveAncestryIdentifiesCurrentOwners, SMT
            DEF AppendEntries, AppendEntriesMessage
        <3> QED BY <3>origin, <3>witness, <3>owner, SMT DEF AppendEntriesMessage
    <2> QED BY <2>old_request, <2>new_request, SMT
<1>new. CASE record \notin voteHistory
    <2>origin. PICK actor \in Server, payload \in ClientPayload:
        /\ ClientRequest(actor, payload) /\ record.candidate = actor /\ record.term = currentTerm[actor]
        /\ record.snapshot = CampaignPrefix(log[actor], currentTerm[actor]) /\ record.prefix = log'[actor]
        BY <1>base, <1>new, NewLocalAppendRecordOrigin, SMT
    <2> QED BY <1>base, <2>origin, SMT
        DEF CurrentRequestSendersUnique, AppendRequests, ClientRequest
<1> QED BY <1>old, <1>new, SMT

LEMMA LocalAppendPrefixHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars,
           LocalAppendRequestOwnersUnique(voteHistory), LocalAppendPrefixHistory(voteHistory)
    PROVE LocalAppendPrefixHistory(nextVoteHistory)'
<1>base. TypeOK /\ SendInvariant /\ CampaignHistory(voteHistory)
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv
<1> SUFFICES ASSUME NEW record \in nextVoteHistory, LocalAppendRecord(record),
                      NEW target \in Seq(LogEntry), IsPrefix(target, record.prefix)
             PROVE IsPrefix(target, log'[record.candidate])
                   \/ ConflictingHigherAppendRequest(record.candidate, record.term, target)'
    BY SMT DEF LocalAppendPrefixHistory
<1>old. CASE record \in voteHistory
    <2>types. record.candidate \in Server /\ record.term \in Nat /\ record.term <= currentTerm[record.candidate]
        BY <1>base, <1>old, SMT DEF CampaignHistory, CampaignHistoryRecord
    <2>held. CASE IsPrefix(target, log[record.candidate])
        BY <1>old, <2>types, <2>held, LocalSourceTargetNext, SMT DEF LocalAppendRequestOwnersUnique
    <2>conflict. CASE ConflictingHigherAppendRequest(record.candidate, record.term, target)
        BY <1>base, <2>types, <2>conflict, ConflictingHigherAppendRequestRetained, SMT
    <2> QED BY <1>old, <2>held, <2>conflict, SMT DEF LocalAppendPrefixHistory
<1>new. CASE record \notin voteHistory
    <2>origin. \E actor \in Server, payload \in ClientPayload:
        /\ ClientRequest(actor, payload) /\ record.candidate = actor /\ record.prefix = log'[actor]
        BY <1>base, <1>new, NewLocalAppendRecordOrigin, SMT
    <2> QED BY <2>origin, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA LocalAppendVoteCutHistoryNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars,
           NEW ancestry, LocalAppendRecordsCovered(voteHistory, ancestry),
           LocalAppendPrefixHistory(voteHistory), LocalAppendVoteCutHistory(voteHistory)
    PROVE LocalAppendVoteCutHistory(nextVoteHistory)'
<1>base. TypeOK /\ TypeOK' /\ SendInvariant' /\ CampaignHistory(voteHistory)
    BY JointCoreBase, TypeOKNext, ReplicationPrefixInvNext, SMT
    DEF MembershipJointCore, ReplicationPrefixInv, ReplicationEvidenceInv, MembershipEntryAncestryInv,
        MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv
<1> SUFFICES ASSUME NEW record \in nextVoteHistory, LocalAppendRecord(record)
             PROVE AcknowledgmentVoteCuts(nextVoteHistory, record.prefix, record.candidate, record.term)'
    BY SMT DEF LocalAppendVoteCutHistory
<1>old. CASE record \in voteHistory
    <2>types. record.candidate \in Server /\ record.term \in Nat /\ record.prefix \in Seq(LogEntry)
        BY <1>base, <1>old, SMT DEF CampaignHistory, CampaignHistoryRecord, LocalAppendRecordsCovered
    <2> QED BY <1>old, <2>types, VoteCutsWithPrefixHistoryNext, SMT
        DEF LocalAppendPrefixHistory, LocalAppendVoteCutHistory
<1>new. CASE record \notin voteHistory
    <2>origin. PICK actor \in Server, payload \in ClientPayload:
        /\ ClientRequest(actor, payload) /\ record.candidate = actor /\ record.term = currentTerm[actor]
        /\ record.snapshot = CampaignPrefix(log[actor], currentTerm[actor]) /\ record.prefix = log'[actor]
        BY <1>base, <1>new, NewLocalAppendRecordOrigin, SMT
    <2> QED BY <1>base, <2>origin, SMT
        DEF AcknowledgmentVoteCuts, RecordedCampaignVote, Grant, Started, SendInvariant,
            ClientRequest, TypeOK, ServerVarsTypeOK
<1> QED BY <1>old, <1>new, SMT

LEMMA LocalAppendCoverageWithoutClient ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry,
           LocalAppendRecordsCovered(voteHistory, ancestry),
           ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    PROVE LocalAppendRecordsCovered(nextVoteHistory, ancestry)
    BY NewLocalAppendRecordOrigin, SMT DEF LocalAppendRecordsCovered

LEMMA LocalAppendCoverageClient ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry,
           LocalAppendRecordsCovered(voteHistory, ancestry), NEW actor \in Server, NEW payload \in ClientPayload,
           ClientRequest(actor, payload), NEW fresh, fresh.prefix = log'[actor], fresh.owner = actor,
           fresh.edge.term = currentTerm[actor], fresh.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
    PROVE LocalAppendRecordsCovered(nextVoteHistory, ancestry \cup {fresh})
    BY ClientRequestLogTypeOK, SMT
    DEF LocalAppendRecordsCovered, CampaignHistoryContextStep, CampaignHistoryStep, LogVarsTypeOK

LEMMA ReadyCandidateCapturesLocalAppendCut ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), LocalAppendVoteCutHistory(voteHistory),
           OpportunityRequestIntersections(voteHistory), NEW candidate \in Server, state[candidate] = Candidate,
           NEW term \in Nat, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE LocalAppendElectionCut(voteHistory, term, snapshot, support)
<1>base. TypeOK /\ SendInvariant /\ CampaignHistory(voteHistory)
    BY JointCoreBase, SMT DEF MembershipCampaignsInv, MembershipVotesInv
<1>no_append. \A request \in AppendRequests: request.mterm # term
    BY ReadyCandidateHasNoSameTermAppendRequests, SMT
<1> SUFFICES ASSUME NEW record \in voteHistory, LocalAppendRecord(record),
                      record.candidate \in support, record.term < term,
                      NEW target \in Seq(LogEntry), IsPrefix(target, record.prefix)
             PROVE SnapshotCoversPrefix(snapshot, target)
                   \/ EarlierConflictingRequest(record.candidate, record.term, term, target)
    BY SMT DEF LocalAppendElectionCut
<1>types. record.candidate \in Server /\ record.term \in Nat
    BY <1>base, SMT DEF CampaignHistory, CampaignHistoryRecord
<1>vote. RecordedCampaignVote(voteHistory, record.candidate, candidate, term)
    BY SMT DEF ReadyElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
<1>cut. ConflictingRequestBeforeVote(record.candidate, record.term, term, target)
        \/ \E request \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(request, target)
    BY <1>types, <1>vote, SMT DEF LocalAppendVoteCutHistory, AcknowledgmentVoteCuts
<1>conflict. CASE ConflictingRequestBeforeVote(record.candidate, record.term, term, target)
    BY <1>conflict, <1>no_append, SMT DEF ConflictingRequestBeforeVote, EarlierConflictingRequest
<1>fresh. CASE \E request \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(request, target)
    BY <1>fresh, RecordedVoteRequestsUseSnapshot, SMT
    DEF ReadyElectionCertificate, RetainedElectionCertificate, SnapshotCoversPrefix, VoteRequestCoversPrefix
<1> QED BY <1>cut, <1>conflict, <1>fresh, SMT

LEMMA LocalAppendElectionCutNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), MembershipJointCore(voteHistory), [Next]_vars,
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
           LocalAppendElectionCut(voteHistory, term, snapshot, support)
    PROVE LocalAppendElectionCut(nextVoteHistory, term, snapshot, support)'
<1>base. TypeOK /\ SendInvariant
    BY JointCoreBase, SMT
<1> SUFFICES ASSUME NEW record \in nextVoteHistory, LocalAppendRecord(record),
                      record.candidate \in support, record.term < term,
                      NEW target \in Seq(LogEntry), IsPrefix(target, record.prefix)
             PROVE SnapshotCoversPrefix(snapshot, target)
                   \/ EarlierConflictingRequest(record.candidate, record.term, term, target)'
    BY SMT DEF LocalAppendElectionCut
<1>old. CASE record \in voteHistory
    BY <1>old, MessagesMonotonicNext, SMT DEF LocalAppendElectionCut, EarlierConflictingRequest, AppendRequests
<1>new. CASE record \notin voteHistory
    <2>origin. PICK actor \in Server, payload \in ClientPayload:
        /\ ClientRequest(actor, payload) /\ record.candidate = actor /\ record.term = currentTerm[actor]
        /\ record.snapshot = CampaignPrefix(log[actor], currentTerm[actor]) /\ record.prefix = log'[actor]
        BY <1>base, <1>new, NewLocalAppendRecordOrigin, SMT
    <2>vote. RecordedCampaignVote(voteHistory, actor, candidate, term)
        BY <2>origin, SMT DEF RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
    <2> QED BY <1>base, <2>origin, <2>vote, RecordedCampaignVoteTermBound, SMT
        DEF TypeOK, ServerVarsTypeOK
<1> QED BY <1>old, <1>new, SMT

LEMMA ReadyCandidateCapturesRequestSourceCut ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, RequestSourceVoteCutHistory(voteHistory, ancestry), OpportunityRequestIntersections(voteHistory),
           NEW candidate \in Server, state[candidate] = Candidate, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support, ReadyElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE RequestSourceElectionCut(ancestry, candidate, term, snapshot, support)
<1>base. TypeOK /\ SendInvariant BY JointCoreBase, SMT
<1>no_append. \A request \in AppendRequests: request.mterm # term
    BY ReadyCandidateHasNoSameTermAppendRequests, SMT
<1> SUFFICES ASSUME NEW original \in AppendRequests, original.msource \in support, original.mterm < term
             PROVE \E prefix \in Seq(LogEntry):
                       /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
                       /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                              SnapshotCoversPrefix(snapshot, target)
                              \/ EarlierConflictingRequest(original.msource, original.mterm, term, target)
    BY SMT DEF RequestSourceElectionCut
<1>fields. original.msource \in Server /\ original.mterm \in Nat
    BY <1>base, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, AppendRequests
<1>vote. RecordedCampaignVote(voteHistory, original.msource, candidate, term)
    BY SMT DEF ReadyElectionCertificate, RetainedElectionCertificate, VoteSupport, VoteFor, RecordedCampaignVote
<1>prefix. PICK prefix \in Seq(LogEntry):
        /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
        /\ AcknowledgmentVoteCuts(voteHistory, prefix, original.msource, original.mterm)
    BY SMT DEF RequestSourceVoteCutHistory
<1>targets. \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
        SnapshotCoversPrefix(snapshot, target)
        \/ EarlierConflictingRequest(original.msource, original.mterm, term, target)
    <2> SUFFICES ASSUME NEW target \in Seq(LogEntry), IsPrefix(target, prefix)
                 PROVE SnapshotCoversPrefix(snapshot, target)
                       \/ EarlierConflictingRequest(original.msource, original.mterm, term, target) BY SMT
    <2>history. ConflictingRequestBeforeVote(original.msource, original.mterm, term, target)
                \/ \E request \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(request, target)
        BY <1>fields, <1>vote, <1>prefix, SMT DEF AcknowledgmentVoteCuts
    <2>conflict. CASE ConflictingRequestBeforeVote(original.msource, original.mterm, term, target)
        BY <1>base, <1>no_append, <1>fields, <2>conflict, MessageFieldsTypeOK, SMT
        DEF ConflictingRequestBeforeVote, EarlierConflictingRequest, AppendRequests, TypeOK, MsgTypeOK
    <2>fresh. CASE \E request \in RecordedVoteRequests(voteHistory, candidate, term): VoteRequestCoversPrefix(request, target)
        <3>request. PICK request \in RecordedVoteRequests(voteHistory, candidate, term):
                VoteRequestCoversPrefix(request, target)
            BY <2>fresh, SMT
        <3>history. CampaignHistory(voteHistory) /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
            BY SMT DEF ReadyElectionCertificate, RetainedElectionCertificate
        <3>fields.
                /\ request.mlastLogTerm = LastTerm(snapshot)
                /\ request.mlastLogIndex = Len(snapshot)
            BY <3>request, <3>history, RecordedVoteRequestsUseSnapshot, Zenon
        <3> QED BY <3>request, <3>fields, SMT DEF SnapshotCoversPrefix, VoteRequestCoversPrefix
    <2> QED BY <2>history, <2>conflict, <2>fresh, SMT
<1> QED BY <1>prefix, <1>targets, SMT

LEMMA RequestSourceElectionCutNext ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), [Next]_vars, NEW ancestry, NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support),
           RequestSourceElectionCut(ancestry, candidate, term, snapshot, support)
    PROVE RequestSourceElectionCut(ancestry, candidate, term, snapshot, support)'
<1>base. TypeOK /\ EntryEdgeBase /\ SendInvariant BY JointCoreBase, SMT DEF MembershipJointCore
<1> SUFFICES ASSUME NEW original \in AppendRequests', original.msource \in support, original.mterm < term
             PROVE \E prefix \in Seq(LogEntry):
                       /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
                       /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                              SnapshotCoversPrefix(snapshot, target)
                              \/ EarlierConflictingRequest(original.msource, original.mterm, term, target)'
    BY SMT DEF RequestSourceElectionCut, RequestPrefixData, CoveredPrefix
<1>old. CASE original \in messages
    <2>prefix. PICK prefix \in Seq(LogEntry):
            /\ RequestPrefixData(original, prefix) /\ CoveredPrefix(ancestry, prefix)
            /\ \A target \in Seq(LogEntry): IsPrefix(target, prefix) =>
                   SnapshotCoversPrefix(snapshot, target)
                   \/ EarlierConflictingRequest(original.msource, original.mterm, term, target)
        BY <1>old, SMT DEF RequestSourceElectionCut, AppendRequests
    <2> QED BY <2>prefix, MessagesMonotonicNext, SMT DEF EarlierConflictingRequest, AppendRequests
<1>new. CASE original \notin messages
    <2>origin. PICK actor, peer \in Server:
            /\ AppendEntries(actor, peer) /\ original = AppendEntriesMessage(actor, peer)
        BY <1>base, <1>new, NewAppendRequestOrigin, SMT DEF AppendRequests
    <2>vote. RecordedCampaignVote(voteHistory, actor, candidate, term)
        BY <2>origin, SMT DEF RetainedElectionCertificate, VoteSupport, VoteFor,
            RecordedCampaignVote, AppendEntriesMessage
    <2> QED BY <1>base, <2>origin, <2>vote, RecordedCampaignVoteTermBound, SMT
        DEF AppendEntriesMessage, TypeOK, ServerVarsTypeOK
<1> QED BY <1>old, <1>new, SMT

LEMMA PostRequestSourceHistoriesFamilyExtension ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry, NEW larger, ancestry \subseteq larger,
           RequestSourcePrefixHistory(ancestry)', RequestSourceVoteCutHistory(nextVoteHistory, ancestry)'
    PROVE RequestSourcePrefixHistory(larger)' /\ RequestSourceVoteCutHistory(nextVoteHistory, larger)'
<1>covered. \A prefix \in Seq(LogEntry): CoveredPrefix(ancestry, prefix)' => CoveredPrefix(larger, prefix)'
    BY SMT DEF CoveredPrefix
<1> QED BY <1>covered, SMT DEF RequestSourcePrefixHistory, RequestSourceVoteCutHistory

LEMMA DataFamilyEdgeConsistency ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry)
    PROVE WitnessEdgeConsistency(ancestry)
<1> SUFFICES ASSUME NEW left \in ancestry, NEW right \in ancestry,
                      left.edge.index = right.edge.index, left.edge.term = right.edge.term
             PROVE left.edge.entry = right.edge.entry /\ left.edge.previous = right.edge.previous
    BY SMT DEF WitnessEdgeConsistency
<1>data.
        /\ left.prefix \in Seq(LogEntry) /\ right.prefix \in Seq(LogEntry)
        /\ left.edge.index \in DOMAIN left.prefix
        /\ left.edge = LogEntryEdge(left.prefix, left.edge.index)
        /\ right.edge = LogEntryEdge(right.prefix, right.edge.index)
    BY LenProperties, SMT DEF PrefixWitnessFamilyData, WitnessPrefixData
<1>prefix. IsPrefix(left.prefix, right.prefix)
    BY <1>data, SMT DEF PrefixWitnessFamilyData, WitnessPrefixData, TermPrefixOrder
<1>edges. left.edge = right.edge
    BY <1>data, <1>prefix, PrefixEntryEdgesEqual, SMT
<1> QED BY <1>edges, SMT

LEMMA DataFamilyCoveredEntryHasPrefixWitness ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), WitnessEdgeConsistency(ancestry),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), NEW index \in DOMAIN entries
    PROVE \E witness \in ancestry:
              /\ witness.prefix = SubSeq(entries, 1, index)
              /\ witness.edge.index = index /\ witness.edge.term = entries[index].term
<1>witness. PICK witness \in ancestry: witness.edge = LogEntryEdge(entries, index)
    BY SMT DEF CoveredPrefix
<1>data.
        /\ witness.prefix \in Seq(LogEntry) /\ Len(witness.prefix) = index
        /\ index \in DOMAIN witness.prefix
        /\ witness.prefix[index].term = entries[index].term
        /\ witness.edge.index = index /\ witness.edge.term = entries[index].term
    BY <1>witness, LenProperties, SMT DEF PrefixWitnessFamilyData, WitnessPrefixData, LogEntryEdge
<1>covered. CoveredPrefix(ancestry, witness.prefix)
    BY <1>witness, SMT DEF PrefixWitnessFamilyData, CoveredPrefix
<1>matching. SubSeq(witness.prefix, 1, index) = SubSeq(entries, 1, index)
    BY <1>data, <1>covered, CoveredPrefixesMatch, SMT
<1> QED BY <1>witness, <1>data, <1>matching, WholeSequencePrefix, SMT

LEMMA CommitPrefixDataTargetProperties ==
    ASSUME NEW certificate, CommitPrefixData(certificate)
    PROVE /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) = certificate.index
          /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ IsPrefix(CommitTarget(certificate), certificate.entries)
    BY SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF CommitPrefixData, CommitTarget, LastTerm, IsPrefix

LEMMA DataCoveredExtensionConfigurationFrontier ==
    ASSUME NEW ancestry, NEW commits, NEW working, BarrierFrontierData(ancestry, commits, working),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), IsPrefix(working.prefix, entries)
    PROVE LatestConfigurationOccurrence(entries) = working
          \/ \E witness \in ancestry, certificate \in commits:
                 /\ witness.prefix = LatestConfigurationOccurrence(entries).prefix
                 /\ witness.edge.index = LatestConfigurationOccurrence(entries).index
                 /\ witness.edge.entry.members # Nil /\ ConfigurationBarrierFor(witness, certificate)
                 /\ certificate.configuration = working /\ ConfigOf(witness.prefix) = ConfigOf(entries)
<1>base. PrefixWitnessFamilyData(ancestry) /\ WitnessEdgeConsistency(ancestry)
    BY DataFamilyEdgeConsistency, SMT DEF BarrierFrontierData
<1>working. ConfigurationOccurrenceData(working)
              /\ LastConfigChangeIndex(working.prefix) = working.index
    BY SMT DEF BarrierFrontierData
<1>latest.
        /\ ConfigurationOccurrenceData(LatestConfigurationOccurrence(entries))
        /\ IsPrefix(LatestConfigurationOccurrence(entries).prefix, entries)
        /\ LastConfigChangeIndex(entries) \in 0..Len(entries)
    BY LatestConfigurationOccurrenceData, ConfigurationIndexProperties, SubSeqProperties,
       ElementOfSeq, LenProperties, SMT DEF LatestConfigurationOccurrence, IsPrefix
<1>lower. working.index <= LastConfigChangeIndex(entries)
    BY <1>working, PrefixConfigurationIndexMonotonic, SMT DEF ConfigurationOccurrenceData
<1>same. CASE LastConfigChangeIndex(entries) <= working.index
    BY <1>working, <1>latest, <1>lower, <1>same,
           PrefixesWithBoundedLength, CompatibleOccurrenceAtSameIndexEqual, SMT
    DEF LatestConfigurationOccurrence, ConfigurationOccurrenceData
<1>successor. CASE working.index < LastConfigChangeIndex(entries)
    <2>index. LastConfigChangeIndex(entries) \in DOMAIN entries
              /\ entries[LastConfigChangeIndex(entries)].members # Nil
        BY <1>working, <1>latest, <1>successor, ConfigurationIndexProperties, LenProperties, SMT
        DEF ConfigurationOccurrenceData, ConfigChangeIndexes
    <2>witness. PICK witness \in ancestry:
            /\ witness.prefix = SubSeq(entries, 1, LastConfigChangeIndex(entries))
            /\ witness.edge.index = LastConfigChangeIndex(entries)
        BY <1>base, <2>index, DataFamilyCoveredEntryHasPrefixWitness, SMT
    <2>entry. witness.edge.entry.members # Nil
        BY <1>base, <2>index, <2>witness, SubSeqProperties, ElementOfSeq, LenProperties, SMT
        DEF PrefixWitnessFamilyData, WitnessPrefixData, LogEntryEdge
    <2>barrier. PICK certificate \in commits: ConfigurationBarrierFor(witness, certificate)
        BY <2>witness, <2>entry, SMT DEF BarrierFrontierData, ConfigurationBarrierAncestry
    <2>before. PICK before \in Seq(LogEntry):
            before = SubSeq(entries, 1, LastConfigChangeIndex(entries) - 1)
        BY <1>latest, <2>index, SubSeqTypeOK, LenProperties, SMT
    <2>prefix.
            /\ IsPrefix(before, entries)
            /\ Len(before) = LastConfigChangeIndex(entries) - 1
            /\ IsPrefix(working.prefix, before)
        BY <1>working, <1>latest, <1>successor, <2>index, <2>before,
           SubSeqProperties, ElementOfSeq, PrefixesWithBoundedLength, LenProperties, SMT
        DEF ConfigurationOccurrenceData, IsPrefix
    <2>predecessor.
            LatestConfigurationOccurrence(before) =
                LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
        BY <1>latest, <2>index, <2>witness, <2>before, SubSeqOfSubSeq, LenProperties, SMT
    <2>upper.
            /\ LatestConfigurationOccurrence(before).index <= working.index
            /\ IsPrefix(LatestConfigurationOccurrence(before).prefix, working.prefix)
        BY <2>witness, <2>entry, <2>predecessor, SMT DEF BarrierFrontierData
    <2>lower. working.index <= LatestConfigurationOccurrence(before).index
        BY <1>working, <2>before, <2>prefix, PrefixConfigurationIndexMonotonic, SMT
        DEF LatestConfigurationOccurrence, ConfigurationOccurrenceData
    <2>data. ConfigurationOccurrenceData(LatestConfigurationOccurrence(before))
        BY <2>before, LatestConfigurationOccurrenceData, SMT
    <2>index_equal. LatestConfigurationOccurrence(before).index = working.index
        BY <1>working, <2>data, <2>upper, <2>lower, LenProperties, SMT DEF ConfigurationOccurrenceData
    <2>parent. LatestConfigurationOccurrence(before) = working
        BY <1>working, <2>data, <2>upper, <2>index_equal,
           CompatibleOccurrenceAtSameIndexEqual, SMT
    <2>members. ConfigOf(witness.prefix) = ConfigOf(entries)
        BY <1>latest, <2>witness, ConfigurationOccurrenceOnContainingPrefix,
           SubSeqProperties, ElementOfSeq, LenProperties, SMT
        DEF LatestConfigurationOccurrence, ConfigurationOccurrenceData, IsPrefix
    <2> QED BY <2>witness, <2>entry, <2>barrier, <2>predecessor, <2>parent, <2>members, SMT
        DEF ConfigurationBarrierFor, LatestConfigurationOccurrence
<1> QED BY <1>working, <1>latest, <1>same, <1>successor, SMT
    DEF ConfigurationOccurrenceData

LEMMA DataCoveredExtensionHasWorkingOrAdjacentConfiguration ==
    ASSUME NEW ancestry, NEW commits, NEW working, BarrierFrontierData(ancestry, commits, working),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), IsPrefix(working.prefix, entries)
    PROVE LatestConfigurationOccurrence(entries) = working
          \/ SingleChange(working.members, ConfigOf(entries))
    BY DataCoveredExtensionConfigurationFrontier, SMT DEF ConfigurationBarrierFor

LEMMA DataProtectedPrefixesHaveOnlyOneSuccessor ==
    ASSUME NEW ancestry, NEW commits, NEW working, BarrierFrontierData(ancestry, commits, working),
           NEW leftEntries \in Seq(LogEntry), NEW rightEntries \in Seq(LogEntry),
           TermsOrdered(leftEntries), TermsOrdered(rightEntries),
           CoveredPrefix(ancestry, leftEntries), CoveredPrefix(ancestry, rightEntries),
           IsPrefix(working.prefix, leftEntries), IsPrefix(working.prefix, rightEntries),
           \A certificate \in commits: IsPrefix(CommitTarget(certificate), leftEntries),
           \A certificate \in commits: IsPrefix(CommitTarget(certificate), rightEntries),
           NEW leftOccurrence, NEW rightOccurrence,
           leftOccurrence = LatestConfigurationOccurrence(leftEntries),
           rightOccurrence = LatestConfigurationOccurrence(rightEntries),
           leftOccurrence # working, rightOccurrence # working
    PROVE leftOccurrence = rightOccurrence
<1>base. BarrierFrontierData(ancestry, commits, working)
    BY SMT
<1>snapshots.
        /\ leftOccurrence = LatestConfigurationOccurrence(leftEntries)
        /\ rightOccurrence = LatestConfigurationOccurrence(rightEntries)
    BY SMT
<1>covered. CoveredPrefix(ancestry, leftEntries) /\ CoveredPrefix(ancestry, rightEntries)
    BY SMT
<1>prefixes.
        /\ IsPrefix(working.prefix, leftEntries)
        /\ IsPrefix(working.prefix, rightEntries)
    BY SMT
<1>first. PICK first \in ancestry, firstBarrier \in commits:
        /\ first.prefix = leftOccurrence.prefix /\ first.edge.index = leftOccurrence.index
        /\ first.edge.entry.members # Nil /\ ConfigurationBarrierFor(first, firstBarrier)
        /\ firstBarrier.configuration = working
    BY <1>base, <1>snapshots, <1>covered, <1>prefixes, DataCoveredExtensionConfigurationFrontier, SMT
<1>second. PICK second \in ancestry, secondBarrier \in commits:
        /\ second.prefix = rightOccurrence.prefix /\ second.edge.index = rightOccurrence.index
        /\ second.edge.entry.members # Nil /\ ConfigurationBarrierFor(second, secondBarrier)
        /\ secondBarrier.configuration = working
    BY <1>base, <1>snapshots, <1>covered, <1>prefixes, DataCoveredExtensionConfigurationFrontier, SMT
<1>data.
        /\ CommitPrefixData(firstBarrier) /\ CommitPrefixData(secondBarrier)
        /\ WitnessPrefixData(first) /\ WitnessPrefixData(second)
        /\ ConfigurationOccurrenceData(leftOccurrence) /\ ConfigurationOccurrenceData(rightOccurrence)
        /\ ConfigurationOccurrenceData(working)
    BY <1>base, <1>snapshots, <1>first, <1>second, LatestConfigurationOccurrenceData, SMT
    DEF BarrierFrontierData, PrefixWitnessFamilyData
<1>targets.
        /\ CommitTarget(firstBarrier) \in Seq(LogEntry) /\ Len(CommitTarget(firstBarrier)) > 0
        /\ LastTerm(CommitTarget(firstBarrier)) = firstBarrier.term
        /\ LatestConfigurationOccurrence(CommitTarget(firstBarrier)) = working
        /\ CommitTarget(secondBarrier) \in Seq(LogEntry) /\ Len(CommitTarget(secondBarrier)) > 0
        /\ LastTerm(CommitTarget(secondBarrier)) = secondBarrier.term
        /\ LatestConfigurationOccurrence(CommitTarget(secondBarrier)) = working
    BY <1>base, <1>first, <1>second, <1>data, CommitPrefixDataTargetProperties,
       CommitPrefixDataTargetProperties, ConfigurationOccurrenceOnContainingPrefix, SMT
    DEF ConfigurationBarrierFor, CommitPrefixData, LatestConfigurationOccurrence
<1>contains.
        /\ IsPrefix(CommitTarget(firstBarrier), rightEntries)
        /\ IsPrefix(CommitTarget(secondBarrier), leftEntries)
    BY <1>first, <1>second, SMT
<1>frontiers.
        /\ working.index < leftOccurrence.index
        /\ working.index < rightOccurrence.index
        /\ LastTerm(leftOccurrence.prefix) = firstBarrier.term
        /\ LastTerm(rightOccurrence.prefix) = secondBarrier.term
    BY <1>first, <1>second, <1>data, LenProperties, SMT
    DEF ConfigurationBarrierFor, WitnessPrefixData, LogEntryEdge, LastTerm, CommitPrefixData,
        ConfigurationOccurrenceData
<1>earlier. CASE firstBarrier.term < secondBarrier.term
    BY <1>base, <1>snapshots, <1>data, <1>targets, <1>contains, <1>frontiers, <1>earlier,
       OlderConfigurationCannotContainNewerParentTarget, SMT
<1>later. CASE secondBarrier.term < firstBarrier.term
    BY <1>base, <1>snapshots, <1>data, <1>targets, <1>contains, <1>frontiers, <1>later,
       OlderConfigurationCannotContainNewerParentTarget, SMT
<1>same. CASE firstBarrier.term = secondBarrier.term
    <2>fields.
            /\ first.prefix \in Seq(LogEntry) /\ second.prefix \in Seq(LogEntry)
            /\ first.edge.index = Len(first.prefix) /\ second.edge.index = Len(second.prefix)
            /\ first.edge = LogEntryEdge(first.prefix, Len(first.prefix))
            /\ second.edge = LogEntryEdge(second.prefix, Len(second.prefix))
            /\ Len(first.prefix) > 0 /\ Len(second.prefix) > 0
        BY <1>data, SMT DEF WitnessPrefixData
    <2>changes.
            /\ Len(first.prefix) \in ConfigChangeIndexes(first.prefix)
            /\ Len(second.prefix) \in ConfigChangeIndexes(second.prefix)
        BY <1>first, <1>second, <2>fields, LenProperties, SMT DEF LogEntryEdge, ConfigChangeIndexes
    <2>last.
            /\ LastConfigChangeIndex(first.prefix) = Len(first.prefix)
            /\ LastConfigChangeIndex(second.prefix) = Len(second.prefix)
        BY <2>fields, <2>changes, ConfigurationIndexProperties, LenProperties, SMT
    <2>predecessors.
            LatestConfigurationOccurrence(SubSeq(first.prefix, 1, Len(first.prefix) - 1)) =
                LatestConfigurationOccurrence(SubSeq(second.prefix, 1, Len(second.prefix) - 1))
        BY <1>first, <1>second, <2>fields, SMT DEF ConfigurationBarrierFor
    <2>order. IsPrefix(first.prefix, second.prefix) \/ IsPrefix(second.prefix, first.prefix)
        BY <1>base, <1>first, <1>second, <1>data, <1>same, SMT
        DEF BarrierFrontierData, TermPrefixOrder, ConfigurationBarrierFor, WitnessPrefixData
    <2>equal. first.prefix = second.prefix
        BY <2>fields, <2>last, <2>predecessors, <2>order,
           ConfigurationPrefixesWithSameParentAreUnique, SMT
    <2> QED BY <1>first, <1>second, <1>data, <2>equal, SMT DEF ConfigurationOccurrenceData
<1> QED BY <1>data, <1>earlier, <1>later, <1>same, SMT DEF CommitPrefixData

ProtectedPrefixData(ancestry, commits, working, entries) ==
    /\ entries \in Seq(LogEntry) /\ TermsOrdered(entries) /\ CoveredPrefix(ancestry, entries)
    /\ IsPrefix(working.prefix, entries)
    /\ \A certificate \in commits: IsPrefix(CommitTarget(certificate), entries)

LEMMA DataProtectedConfigurationsAreEqualOrAdjacent ==
    ASSUME NEW ancestry, NEW commits, NEW working, BarrierFrontierData(ancestry, commits, working),
           NEW leftEntries, NEW rightEntries,
           ProtectedPrefixData(ancestry, commits, working, leftEntries),
           ProtectedPrefixData(ancestry, commits, working, rightEntries)
    PROVE EqualOrAdjacentConfigurations(ConfigOf(leftEntries), ConfigOf(rightEntries))
<1>left. LatestConfigurationOccurrence(leftEntries) = working
         \/ SingleChange(working.members, ConfigOf(leftEntries))
    BY DataCoveredExtensionHasWorkingOrAdjacentConfiguration, SMT DEF ProtectedPrefixData
<1>right. LatestConfigurationOccurrence(rightEntries) = working
          \/ SingleChange(working.members, ConfigOf(rightEntries))
    BY DataCoveredExtensionHasWorkingOrAdjacentConfiguration, SMT DEF ProtectedPrefixData
<1>left_working. CASE LatestConfigurationOccurrence(leftEntries) = working
    BY <1>right, <1>left_working, SMT DEF EqualOrAdjacentConfigurations, LatestConfigurationOccurrence
<1>right_working. CASE LatestConfigurationOccurrence(rightEntries) = working
    BY <1>left, <1>right_working, SMT DEF EqualOrAdjacentConfigurations, LatestConfigurationOccurrence, SingleChange
<1>successors. CASE /\ LatestConfigurationOccurrence(leftEntries) # working
                    /\ LatestConfigurationOccurrence(rightEntries) # working
    <2>equal. LatestConfigurationOccurrence(leftEntries) = LatestConfigurationOccurrence(rightEntries)
        BY <1>successors, DataProtectedPrefixesHaveOnlyOneSuccessor, SMT DEF ProtectedPrefixData
    <2> QED BY <2>equal, SMT DEF EqualOrAdjacentConfigurations, LatestConfigurationOccurrence
<1> QED BY <1>left_working, <1>right_working, <1>successors, SMT

\* The term induction includes election snapshots and request senders, so an
\* intervening conflicting request is a strictly earlier induction query.
LEMMA TermBarrierHistoryProperties ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat
    PROVE /\ ConfigurationHistoryData(TermBarrierHistory(ancestry, term))
          /\ ConfigurationHistoryCompatible(TermBarrierHistory(ancestry, term))
          /\ TermBarrierHistory(ancestry, term) \subseteq EvidenceConfigurationHistory(voteHistory)
<1>base. TypeOK /\ ConfigurationHistoryData(EvidenceConfigurationHistory(voteHistory))
          /\ ConfigurationHistoryCompatible(EvidenceConfigurationHistory(voteHistory))
    BY JointCoreBase, EvidenceConfigurationHistoryWellFormed, JointCoreImpliesCompatibleHistory, SMT
<1>subset. TermBarrierHistory(ancestry, term) \subseteq EvidenceConfigurationHistory(voteHistory)
    BY ConfigurationBarrierPredecessorIsAgreed, SMT
    DEF TermBarrierHistory, TermAncestry, EvidenceConfigurationHistory, ConfigurationHistory
<1>finite. IsFiniteSet(TermBarrierHistory(ancestry, term))
    BY <1>base, <1>subset, FS_Subset, SMT DEF ConfigurationHistoryData
<1> QED BY <1>base, <1>subset, <1>finite, SMT
    DEF ConfigurationHistoryData, ConfigurationHistoryCompatible, TermBarrierHistory

LEMMA TermWorkingConfigurationProperties ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat
    PROVE /\ TermWorkingConfiguration(ancestry, term) \in TermBarrierHistory(ancestry, term)
          /\ ConfigurationOccurrenceData(TermWorkingConfiguration(ancestry, term))
          /\ LastConfigChangeIndex(TermWorkingConfiguration(ancestry, term).prefix) =
                 TermWorkingConfiguration(ancestry, term).index
          /\ \A occurrence \in TermBarrierHistory(ancestry, term):
                 /\ occurrence.index <= TermWorkingConfiguration(ancestry, term).index
                 /\ IsPrefix(occurrence.prefix, TermWorkingConfiguration(ancestry, term).prefix)
<1>base. TypeOK /\ ConfigurationHistoryData(TermBarrierHistory(ancestry, term))
          /\ ConfigurationHistoryCompatible(TermBarrierHistory(ancestry, term))
          /\ TermBarrierHistory(ancestry, term) \subseteq EvidenceConfigurationHistory(voteHistory)
    BY JointCoreBase, TermBarrierHistoryProperties, SMT
<1>latest. TermWorkingConfiguration(ancestry, term) \in TermBarrierHistory(ancestry, term)
    BY <1>base, LatestEvidenceOccurrenceProperties, SMT DEF TermWorkingConfiguration
<1> QED BY <1>base, <1>latest, LatestEvidenceOccurrenceProperties,
    LatestCompatibleOccurrenceProperties, EvidenceOccurrencePrefixIndex, SMT DEF TermWorkingConfiguration

LEMMA TermAncestryIsPrefixClosed ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), NEW term \in Nat
    PROVE PrefixWitnessFamilyData(TermAncestry(ancestry, term))
<1> SUFFICES ASSUME NEW witness \in TermAncestry(ancestry, term), NEW index \in DOMAIN witness.prefix
             PROVE \E ancestor \in TermAncestry(ancestry, term): ancestor.edge = LogEntryEdge(witness.prefix, index)
    BY SMT DEF PrefixWitnessFamilyData, TermAncestry
<1>ancestor. PICK ancestor \in ancestry: ancestor.edge = LogEntryEdge(witness.prefix, index)
    BY SMT DEF PrefixWitnessFamilyData, TermAncestry
<1>bound. ancestor.edge.term <= witness.edge.term
    BY <1>ancestor, LenProperties, SMT
    DEF PrefixWitnessFamilyData, WitnessPrefixData, TermsOrdered, LogEntryEdge, LastTerm, TermAncestry
<1> QED BY <1>ancestor, <1>bound, SMT DEF TermAncestry, PrefixWitnessFamilyData, WitnessPrefixData

LEMMA JointWitnessesSupplyTermFrontier ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat
    PROVE BarrierFrontierData(TermAncestry(ancestry, term), TermCommits(commits, term),
                             TermWorkingConfiguration(ancestry, term))
<1>family. PrefixWitnessFamilyData(ancestry)
    BY SMT DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData
<1>restricted. PrefixWitnessFamilyData(TermAncestry(ancestry, term))
    BY <1>family, TermAncestryIsPrefixClosed, SMT
<1>barriers. ConfigurationBarrierAncestry(TermAncestry(ancestry, term), TermCommits(commits, term))
    BY SMT DEF JointMembershipWitnesses, ConfigurationBarrierAncestry, ConfigurationBarrierFor,
        TermAncestry, TermCommits
<1>working.
        /\ ConfigurationOccurrenceData(TermWorkingConfiguration(ancestry, term))
        /\ LastConfigChangeIndex(TermWorkingConfiguration(ancestry, term).prefix) =
               TermWorkingConfiguration(ancestry, term).index
        /\ \A occurrence \in TermBarrierHistory(ancestry, term):
               /\ occurrence.index <= TermWorkingConfiguration(ancestry, term).index
               /\ IsPrefix(occurrence.prefix, TermWorkingConfiguration(ancestry, term).prefix)
    BY TermWorkingConfigurationProperties, SMT
<1>commit_data. \A certificate \in TermCommits(commits, term): CommitPrefixData(certificate)
    BY SMT DEF TermCommits, JointMembershipWitnesses, CommitCertificateFamily,
        RetainedCommitCertificate, CommitPrefixData
<1>predecessors. \A witness \in TermAncestry(ancestry, term):
        witness.edge.entry.members # Nil =>
            LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
                \in TermBarrierHistory(ancestry, term)
    BY SMT DEF TermBarrierHistory
<1>order. TermPrefixOrder(TermAncestry(ancestry, term))
    BY SMT DEF JointMembershipWitnesses, TermPrefixOrder, TermAncestry
<1> QED BY <1>restricted, <1>barriers, <1>working, <1>commit_data, <1>predecessors, <1>order, SMT
    DEF BarrierFrontierData

LEMMA TermCoveredPrefixRestrictsAncestry ==
    ASSUME NEW ancestry, NEW term \in Nat, NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries),
           \A index \in DOMAIN entries: entries[index].term <= term
    PROVE CoveredPrefix(TermAncestry(ancestry, term), entries)
    BY SMT DEF CoveredPrefix, LogEntryEdge, TermAncestry

LEMMA TermProtectedPrefixContainsWorking ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat, NEW entries, TermProtectedPrefix(ancestry, commits, term, entries)
    PROVE IsPrefix(TermWorkingConfiguration(ancestry, term).prefix, entries)
<1>working. TermWorkingConfiguration(ancestry, term) \in TermBarrierHistory(ancestry, term)
    BY TermWorkingConfigurationProperties, SMT
<1>initial. CASE TermWorkingConfiguration(ancestry, term) = InitialConfigurationOccurrence
    BY <1>initial, EmptySeq, SubSeqEmpty, LenProperties, SMT
    DEF InitialConfigurationOccurrence, IsPrefix, TermProtectedPrefix
<1>parent. CASE TermWorkingConfiguration(ancestry, term) # InitialConfigurationOccurrence
    <2>witness. PICK witness \in TermAncestry(ancestry, term):
            /\ witness.edge.entry.members # Nil
            /\ TermWorkingConfiguration(ancestry, term) =
                   LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
        BY <1>working, <1>parent, SMT DEF TermBarrierHistory
    <2>barrier. PICK certificate \in TermCommits(commits, term): ConfigurationBarrierFor(witness, certificate)
        BY <2>witness, SMT DEF JointMembershipWitnesses, ConfigurationBarrierAncestry,
            ConfigurationBarrierFor, TermAncestry, TermCommits
    <2>certificate. RetainedCommitCertificate(voteHistory, certificate)
        BY <2>barrier, SMT DEF TermCommits, JointMembershipWitnesses, CommitCertificateFamily
    <2>target.
            /\ CommitTarget(certificate) \in Seq(LogEntry)
            /\ IsPrefix(CommitTarget(certificate), certificate.entries)
            /\ Len(CommitTarget(certificate)) = certificate.index
        BY <2>certificate, CommitCertificateTargetProperties, SMT
    <2>configuration. certificate.configuration = TermWorkingConfiguration(ancestry, term)
        BY <2>witness, <2>barrier, SMT DEF ConfigurationBarrierFor
    <2>certificate_data.
            /\ certificate.entries \in Seq(LogEntry)
            /\ certificate.configuration = LatestConfigurationOccurrence(certificate.entries)
            /\ certificate.configuration.index <= certificate.index
        BY <2>certificate, <2>barrier, SMT DEF RetainedCommitCertificate, ConfigurationBarrierFor
    <2>configuration_prefix.
            /\ IsPrefix(certificate.configuration.prefix, certificate.entries)
            /\ Len(certificate.configuration.prefix) = certificate.configuration.index
        BY <2>certificate_data, ConfigurationIndexProperties, SubSeqProperties,
           LenProperties, ElementOfSeq, SMT DEF LatestConfigurationOccurrence, IsPrefix
    <2>prefixes.
            /\ IsPrefix(TermWorkingConfiguration(ancestry, term).prefix, certificate.entries)
            /\ Len(TermWorkingConfiguration(ancestry, term).prefix) <= certificate.index
            /\ CommitTarget(certificate) \in Seq(LogEntry)
            /\ IsPrefix(CommitTarget(certificate), certificate.entries)
            /\ Len(CommitTarget(certificate)) = certificate.index
        BY <2>configuration, <2>certificate_data, <2>configuration_prefix, <2>target, SMT
    <2>inside. IsPrefix(TermWorkingConfiguration(ancestry, term).prefix, CommitTarget(certificate))
        BY <2>certificate, <2>prefixes, TermWorkingConfigurationProperties, PrefixesWithBoundedLength, SMT
        DEF ConfigurationOccurrenceData, RetainedCommitCertificate
    <2> QED BY <2>prefixes, <2>inside, <2>barrier, TermWorkingConfigurationProperties, SequencePrefixTransitive, SMT
        DEF TermProtectedPrefix, ConfigurationOccurrenceData
<1> QED BY <1>initial, <1>parent, SMT

LEMMA TermProtectedPrefixSuppliesFrontierData ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat, NEW entries, TermProtectedPrefix(ancestry, commits, term, entries)
    PROVE ProtectedPrefixData(TermAncestry(ancestry, term), TermCommits(commits, term),
                              TermWorkingConfiguration(ancestry, term), entries)
    BY TermProtectedPrefixContainsWorking, TermCoveredPrefixRestrictsAncestry, SMT
    DEF TermProtectedPrefix, ProtectedPrefixData

LEMMA TermProtectedConfigurationsAreEqualOrAdjacent ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat, NEW leftEntries, NEW rightEntries,
           TermProtectedPrefix(ancestry, commits, term, leftEntries),
           TermProtectedPrefix(ancestry, commits, term, rightEntries)
    PROVE EqualOrAdjacentConfigurations(ConfigOf(leftEntries), ConfigOf(rightEntries))
    BY JointWitnessesSupplyTermFrontier, TermProtectedPrefixSuppliesFrontierData,
       DataProtectedConfigurationsAreEqualOrAdjacent, SMT

LEMMA OrderedEntriesBoundedByLastTerm ==
    ASSUME NEW entries \in Seq(LogEntry), TermsOrdered(entries), NEW term \in Nat, LastTerm(entries) <= term
    PROVE \A index \in DOMAIN entries: entries[index].term <= term
<1> SUFFICES ASSUME NEW index \in DOMAIN entries PROVE entries[index].term <= term BY SMT
<1>bounds. Len(entries) > 0 /\ index <= Len(entries) /\ Len(entries) \in DOMAIN entries
    BY LenProperties, SMT
<1>types. entries[index].term \in Nat /\ entries[Len(entries)].term \in Nat
    BY <1>bounds, ElementOfSeq, SMT DEF LogEntry
<1>order. entries[index].term <= entries[Len(entries)].term
    BY <1>bounds, SMT DEF TermsOrdered
<1> QED BY <1>bounds, <1>types, <1>order, SMT DEF LastTerm

LEMMA CurrentLeaderSuppliesTermProtectedPrefix ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           NEW leader \in Server, state[leader] = Leader, NEW term \in Nat, currentTerm[leader] = term
    PROVE TermProtectedPrefix(ancestry, commits, term, log[leader])
<1>base. TypeOK /\ log[leader] \in Seq(LogEntry) /\ TermsOrdered(log[leader]) /\ LogTermBoundInv
    BY JointCoreBase, LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv, TermOrderingInv,
        LogTermsMonotonic, TermsOrdered, TypeOK, LogVarsTypeOK
<1>covered. CoveredPrefix(ancestry, log[leader])
    BY <1>base, CurrentLogPrefixCovered, WholeSequencePrefix, LenProperties, SMT
    DEF JointMembershipWitnesses, IsPrefix
<1>commits. \A certificate \in TermCommits(commits, term): IsPrefix(CommitTarget(certificate), log[leader])
    BY SMT DEF TermCommits, JointMembershipWitnesses, JointCommitProtection,
        ProtectedLeaders, CommitCertificateFamily, RetainedCommitCertificate
<1> QED BY <1>base, <1>covered, <1>commits, SMT DEF TermProtectedPrefix, LogTermBoundInv

LEMMA HigherOpportunitySnapshotContainsEarlierCommits ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat, NEW candidate \in Server, NEW later \in Nat, term < later,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, later, snapshot, occurrence, support)
    PROVE \A certificate \in TermCommits(commits, term): IsPrefix(CommitTarget(certificate), snapshot)
<1> SUFFICES ASSUME NEW certificate \in TermCommits(commits, term)
             PROVE IsPrefix(CommitTarget(certificate), snapshot) BY SMT
<1>certificate. RetainedCommitCertificate(voteHistory, certificate) /\ certificate.term <= term
    BY SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses, JointMembershipWitnesses,
        CommitCertificateFamily, TermCommits
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
    BY <1>certificate, CommitCertificateTargetProperties, LenProperties, SMT DEF RetainedCommitCertificate, LastTerm
<1>prefix. IsPrefix(CommitTarget(certificate), log[candidate])
    BY <1>certificate, SMT DEF JointOpportunityWitnesses, OpportunityRelations,
        OpportunityCommitPrefixes, RetainedCommitCertificate, TermCommits
<1>older. LastTerm(CommitTarget(certificate)) < later
    BY <1>certificate, <1>target, SMT DEF RetainedCommitCertificate
<1> QED BY <1>target, <1>prefix, <1>older, CampaignContainsOlderProtectedPrefix, SMT DEF OpportunityCertificate

LEMMA HigherOpportunitySnapshotSuppliesTermProtectedPrefix ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointOpportunityWitnesses(voteHistory, ancestry, commits),
           NEW term \in Nat, NEW candidate \in Server, NEW later \in Nat, term < later,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(voteHistory, candidate, later, snapshot, occurrence, support), LastTerm(snapshot) <= term
    PROVE TermProtectedPrefix(ancestry, commits, term, snapshot)
<1>base. TypeOK /\ JointMembershipWitnesses(voteHistory, ancestry, commits) /\ TermsOrdered(log[candidate])
    BY JointCoreBase, SMT DEF JointOpportunityWitnesses, JointCandidateWitnesses,
        MembershipCampaignsInv, TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>snapshot. IsPrefix(snapshot, log[candidate]) /\ CoveredPrefix(ancestry, snapshot) /\ TermsOrdered(snapshot)
    BY <1>base, CampaignOpportunitySnapshotCovered, TermsOrderedOnPrefix, LenProperties, SMT
    DEF OpportunityCertificate, IsPrefix, TypeOK, LogVarsTypeOK
<1>commits. \A certificate \in TermCommits(commits, term): IsPrefix(CommitTarget(certificate), snapshot)
    BY HigherOpportunitySnapshotContainsEarlierCommits, SMT
<1> QED BY <1>snapshot, <1>commits, OrderedEntriesBoundedByLastTerm, SMT
    DEF TermProtectedPrefix

LEMMA CausalCampaignsProtectRecordedTarget ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenRequestPrefixesAgree(ancestry), NEW campaigns, CausalCampaignWitnesses(voteHistory, ancestry, commits, campaigns),
           NEW leader \in Server, NEW term \in Nat, NEW target \in Seq(LogEntry),
           Len(target) > 0, LastTerm(target) = term, CoveredPrefix(ancestry, target),
           TargetCampaignEvidence(voteHistory, leader, term, target), NEW configurationEntries,
           TermProtectedPrefix(ancestry, commits, term, configurationEntries),
           NEW support \in Quorums(ConfigOf(configurationEntries)),
           RecordedTargetCampaignIntersections(leader, term, target, support, campaigns)
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
            BY <2>data, <2>bounded, OrderedEntriesBoundedByLastTerm, SMT
            DEF CausalCampaignWitnesses, CausalCampaignData, CampaignCommitPrefixes, TermCommits,
                TermProtectedPrefix, JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate
        <3>shape. EqualOrAdjacentConfigurations(ConfigOf(configurationEntries), ConfigOf(campaign.snapshot))
            BY <3>profile, TermProtectedConfigurationsAreEqualOrAdjacent, SMT
        <3>votes. campaign.support \in Quorums(ConfigOf(campaign.snapshot))
                  /\ ConfigOf(campaign.snapshot) \subseteq Server
            BY <2>data, ConfigurationType, SMT DEF CausalCampaignData, CausalElectionCertificate,
                RetainedElectionCertificate, LatestConfigurationOccurrence
        <3>shared. PICK peer \in support \cap campaign.support: TRUE
            BY <1>base, <3>shape, <3>votes, EqualOrAdjacentQuorumsIntersect, SMT
        <3>response. PICK response \in messages:
                /\ SuccessfulAppendResponse(response) /\ response.msource = peer /\ response.mdest = leader
                /\ response.mterm = term /\ response.mmatchIndex >= Len(target)
            BY <3>shared, SMT DEF RecordedTargetCampaignIntersections
        <3>frozen. PICK request, prefix:
                /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
                /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
                /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
                /\ \A part \in Seq(LogEntry): IsPrefix(part, prefix) =>
                       SnapshotCoversPrefix(campaign.snapshot, part)
                       \/ EarlierConflictingRequest(peer, term, campaign.term, part)
            BY <2>data, <3>shared, <3>response, SMT
            DEF CausalCampaignData, CausalElectionCertificate, FrozenElectionAcknowledgmentCut
        <3>boundary. RequestCampaignBoundary(voteHistory, request, prefix)
            <4>original. PICK original \in Seq(LogEntry):
                    /\ RequestPrefixData(request, original) /\ CoveredPrefix(ancestry, original)
                    /\ RequestCampaignBoundary(voteHistory, request, original)
                BY <3>frozen, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
            <4>equal. prefix = original
                BY <1>base, <3>frozen, <4>original, MessageFieldsTypeOK, CoveredRequestPrefixIsUnique, SMT
                DEF TypeOK, MsgTypeOK, AppendRequests
            <4> QED BY <4>original, <4>equal, SMT
        <3>inside. IsPrefix(target, prefix)
            BY <1>base, <3>response, <3>frozen, <3>boundary, FrozenRequestPrefixContainsTarget, SMT
            DEF ResponseMatchesRequest
        <3>cut. SnapshotCoversPrefix(campaign.snapshot, target)
                \/ EarlierConflictingRequest(peer, term, campaign.term, target)
            BY <3>frozen, <3>inside, SMT
        <3>fresh. CASE SnapshotCoversPrefix(campaign.snapshot, target)
            <4>contains. IsPrefix(target, campaign.snapshot)
                BY <1>base, <2>data, <2>bounded, <3>fresh, LastTermTypeOK, LenProperties,
                   CoveredSequencesWithSameLastTermAreOrdered, SMT
                DEF SnapshotCoversPrefix, CausalCampaignData, LastTerm
            <4> QED BY <4>contains, SMT
        <3>conflict. CASE EarlierConflictingRequest(peer, term, campaign.term, target)
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
                    BY <1>base, <4>request, MessageFieldsTypeOK, SMT
                    DEF TypeOK, MsgTypeOK, AppendRequests
                <5>snapshot. earlier.snapshot \in Seq(LogEntry)
                    BY <4>earlier, SMT DEF CausalCampaignWitnesses, CausalCampaignData
                <5> QED BY <5>fields, <5>snapshot, <4>earlier, <4>contains,
                    ComparableRequestPrefixRespectsTarget, Zenon
            <4> QED BY <4>request, <4>respects, SMT
        <3> QED BY <3>cut, <3>fresh, <3>conflict, SMT
    <2> QED BY <2>data, <2>higher, <2>bounded, LastTermTypeOK, SMT DEF CausalCampaignData
<1>all. \A bound \in Nat: P(bound) BY <1>initial, <1>step, NatInduction, Isa
<1> QED BY <1>all, SMT DEF P, CausalCampaignWitnesses, CausalCampaignData

LEMMA DataCoveredWordHasLastWitness ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), Len(entries) > 0
    PROVE \E witness \in ancestry: witness.prefix = entries /\ witness.edge.term = LastTerm(entries)
<1>index. Len(entries) \in DOMAIN entries BY LenProperties, SMT
<1>witness. PICK witness \in ancestry:
        /\ witness.prefix = SubSeq(entries, 1, Len(entries))
        /\ witness.edge.term = entries[Len(entries)].term
    BY <1>index, DataFamilyEdgeConsistency, DataFamilyCoveredEntryHasPrefixWitness, SMT
<1> QED BY <1>witness, WholeSequencePrefix, SMT DEF LastTerm

LEMMA DataCoveredWordsWithSameLastTermAreOrdered ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right),
           Len(left) > 0, Len(right) > 0, LastTerm(left) = LastTerm(right), Len(left) <= Len(right)
    PROVE IsPrefix(left, right)
<1>witnesses. PICK first, second:
        /\ first \in ancestry /\ second \in ancestry /\ first.prefix = left /\ second.prefix = right
        /\ first.edge.term = LastTerm(left) /\ second.edge.term = LastTerm(right)
    BY DataCoveredWordHasLastWitness, SMT
<1> QED BY <1>witnesses, SMT DEF TermPrefixOrder, PrefixWitnessFamilyData, WitnessPrefixData

LEMMA DataFreshWordContainsProtectedTarget ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW target \in Seq(LogEntry), Len(target) > 0, CoveredPrefix(ancestry, target),
           NEW term \in Nat, LastTerm(target) = term, LaterTermPrefixProtection(ancestry, target, term),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), SnapshotCoversPrefix(entries, target)
    PROVE IsPrefix(target, entries)
<1>higher. CASE LastTerm(entries) > term
    <2>nonempty. Len(entries) > 0 BY <1>higher, LastTermTypeOK, LenProperties, SMT DEF LastTerm
    <2>witness. PICK witness \in ancestry: witness.prefix = entries /\ witness.edge.term = LastTerm(entries)
        BY <2>nonempty, DataCoveredWordHasLastWitness, SMT
    <2> QED BY <1>higher, <2>witness, SMT DEF LaterTermPrefixProtection
<1>same. CASE LastTerm(entries) = term /\ Len(target) <= Len(entries)
    BY <1>same, DataCoveredWordsWithSameLastTermAreOrdered, LenProperties, SMT
<1> QED BY <1>higher, <1>same, SMT DEF SnapshotCoversPrefix

LEMMA CommitLogDataProperties ==
    ASSUME NEW certificate, CommitLogData(certificate)
    PROVE /\ certificate.entries \in Seq(LogEntry) /\ Len(certificate.entries) > 0
          /\ LastTerm(certificate.entries) = certificate.term
          /\ CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ IsPrefix(CommitTarget(certificate), certificate.entries)
          /\ certificate.term \in Nat
<1>base. CommitPrefixData(certificate) BY SMT DEF CommitLogData
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ IsPrefix(CommitTarget(certificate), certificate.entries)
    BY <1>base, CommitPrefixDataTargetProperties, SMT
<1>bounds. Len(certificate.entries) > 0 /\ Len(certificate.entries) \in DOMAIN certificate.entries
            /\ certificate.index <= Len(certificate.entries)
    BY <1>base, LenProperties, SMT DEF CommitPrefixData
<1>types. certificate.entries[Len(certificate.entries)].term \in Nat /\ certificate.term \in Nat
    BY <1>base, <1>bounds, ElementOfSeq, SMT DEF CommitPrefixData, LogEntry
<1>ordered. certificate.term <= certificate.entries[Len(certificate.entries)].term
    BY <1>base, <1>bounds, LenProperties, SMT DEF CommitPrefixData, TermsOrdered
<1>upper. certificate.entries[Len(certificate.entries)].term <= certificate.term
    BY <1>bounds, SMT DEF CommitLogData, EntryStructure
<1>last. LastTerm(certificate.entries) = certificate.term
    BY <1>bounds, <1>types, <1>ordered, <1>upper, SMT DEF LastTerm
<1> QED BY <1>base, <1>target, <1>bounds, <1>last, SMT DEF CommitPrefixData

LEMMA BarrierTargetInsideCreatorPrefix ==
    ASSUME NEW witness, WitnessPrefixData(witness), NEW certificate, CommitPrefixData(certificate),
           ConfigurationBarrierFor(witness, certificate)
    PROVE IsPrefix(CommitTarget(certificate), witness.prefix) /\ Len(certificate.entries) < Len(witness.prefix)
<1>predecessor. SubSeq(witness.prefix, 1, witness.edge.index - 1) \in Seq(LogEntry)
                /\ IsPrefix(SubSeq(witness.prefix, 1, witness.edge.index - 1), witness.prefix)
                /\ Len(SubSeq(witness.prefix, 1, witness.edge.index - 1)) = Len(witness.prefix) - 1
    BY SubSeqProperties, SubSeqTypeOK, ElementOfSeq, LenProperties, SMT DEF WitnessPrefixData, IsPrefix
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ IsPrefix(CommitTarget(certificate), certificate.entries)
    BY CommitPrefixDataTargetProperties, SMT
<1>inside. IsPrefix(certificate.entries, witness.prefix) /\ Len(certificate.entries) < Len(witness.prefix)
    BY <1>predecessor, SequencePrefixTransitive, LenProperties, SMT
    DEF WitnessPrefixData, CommitPrefixData, ConfigurationBarrierFor, IsPrefix
<1> QED BY <1>target, <1>inside, SequencePrefixTransitive, SMT DEF WitnessPrefixData, CommitPrefixData

LEMMA MissingCommitTargetIsNumericallyStale ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW certificate, CommitLogData(certificate), CoveredPrefix(ancestry, certificate.entries),
           LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), ~IsPrefix(CommitTarget(certificate), entries)
    PROVE ~SnapshotCoversPrefix(entries, CommitTarget(certificate))
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term /\ certificate.term \in Nat
          /\ IsPrefix(CommitTarget(certificate), certificate.entries) /\ certificate.entries \in Seq(LogEntry)
    BY CommitLogDataProperties, SMT
<1>covered. CoveredPrefix(ancestry, CommitTarget(certificate))
    BY <1>target, CoveredPrefixRestriction, SMT
<1> QED BY <1>target, <1>covered, DataFreshWordContainsProtectedTarget, SMT

LEMMA DataFamilyEntryHasExactPrefixWitness ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW entries \in Seq(LogEntry), CoveredPrefix(ancestry, entries), NEW index \in DOMAIN entries
    PROVE \E witness \in ancestry:
              /\ witness.edge = LogEntryEdge(entries, index)
              /\ IsPrefix(witness.prefix, entries)
<1>consistent. WitnessEdgeConsistency(ancestry) BY DataFamilyEdgeConsistency, SMT
<1>witness. PICK witness \in ancestry:
        /\ witness.prefix = SubSeq(entries, 1, index) /\ witness.edge.index = index
    BY <1>consistent, DataFamilyCoveredEntryHasPrefixWitness, SMT
<1>prefix. IsPrefix(witness.prefix, entries) /\ index \in DOMAIN witness.prefix
    BY <1>witness, SubSeqProperties, ElementOfSeq, LenProperties, SMT DEF IsPrefix
<1>edge. witness.edge = LogEntryEdge(entries, index)
    BY <1>witness, <1>prefix, PrefixEntryEdgesEqual, SMT DEF PrefixWitnessFamilyData, WitnessPrefixData
<1> QED BY <1>witness, <1>prefix, <1>edge, SMT

LEMMA PairAncestryIsPrefixClosed ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry)
    PROVE PrefixWitnessFamilyData(PairAncestry(ancestry, left, right))
<1> SUFFICES ASSUME NEW witness \in PairAncestry(ancestry, left, right), NEW index \in DOMAIN witness.prefix
             PROVE \E earlier \in PairAncestry(ancestry, left, right): earlier.edge = LogEntryEdge(witness.prefix, index)
    BY SMT DEF PrefixWitnessFamilyData, PairAncestry
<1>data. witness.prefix \in Seq(LogEntry) /\ CoveredPrefix(ancestry, witness.prefix)
    BY SMT DEF PrefixWitnessFamilyData, WitnessPrefixData, PairAncestry, CoveredPrefix
<1>earlier. PICK earlier \in ancestry:
        /\ earlier.edge = LogEntryEdge(witness.prefix, index) /\ IsPrefix(earlier.prefix, witness.prefix)
    BY <1>data, DataFamilyEntryHasExactPrefixWitness, SMT
<1>prefix. IsPrefix(earlier.prefix, left) \/ IsPrefix(earlier.prefix, right)
    BY <1>data, <1>earlier, SequencePrefixTransitive, SMT
    DEF PairAncestry, PrefixWitnessFamilyData, WitnessPrefixData
<1> QED BY <1>earlier, <1>prefix, SMT DEF PairAncestry

LEMMA PairAncestryCoversBothWords ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right)
    PROVE CoveredPrefix(PairAncestry(ancestry, left, right), left)
          /\ CoveredPrefix(PairAncestry(ancestry, left, right), right)
    BY DataFamilyEntryHasExactPrefixWitness, SMT DEF CoveredPrefix, PairAncestry

LEMMA BarrierParentIsInsideTarget ==
    ASSUME NEW witness, WitnessPrefixData(witness), NEW certificate, CommitPrefixData(certificate),
           ConfigurationBarrierFor(witness, certificate)
    PROVE /\ ConfigurationOccurrenceData(certificate.configuration)
          /\ LastConfigChangeIndex(certificate.configuration.prefix) = certificate.configuration.index
          /\ IsPrefix(certificate.configuration.prefix, CommitTarget(certificate))
<1>data. certificate.entries \in Seq(LogEntry)
          /\ ConfigurationOccurrenceData(certificate.configuration)
          /\ LastConfigChangeIndex(certificate.configuration.prefix) = certificate.configuration.index
    BY LatestConfigurationOccurrenceData, ConfigurationOccurrencePrefixIndex, SMT DEF CommitPrefixData
<1>target. CommitTarget(certificate) \in Seq(LogEntry)
          /\ IsPrefix(CommitTarget(certificate), certificate.entries) /\ Len(CommitTarget(certificate)) = certificate.index
    BY CommitPrefixDataTargetProperties, SMT
<1>prefix. IsPrefix(certificate.configuration.prefix, certificate.entries)
    BY <1>data, ConfigurationIndexProperties, SubSeqProperties, ElementOfSeq, LenProperties, SMT
    DEF CommitPrefixData, LatestConfigurationOccurrence, IsPrefix
<1>inside. IsPrefix(certificate.configuration.prefix, CommitTarget(certificate))
    BY <1>data, <1>target, <1>prefix, PrefixesWithBoundedLength, SMT
    DEF ConfigurationBarrierFor, ConfigurationOccurrenceData
<1> QED BY <1>data, <1>inside, SMT

LEMMA PairedParentHistoryProperties ==
    ASSUME NEW ancestry, IsFiniteSet(ancestry), PrefixWitnessFamilyData(ancestry),
           NEW commits, ConfigurationBarrierAncestry(ancestry, commits),
           \A certificate \in commits: CommitPrefixData(certificate),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           \A certificate \in FamilyBarriers(ancestry, commits):
               IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right)
    PROVE /\ ConfigurationHistoryData(FamilyParentHistory(ancestry))
          /\ ConfigurationHistoryCompatible(FamilyParentHistory(ancestry))
          /\ \A occurrence \in FamilyParentHistory(ancestry):
                 /\ LastConfigChangeIndex(occurrence.prefix) = occurrence.index
                 /\ IsPrefix(occurrence.prefix, left) /\ IsPrefix(occurrence.prefix, right)
<1>finite. IsFiniteSet(FamilyParentHistory(ancestry))
    <2>selected. IsFiniteSet({entry \in ancestry: entry.edge.entry.members # Nil}) BY FS_Subset, SMT
    <2>image. IsFiniteSet({LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1)):
                            witness \in {entry \in ancestry: entry.edge.entry.members # Nil}})
        BY <2>selected, FS_Image, Isa
    <2> QED BY <2>image, FS_Union, FS_Singleton, SMT DEF FamilyParentHistory
<1>occurrences. \A occurrence \in FamilyParentHistory(ancestry):
        /\ ConfigurationOccurrenceData(occurrence)
        /\ LastConfigChangeIndex(occurrence.prefix) = occurrence.index
        /\ IsPrefix(occurrence.prefix, left) /\ IsPrefix(occurrence.prefix, right)
    <2> SUFFICES ASSUME NEW occurrence \in FamilyParentHistory(ancestry)
                 PROVE /\ ConfigurationOccurrenceData(occurrence)
                       /\ LastConfigChangeIndex(occurrence.prefix) = occurrence.index
                       /\ IsPrefix(occurrence.prefix, left) /\ IsPrefix(occurrence.prefix, right)
        BY SMT
    <2>initial. CASE occurrence = InitialConfigurationOccurrence
        BY <2>initial, InitialConfigurationOccurrenceData, EmptySeq, SubSeqEmpty,
           ConfigurationIndexProperties, LenProperties, SMT DEF InitialConfigurationOccurrence, IsPrefix
    <2>parent. CASE occurrence # InitialConfigurationOccurrence
        <3>witness. PICK witness \in ancestry:
                /\ witness.edge.entry.members # Nil
                /\ occurrence = LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
            BY <2>parent, SMT DEF FamilyParentHistory
        <3>certificate. PICK certificate \in commits: ConfigurationBarrierFor(witness, certificate)
            BY <3>witness, SMT DEF ConfigurationBarrierAncestry
        <3>target. IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right)
            BY <3>witness, <3>certificate, SMT DEF FamilyBarriers
        <3>inside. ConfigurationOccurrenceData(occurrence)
                   /\ LastConfigChangeIndex(occurrence.prefix) = occurrence.index
                   /\ IsPrefix(occurrence.prefix, CommitTarget(certificate))
            BY <3>witness, <3>certificate, BarrierParentIsInsideTarget, SMT
            DEF PrefixWitnessFamilyData, ConfigurationBarrierFor
        <3> QED BY <3>certificate, <3>target, <3>inside, CommitPrefixDataTargetProperties,
            SequencePrefixTransitive, SMT DEF ConfigurationOccurrenceData
    <2> QED BY <2>initial, <2>parent, SMT
<1>compatible. ConfigurationHistoryCompatible(FamilyParentHistory(ancestry))
    BY <1>occurrences, PrefixesWithBoundedLength, SMT DEF ConfigurationHistoryCompatible, ConfigurationOccurrenceData
<1> QED BY <1>finite, <1>occurrences, <1>compatible, SMT DEF ConfigurationHistoryData, FamilyParentHistory

LEMMA PairedParentsSupplyEqualOrAdjacentConfigurations ==
    ASSUME NEW ancestry, IsFiniteSet(ancestry), PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW commits, ConfigurationBarrierAncestry(ancestry, commits),
           \A certificate \in commits: CommitPrefixData(certificate),
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry), TermsOrdered(left), TermsOrdered(right),
           CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right),
           \A certificate \in FamilyBarriers(PairAncestry(ancestry, left, right), commits):
               IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right)
    PROVE EqualOrAdjacentConfigurations(ConfigOf(left), ConfigOf(right))
<1> DEFINE selected == PairAncestry(ancestry, left, right)
           barriers == FamilyBarriers(selected, commits)
           history == FamilyParentHistory(selected)
           working == LatestEvidenceOccurrence(history)
<1>family. IsFiniteSet(selected) /\ PrefixWitnessFamilyData(selected) /\ TermPrefixOrder(selected)
    <2>prefix. PrefixWitnessFamilyData(selected) BY PairAncestryIsPrefixClosed, SMT DEF selected
    <2>subset. selected \subseteq ancestry BY SMT DEF selected, PairAncestry
    <2>finite. IsFiniteSet(selected) BY <2>subset, FS_Subset, SMT
    <2>order. TermPrefixOrder(selected) BY <2>subset, SMT DEF TermPrefixOrder
    <2> QED BY <2>prefix, <2>finite, <2>order, SMT
<1>covered. CoveredPrefix(selected, left) /\ CoveredPrefix(selected, right)
    BY PairAncestryCoversBothWords, SMT DEF selected
<1>barriers. ConfigurationBarrierAncestry(selected, barriers)
    BY SMT DEF selected, barriers, PairAncestry, FamilyBarriers, ConfigurationBarrierAncestry
<1>history. ConfigurationHistoryData(history) /\ ConfigurationHistoryCompatible(history)
             /\ \A occurrence \in history:
                    /\ LastConfigChangeIndex(occurrence.prefix) = occurrence.index
                    /\ IsPrefix(occurrence.prefix, left) /\ IsPrefix(occurrence.prefix, right)
    BY <1>family, <1>barriers, PairedParentHistoryProperties, SMT
    DEF history, barriers, FamilyBarriers
<1>working. ConfigurationOccurrenceData(working) /\ working \in history
             /\ LastConfigChangeIndex(working.prefix) = working.index
             /\ IsPrefix(working.prefix, left) /\ IsPrefix(working.prefix, right)
    BY <1>history, LatestEvidenceOccurrenceProperties, SMT DEF working
<1>parents. \A witness \in selected: witness.edge.entry.members # Nil =>
        LET parent == LatestConfigurationOccurrence(SubSeq(witness.prefix, 1, witness.edge.index - 1))
        IN /\ parent.index <= working.index /\ IsPrefix(parent.prefix, working.prefix)
    BY <1>history, LatestEvidenceOccurrenceProperties, LatestCompatibleOccurrenceProperties, SMT
    DEF working, history, FamilyParentHistory
<1>commit_data. \A certificate \in barriers: CommitPrefixData(certificate)
    BY SMT DEF barriers, FamilyBarriers
<1>frontier. BarrierFrontierData(selected, barriers, working)
    BY <1>family, <1>barriers, <1>working, <1>parents, <1>commit_data, SMT DEF BarrierFrontierData
<1>profiles. ProtectedPrefixData(selected, barriers, working, left)
              /\ ProtectedPrefixData(selected, barriers, working, right)
    BY <1>covered, <1>working, SMT DEF ProtectedPrefixData, selected, barriers
<1> QED BY <1>frontier, <1>profiles, DataProtectedConfigurationsAreEqualOrAdjacent, SMT

LEMMA OlderWordParentsAreInLaterCommitLog ==
    ASSUME NEW ancestry, PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW commits, \A certificate \in commits:
               /\ CommitLogData(certificate)
               /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term),
           NEW right, CommitLogData(right), CoveredPrefix(ancestry, right.entries),
           NEW left \in Seq(LogEntry), TermsOrdered(left), CoveredPrefix(ancestry, left),
           ~SnapshotCoversPrefix(left, CommitTarget(right)), NEW witness \in ancestry,
           IsPrefix(witness.prefix, left), NEW certificate \in commits, ConfigurationBarrierFor(witness, certificate)
    PROVE IsPrefix(CommitTarget(certificate), right.entries)
<1>data. WitnessPrefixData(witness) /\ CommitLogData(certificate)
    BY SMT DEF PrefixWitnessFamilyData
<1>right. right.entries \in Seq(LogEntry) /\ LastTerm(right.entries) = right.term
          /\ Len(right.entries) > 0 /\ CommitTarget(right) \in Seq(LogEntry)
          /\ Len(CommitTarget(right)) > 0 /\ LastTerm(CommitTarget(right)) = right.term
          /\ IsPrefix(CommitTarget(right), right.entries) /\ right.term \in Nat
    BY CommitLogDataProperties, SMT
<1>types. LastTerm(left) \in Nat /\ Len(left) \in Nat /\ LastTerm(witness.prefix) \in Nat
          /\ certificate.term \in Nat /\ right.term \in Nat
    BY <1>data, <1>right, LastTermTypeOK, LenProperties, SMT DEF WitnessPrefixData, CommitLogData, CommitPrefixData
<1>bound. LastTerm(left) <= right.term
    BY <1>right, <1>types, SMT DEF SnapshotCoversPrefix
<1>inside. IsPrefix(CommitTarget(certificate), witness.prefix)
    BY <1>data, BarrierTargetInsideCreatorPrefix, SMT DEF CommitLogData
<1>same. CASE LastTerm(left) = right.term
    <2>length. Len(left) <= Len(right.entries) /\ Len(left) > 0
        BY <1>right, <1>data, <1>same, LenProperties, SMT
        DEF SnapshotCoversPrefix, WitnessPrefixData, IsPrefix
    <2>prefix. IsPrefix(left, right.entries)
        BY <1>right, <1>same, <2>length, DataCoveredWordsWithSameLastTermAreOrdered, SMT
    <2>target. CommitTarget(certificate) \in Seq(LogEntry) /\ witness.prefix \in Seq(LogEntry)
        BY <1>data, CommitLogDataProperties, SMT DEF WitnessPrefixData
    <2>left. IsPrefix(CommitTarget(certificate), left)
        BY <1>inside, <2>target, SequencePrefixTransitive, SMT
    <2> QED BY <1>right, <2>target, <2>left, <2>prefix, SequencePrefixTransitive, SMT
<1>earlier. CASE LastTerm(left) < right.term
    <2>term. certificate.term <= LastTerm(left)
        BY <1>data, OrderedPrefixLastTermBound, LenProperties, SMT
        DEF WitnessPrefixData, ConfigurationBarrierFor, LogEntryEdge, LastTerm
    <2>last. PICK last \in ancestry: last.prefix = right.entries /\ last.edge.term = right.term
        BY <1>right, DataCoveredWordHasLastWitness, SMT
    <2> QED BY <1>types, <1>earlier, <2>term, <2>last, SMT DEF LaterTermPrefixProtection
<1> QED BY <1>types, <1>bound, <1>same, <1>earlier, SMT

LEMMA ParentBarriersGiveAdjacencyOrShorterMissingLog ==
    ASSUME NEW ancestry, IsFiniteSet(ancestry), PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW commits, ConfigurationBarrierAncestry(ancestry, commits),
           \A certificate \in commits:
               /\ CommitLogData(certificate)
               /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term),
           NEW right, CommitLogData(right), CoveredPrefix(ancestry, right.entries),
           NEW left \in Seq(LogEntry), TermsOrdered(left), CoveredPrefix(ancestry, left),
           ~SnapshotCoversPrefix(left, CommitTarget(right))
    PROVE EqualOrAdjacentConfigurations(ConfigOf(left), ConfigOf(right.entries))
          \/ \E certificate \in commits:
                 ~IsPrefix(CommitTarget(certificate), left) /\ Len(certificate.entries) < Len(right.entries)
<1>right. right.entries \in Seq(LogEntry) /\ TermsOrdered(right.entries)
    BY SMT DEF CommitLogData, CommitPrefixData
<1>missing. CASE \E witness \in ancestry: \E certificate \in commits:
        /\ IsPrefix(witness.prefix, right.entries) /\ witness.edge.entry.members # Nil
        /\ ConfigurationBarrierFor(witness, certificate) /\ ~IsPrefix(CommitTarget(certificate), left)
    <2>chosen. PICK witness, certificate:
            /\ witness \in ancestry /\ certificate \in commits
            /\ IsPrefix(witness.prefix, right.entries) /\ witness.edge.entry.members # Nil
            /\ ConfigurationBarrierFor(witness, certificate) /\ ~IsPrefix(CommitTarget(certificate), left)
        BY <1>missing, SMT
    <2>length. Len(certificate.entries) < Len(right.entries)
        BY <1>right, <2>chosen, BarrierTargetInsideCreatorPrefix, LenProperties, SMT
        DEF PrefixWitnessFamilyData, WitnessPrefixData, CommitLogData, CommitPrefixData, IsPrefix
    <2> QED BY <2>chosen, <2>length, SMT
<1>held. CASE ~\E witness \in ancestry: \E certificate \in commits:
        /\ IsPrefix(witness.prefix, right.entries) /\ witness.edge.entry.members # Nil
        /\ ConfigurationBarrierFor(witness, certificate) /\ ~IsPrefix(CommitTarget(certificate), left)
    <2>parents. \A certificate \in FamilyBarriers(PairAncestry(ancestry, left, right.entries), commits):
            IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right.entries)
        <3> SUFFICES ASSUME NEW certificate \in FamilyBarriers(PairAncestry(ancestry, left, right.entries), commits)
                     PROVE IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right.entries)
            BY SMT
        <3>witness. PICK witness \in ancestry:
                /\ (IsPrefix(witness.prefix, left) \/ IsPrefix(witness.prefix, right.entries))
                /\ witness.edge.entry.members # Nil /\ ConfigurationBarrierFor(witness, certificate)
            BY SMT DEF FamilyBarriers, PairAncestry
        <3>data. CommitLogData(certificate) /\ certificate \in commits /\ WitnessPrefixData(witness)
            BY SMT DEF FamilyBarriers, PrefixWitnessFamilyData
        <3>inside. IsPrefix(CommitTarget(certificate), witness.prefix)
                   /\ CommitTarget(certificate) \in Seq(LogEntry) /\ witness.prefix \in Seq(LogEntry)
            BY <3>witness, <3>data, BarrierTargetInsideCreatorPrefix, CommitLogDataProperties, SMT
            DEF CommitLogData, WitnessPrefixData
        <3>left. CASE IsPrefix(witness.prefix, left)
            <4>target. IsPrefix(CommitTarget(certificate), left)
                BY <3>inside, <3>left, SequencePrefixTransitive, SMT
            <4>later. IsPrefix(CommitTarget(certificate), right.entries)
                BY <3>witness, <3>data, <3>left, OlderWordParentsAreInLaterCommitLog, SMT
            <4> QED BY <4>target, <4>later, SMT
        <3>right. CASE IsPrefix(witness.prefix, right.entries)
            <4>target. IsPrefix(CommitTarget(certificate), right.entries)
                BY <1>right, <3>inside, <3>right, SequencePrefixTransitive, SMT
            <4>left. IsPrefix(CommitTarget(certificate), left)
                BY <1>held, <3>witness, <3>data, <3>right, SMT
            <4> QED BY <4>target, <4>left, SMT
        <3> QED BY <3>witness, <3>left, <3>right, SMT
    <2>shape. EqualOrAdjacentConfigurations(ConfigOf(left), ConfigOf(right.entries))
        BY <1>right, <2>parents, PairedParentsSupplyEqualOrAdjacentConfigurations, SMT DEF CommitLogData
    <2> QED BY <2>shape, SMT
<1> QED BY <1>missing, <1>held, SMT

\* Descend through actual configuration barriers, each with a shorter creator
\* log, until its replication configuration intersects the query configuration.
LEMMA MissingProtectedTargetHasBlockingCertificate ==
    ASSUME NEW ancestry, IsFiniteSet(ancestry), PrefixWitnessFamilyData(ancestry), TermPrefixOrder(ancestry),
           NEW commits, ConfigurationBarrierAncestry(ancestry, commits),
           \A certificate \in commits:
               /\ CommitLogData(certificate) /\ CoveredPrefix(ancestry, certificate.entries)
               /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term),
           NEW initial, CommitLogData(initial), CoveredPrefix(ancestry, initial.entries),
           LaterTermPrefixProtection(ancestry, CommitTarget(initial), initial.term),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           ~IsPrefix(CommitTarget(initial), entries)
    PROVE \E blocker \in commits \cup {initial}:
              /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
              /\ ~SnapshotCoversPrefix(entries, CommitTarget(blocker))
<1> DEFINE P(bound) == \A certificate \in commits \cup {initial}:
        /\ Len(certificate.entries) <= bound /\ ~IsPrefix(CommitTarget(certificate), entries)
        => \E blocker \in commits \cup {initial}:
               /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
               /\ ~SnapshotCoversPrefix(entries, CommitTarget(blocker))
<1>base. P(0)
    BY CommitLogDataProperties, LenProperties, SMT DEF P
<1>step. \A bound \in Nat: P(bound) => P(bound + 1)
    <2> SUFFICES ASSUME NEW bound \in Nat, P(bound), NEW certificate \in commits \cup {initial},
                          Len(certificate.entries) <= bound + 1, ~IsPrefix(CommitTarget(certificate), entries)
                 PROVE \E blocker \in commits \cup {initial}:
                           /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
                           /\ ~SnapshotCoversPrefix(entries, CommitTarget(blocker))
        BY SMT DEF P
    <2>data. CommitLogData(certificate) /\ CoveredPrefix(ancestry, certificate.entries)
              /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
        BY SMT
    <2>stale. ~SnapshotCoversPrefix(entries, CommitTarget(certificate))
        BY <2>data, MissingCommitTargetIsNumericallyStale, SMT
    <2>descent. EqualOrAdjacentConfigurations(ConfigOf(entries), ConfigOf(certificate.entries))
                \/ \E earlier \in commits:
                       ~IsPrefix(CommitTarget(earlier), entries) /\ Len(earlier.entries) < Len(certificate.entries)
        BY <2>data, <2>stale, ParentBarriersGiveAdjacencyOrShorterMissingLog, SMT
    <2>adjacent. CASE EqualOrAdjacentConfigurations(ConfigOf(entries), ConfigOf(certificate.entries))
        <3>types. ConfigOf(entries) \subseteq Server /\ ConfigOf(certificate.entries) \subseteq Server
                  /\ certificate.replication \in Quorums(ConfigOf(certificate.entries))
            BY <2>data, ConfigurationType, SMT DEF CommitLogData, CommitPrefixData, LatestConfigurationOccurrence
        <3>blocks. CertificateBlocksConfiguration(certificate, ConfigOf(entries))
            BY <2>adjacent, <3>types, EqualOrAdjacentQuorumsIntersect, SMT DEF CertificateBlocksConfiguration
        <3> QED BY <2>stale, <3>blocks, SMT
    <2>earlier. CASE \E earlier \in commits:
            ~IsPrefix(CommitTarget(earlier), entries) /\ Len(earlier.entries) < Len(certificate.entries)
        <3>chosen. PICK earlier \in commits:
                ~IsPrefix(CommitTarget(earlier), entries) /\ Len(earlier.entries) < Len(certificate.entries)
            BY <2>earlier, SMT
        <3>bound. Len(earlier.entries) <= bound
            BY <2>data, <3>chosen, LenProperties, SMT DEF CommitLogData, CommitPrefixData
        <3> QED BY <3>chosen, <3>bound, SMT DEF P
    <2> QED BY <2>descent, <2>adjacent, <2>earlier, SMT
<1> HIDE DEF P
<1>all. \A bound \in Nat: P(bound) BY <1>base, <1>step, NatInduction, Isa
<1> QED BY <1>all, LenProperties, SMT DEF P, CommitLogData, CommitPrefixData

LEMMA JointWitnessesSupplyBarrierExclusionData ==
    ASSUME NEW voteHistory, NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits), CommitPrefixCoverage(ancestry, commits)
    PROVE BarrierExclusionData(ancestry, commits)
<1>family. IsFiniteSet(ancestry) /\ PrefixWitnessFamilyData(ancestry) /\ TermPrefixOrder(ancestry)
    BY SMT DEF JointMembershipWitnesses, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData
<1>barriers. ConfigurationBarrierAncestry(ancestry, commits)
    BY SMT DEF JointMembershipWitnesses
<1>commits. \A certificate \in commits: CommitLogData(certificate)
    BY SMT DEF JointMembershipWitnesses, CommitCertificateFamily, RetainedCommitCertificate,
        CommitLogData, CommitPrefixData
<1>covered. \A certificate \in commits: CoveredPrefix(ancestry, certificate.entries)
    BY SMT DEF CommitPrefixCoverage
<1>boundary. \A certificate \in commits:
        LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
    BY SMT DEF JointMembershipWitnesses, JointCommitProtection
<1> QED BY <1>family, <1>barriers, <1>commits, <1>covered, <1>boundary, SMT DEF BarrierExclusionData

LEMMA PostJointWitnessesSupplyBarrierExclusionData ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW ancestry, NEW commits, JointMembershipData(nextVoteHistory, ancestry, commits)', CommitPrefixCoverage(ancestry, commits)'
    PROVE BarrierExclusionData(ancestry, commits)
<1>family. IsFiniteSet(ancestry) /\ PrefixWitnessFamilyData(ancestry) /\ TermPrefixOrder(ancestry)
    BY SMT DEF JointMembershipData, CertificateFamily, CertificateWitness, PrefixWitnessFamilyData,
        WitnessPrefixData, TermPrefixOrder
<1>barriers. ConfigurationBarrierAncestry(ancestry, commits)
    BY SMT DEF JointMembershipData, ConfigurationBarrierAncestry, ConfigurationBarrierFor
<1>commits. \A certificate \in commits: CommitLogData(certificate)
    BY SMT DEF JointMembershipData, CommitCertificateFamily, RetainedCommitCertificate,
        CommitLogData, CommitPrefixData
<1>covered. \A certificate \in commits: CoveredPrefix(ancestry, certificate.entries)
    BY SMT DEF CommitPrefixCoverage, CoveredPrefix
<1>boundary. \A certificate \in commits:
        LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
    BY SMT DEF JointMembershipData, JointCommitProtection, LaterTermPrefixProtection
<1> QED BY <1>family, <1>barriers, <1>commits, <1>covered, <1>boundary, SMT DEF BarrierExclusionData

LEMMA ProtectedRetainedCertificateHasPhysicalQuorum ==
    ASSUME NEW voteHistory, MembershipJointCore(voteHistory), NEW ancestry, NEW commits, JointMembershipWitnesses(voteHistory, ancestry, commits),
           FrozenRequestPrefixesAgree(ancestry), FrozenAcknowledgmentPrefixHistory(ancestry),
           NEW certificate, RetainedCommitCertificate(voteHistory, certificate),
           IsPrefix(CommitTarget(certificate), log[certificate.leader]),
           ProtectedAppendRequests(CommitTarget(certificate), certificate.term)
    PROVE certificate.replication \subseteq ProtectedVoters(CommitTarget(certificate))
<1>base. TypeOK /\ CertificateFamily(voteHistory, ancestry) /\ TermPrefixOrder(ancestry)
    BY JointCoreBase, SMT DEF JointMembershipWitnesses
<1>target. CommitTarget(certificate) \in Seq(LogEntry) /\ Len(CommitTarget(certificate)) > 0
          /\ LastTerm(CommitTarget(certificate)) = certificate.term
          /\ TargetCampaignEvidence(voteHistory, certificate.leader, certificate.term, CommitTarget(certificate))
          /\ CoveredPrefix(ancestry, CommitTarget(certificate))
    BY <1>base, CommitCertificateTargetProperties, CommitCertificateSuppliesTargetCampaignEvidence,
       CurrentLogPrefixCovered, LenProperties, SMT
    DEF RetainedCommitCertificate, JointMembershipWitnesses, LastTerm, TypeOK, LogVarsTypeOK
<1> SUFFICES ASSUME NEW peer \in certificate.replication
             PROVE peer \in ProtectedVoters(CommitTarget(certificate)) BY SMT
<1>types. peer \in Server /\ certificate.leader \in Server /\ certificate.term \in Nat
    BY SMT DEF RetainedCommitCertificate, Quorums
<1>self. CASE peer = certificate.leader
    BY <1>types, <1>self, SMT DEF ProtectedVoters
<1>other. CASE peer # certificate.leader
    <2>recorded. RecordedPrefixAcknowledgment(peer, certificate.leader, certificate.term, CommitTarget(certificate))
        BY <1>other, SMT DEF RetainedCommitCertificate
    <2>response. PICK response \in messages:
            /\ SuccessfulAppendResponse(response) /\ response.msource = peer
            /\ response.mdest = certificate.leader /\ response.mterm = certificate.term
            /\ response.mmatchIndex >= Len(CommitTarget(certificate))
        BY <2>recorded, Zenon DEF RecordedPrefixAcknowledgment
    <2>frozen. PICK request, prefix:
            /\ request \in AppendRequests /\ prefix \in Seq(LogEntry)
            /\ ResponseMatchesRequest(response, request) /\ RequestPrefixData(request, prefix)
            /\ CoveredPrefix(ancestry, prefix) /\ Len(prefix) = response.mmatchIndex
        BY <2>response, SMT DEF FrozenAcknowledgmentPrefixHistory
    <2>boundary. RequestCampaignBoundary(voteHistory, request, prefix)
        <3>old. PICK old \in Seq(LogEntry):
                /\ RequestPrefixData(request, old) /\ CoveredPrefix(ancestry, old) /\ RequestCampaignBoundary(voteHistory, request, old)
            BY <2>frozen, SMT DEF JointMembershipWitnesses, RequestPrefixAncestry, AncestralRequestPrefix
        <3>fields. request.mentries \in Seq(LogEntry)
            BY <1>base, <2>frozen, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
        <3>equal. old = prefix
            BY <1>base, <2>frozen, <3>old, <3>fields, CoveredRequestPrefixIsUnique, Zenon
        <3> QED BY <3>old, <3>equal, SMT
    <2>inside. IsPrefix(CommitTarget(certificate), prefix)
        BY <1>base, <1>target, <1>types, <2>response, <2>frozen, <2>boundary, FrozenRequestPrefixContainsTarget, SMT
        DEF ResponseMatchesRequest
    <2>history. IsPrefix(CommitTarget(certificate), log[peer])
                \/ ConflictingHigherAppendRequest(peer, certificate.term, CommitTarget(certificate))
        BY <1>target, <2>response, <2>frozen, <2>inside, FrozenAcknowledgmentFixedTargetHistory, SMT
    <2>no_conflict. ~ConflictingHigherAppendRequest(peer, certificate.term, CommitTarget(certificate))
        <3> SUFFICES ASSUME NEW conflicting \in AppendRequests,
                              conflicting.mdest = peer, conflicting.mterm > certificate.term,
                              conflicting.mterm <= currentTerm[peer],
                              ~RequestRespectsPrefix(conflicting, CommitTarget(certificate))
                     PROVE FALSE
            BY SMT DEF ConflictingHigherAppendRequest
        <3>term. conflicting.mterm \in Nat
            BY <1>base, MessageFieldsTypeOK, Zenon DEF TypeOK, MsgTypeOK, AppendRequests
        <3>bound. conflicting.mterm >= certificate.term BY <1>types, <3>term, SMT
        <3>respect. RequestRespectsPrefix(conflicting, CommitTarget(certificate))
            BY <3>bound, SMT DEF ProtectedAppendRequests
        <3> QED BY <3>respect, SMT
    <2> QED BY <1>types, <2>history, <2>no_conflict, SMT DEF ProtectedVoters
<1> QED BY <1>self, <1>other, SMT

LEMMA SnapshotFreshnessCoversHeldPrefix ==
    ASSUME NEW entries \in Seq(LogEntry), TermsOrdered(entries), NEW target \in Seq(LogEntry), IsPrefix(target, entries),
           NEW snapshot \in Seq(LogEntry),
           LastTerm(snapshot) > LastTerm(entries)
               \/ (LastTerm(snapshot) = LastTerm(entries) /\ Len(snapshot) >= Len(entries))
    PROVE SnapshotCoversPrefix(snapshot, target)
<1> DEFINE request == [mlastLogTerm |-> LastTerm(snapshot), mlastLogIndex |-> Len(snapshot)]
<1>covers. VoteRequestCoversPrefix(request, target)
    BY FreshRequestCoversHeldPrefix, LastTermTypeOK, LenProperties, SMT DEF request
<1> QED BY <1>covers, SMT DEF request, VoteRequestCoversPrefix, SnapshotCoversPrefix

LEMMA PostFutureCertificateCannotBeBlocked ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), TypeOK', SendInvariant', PositiveVoteResponseRequestInv',
           \A server \in Server: TermsOrdered(log'[server]), NEW candidate \in Server, NEW term \in Nat,
           currentTerm'[candidate] < term, NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           OpportunityCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)',
           NEW blocker, CommitLogData(blocker), CertificateBlocksConfiguration(blocker, ConfigOf(snapshot)),
           blocker.replication \subseteq ProtectedVoters(CommitTarget(blocker))',
           ~SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
    PROVE FALSE
<1>snapshot. snapshot = log'[candidate]
    BY SMT DEF OpportunityCertificate, CampaignOpportunity
<1>quorum. support \in Quorums(ConfigOf(snapshot))
    BY SMT DEF OpportunityCertificate, LatestConfigurationOccurrence
<1>intersection. blocker.replication \cap support # {}
    BY <1>quorum, SMT DEF CertificateBlocksConfiguration
<1>peer. PICK peer \in support \cap blocker.replication: TRUE
    BY <1>intersection, Zenon
<1>held. peer \in Server /\ IsPrefix(CommitTarget(blocker), log'[peer])
    BY <1>peer, SMT DEF ProtectedVoters
<1>target. CommitTarget(blocker) \in Seq(LogEntry)
    BY CommitLogDataProperties, SMT
<1>no_vote. ~RecordedCampaignVote(nextVoteHistory, peer, candidate, term)'
    BY <1>held, SMT DEF RecordedCampaignVote, Grant, Started, PositiveVoteResponseRequestInv,
        SendInvariant, TypeOK, ServerVarsTypeOK
<1>self. CASE peer = candidate
    <2>fresh. SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
        BY <1>snapshot, <1>held, <1>target, <1>self, SnapshotFreshnessCoversHeldPrefix,
           LastTermTypeOK, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>fresh, SMT
<1>other. CASE peer # candidate
    <2>eligible. NewPeerVoteEligible(peer, candidate, term, snapshot)'
        BY <1>peer, <1>held, <1>no_vote, <1>other, SMT DEF OpportunityCertificate, OpportunityVoters
    <2>fresh. SnapshotCoversPrefix(snapshot, CommitTarget(blocker))
        BY <1>held, <1>target, <2>eligible, SnapshotFreshnessCoversHeldPrefix, SMT
        DEF NewPeerVoteEligible, SnapshotFreshFor, TypeOK, LogVarsTypeOK
    <2> QED BY <2>fresh, SMT
<1> QED BY <1>self, <1>other, SMT

LEMMA MissingProtectedTargetHasTermBoundedBlocker ==
    ASSUME NEW ancestry, NEW commits, BarrierExclusionData(ancestry, commits),
           NEW initial, CommitLogData(initial), CoveredPrefix(ancestry, initial.entries),
           LaterTermPrefixProtection(ancestry, CommitTarget(initial), initial.term),
           NEW entries \in Seq(LogEntry), TermsOrdered(entries), CoveredPrefix(ancestry, entries),
           ~IsPrefix(CommitTarget(initial), entries)
    PROVE \E blocker \in TermCommits(commits, initial.term) \cup {initial}:
              /\ CertificateBlocksConfiguration(blocker, ConfigOf(entries))
              /\ ~SnapshotCoversPrefix(entries, CommitTarget(blocker))
<1>initial_data. initial.term \in Nat /\ initial.entries \in Seq(LogEntry)
                  /\ CommitTarget(initial) \in Seq(LogEntry) /\ LastTerm(CommitTarget(initial)) = initial.term
    BY CommitLogDataProperties, SMT
<1>stale. ~SnapshotCoversPrefix(entries, CommitTarget(initial))
    BY MissingCommitTargetIsNumericallyStale, SMT DEF BarrierExclusionData
<1>bound. LastTerm(entries) <= initial.term
    BY <1>stale, <1>initial_data, LastTermTypeOK, SMT DEF SnapshotCoversPrefix
<1> DEFINE selected == TermAncestry(ancestry, initial.term)
           barriers == TermCommits(commits, initial.term)
<1>closed. PrefixWitnessFamilyData(selected)
    BY <1>initial_data, TermAncestryIsPrefixClosed, SMT DEF selected, BarrierExclusionData
<1>family. IsFiniteSet(selected) /\ PrefixWitnessFamilyData(selected) /\ TermPrefixOrder(selected)
    BY FiniteSetSubsetsAreFinite, <1>closed, SMT DEF selected, TermAncestry, BarrierExclusionData, TermPrefixOrder
<1>configurations. ConfigurationBarrierAncestry(selected, barriers)
    BY SMT DEF selected, barriers, TermAncestry, TermCommits, BarrierExclusionData,
        ConfigurationBarrierAncestry, ConfigurationBarrierFor
<1>entries. CoveredPrefix(selected, entries)
    BY <1>initial_data, <1>bound, OrderedEntriesBoundedByLastTerm, TermCoveredPrefixRestrictsAncestry, SMT DEF selected
<1>initial_bound. \A index \in DOMAIN initial.entries: initial.entries[index].term <= initial.term
    BY SMT DEF CommitLogData, EntryStructure
<1>initial_covered. CoveredPrefix(selected, initial.entries)
    BY <1>initial_data, <1>initial_bound, TermCoveredPrefixRestrictsAncestry, SMT DEF selected
<1>initial. CoveredPrefix(selected, initial.entries)
              /\ LaterTermPrefixProtection(selected, CommitTarget(initial), initial.term)
    BY <1>initial_covered, SMT DEF selected, TermAncestry, LaterTermPrefixProtection
<1>commits. \A certificate \in barriers:
        /\ CommitLogData(certificate) /\ CoveredPrefix(selected, certificate.entries)
        /\ LaterTermPrefixProtection(selected, CommitTarget(certificate), certificate.term)
    <2> SUFFICES ASSUME NEW certificate \in barriers
                 PROVE /\ CommitLogData(certificate) /\ CoveredPrefix(selected, certificate.entries)
                       /\ LaterTermPrefixProtection(selected, CommitTarget(certificate), certificate.term) BY SMT
    <2>data. CommitLogData(certificate) /\ CoveredPrefix(ancestry, certificate.entries)
              /\ LaterTermPrefixProtection(ancestry, CommitTarget(certificate), certificate.term)
              /\ certificate.term <= initial.term /\ certificate.term \in Nat /\ certificate.entries \in Seq(LogEntry)
        BY SMT DEF barriers, TermCommits, BarrierExclusionData, CommitLogData, CommitPrefixData
    <2>bound. \A index \in DOMAIN certificate.entries: certificate.entries[index].term <= initial.term
        BY <1>initial_data, <2>data, ElementOfSeq, SMT DEF CommitLogData, EntryStructure, LogEntry
    <2>covered. CoveredPrefix(selected, certificate.entries)
        BY <1>initial_data, <2>data, <2>bound, TermCoveredPrefixRestrictsAncestry, SMT DEF selected
    <2> QED BY <2>data, <2>covered, SMT DEF selected, TermAncestry, LaterTermPrefixProtection
<1> QED BY <1>family, <1>configurations, <1>entries, <1>initial, <1>commits,
    MissingProtectedTargetHasBlockingCertificate, SMT DEF selected, barriers

LEMMA PrefixesProtectedBelowTermHaveAdjacentConfigurations ==
    ASSUME NEW ancestry, NEW commits, BarrierExclusionData(ancestry, commits), NEW term \in Nat,
           NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
           TermsOrdered(left), TermsOrdered(right), CoveredPrefix(ancestry, left), CoveredPrefix(ancestry, right),
           \A index \in DOMAIN left: left[index].term < term,
           \A index \in DOMAIN right: right[index].term < term,
           \A certificate \in commits: certificate.term < term =>
               IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right)
    PROVE EqualOrAdjacentConfigurations(ConfigOf(left), ConfigOf(right))
<1>parents. \A certificate \in FamilyBarriers(PairAncestry(ancestry, left, right), commits):
        IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right)
    <2> SUFFICES ASSUME NEW certificate \in FamilyBarriers(PairAncestry(ancestry, left, right), commits)
                 PROVE IsPrefix(CommitTarget(certificate), left) /\ IsPrefix(CommitTarget(certificate), right) BY SMT
    <2>witness. PICK witness \in ancestry:
            /\ (IsPrefix(witness.prefix, left) \/ IsPrefix(witness.prefix, right))
            /\ witness.edge.entry.members # Nil /\ ConfigurationBarrierFor(witness, certificate)
        BY SMT DEF FamilyBarriers, PairAncestry
    <2>data. WitnessPrefixData(witness) /\ certificate \in commits
        BY <2>witness, SMT DEF BarrierExclusionData, PrefixWitnessFamilyData, FamilyBarriers
    <2>term. certificate.term < term
        BY <2>data, <2>witness, PrefixEntryEqual, LenProperties, SMT
        DEF WitnessPrefixData, LogEntryEdge, IsPrefix, ConfigurationBarrierFor
    <2> QED BY <2>data, <2>term, SMT
<1> QED BY <1>parents, PairedParentsSupplyEqualOrAdjacentConfigurations, SMT DEF BarrierExclusionData, CommitLogData

=======================================================================
