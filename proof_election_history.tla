------------------------------ MODULE proof_election_history ------------------------------
\* proof_election_history.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_base

TermsOrdered(entries) ==
    \A first, last \in DOMAIN entries:
        first <= last => entries[first].term <= entries[last].term

PreTermIndexes(entries, term) ==
    {index \in DOMAIN entries: entries[index].term < term}

CampaignPrefixIndex(entries, term) == MaxOrZero(PreTermIndexes(entries, term))

\* The campaign log can be recovered from a current candidate or leader by
\* removing precisely the suffix appended in its current term.
CampaignPrefix(entries, term) ==
    SubSeq(entries, 1, CampaignPrefixIndex(entries, term))

\* Prefix and index distinguish repeated memberships and competing branches.
\* At index zero the prefix is empty and members is InitialConfig.
LatestConfigurationOccurrence(entries) ==
    LET index == LastConfigChangeIndex(entries)
    IN [index |-> index, prefix |-> SubSeq(entries, 1, index),
        members |-> ConfigOf(entries)]

CampaignRequests(candidate, term, snapshot) ==
    {[mtype |-> RequestVoteRequest, mterm |-> term,
      mlastLogTerm |-> LastTerm(snapshot), mlastLogIndex |-> Len(snapshot),
      msource |-> candidate, mdest |-> peer]:
        peer \in ConfigOf(snapshot) \ {candidate}}

RecordedCampaignRequests(candidate, term) ==
    {message \in messages:
        /\ message.mtype = RequestVoteRequest
        /\ message.msource = candidate
        /\ message.mterm = term}

CampaignSnapshotInv ==
    \A candidate \in Server:
        state[candidate] \in {Candidate, Leader} =>
            RecordedCampaignRequests(candidate, currentTerm[candidate]) =
                CampaignRequests(candidate, currentTerm[candidate],
                    CampaignPrefix(log[candidate], currentTerm[candidate]))

PositiveVoteResponseRequestInv ==
    \A response \in messages:
        /\ response.mtype = RequestVoteResponse
        /\ response.mvoteGranted
        => \E request \in messages:
               /\ request.mtype = RequestVoteRequest
               /\ request.mterm = response.mterm
               /\ request.msource = response.mdest
               /\ request.mdest = response.msource

GrantedVotesRecorded ==
    \A candidate \in Server: state[candidate] \in {Candidate, Leader} =>
        \A voter \in votesGranted[candidate]: VoteFor(voter, candidate, currentTerm[candidate])

\* These finite records are existential witnesses in a state predicate.
\* They add neither protocol variables nor messages, including for a local
\* election whose sole eligible voter is the candidate itself.
CampaignHistoryRecord(record) ==
    /\ ("prefix" \in DOMAIN record =>
           /\ record.support \in Quorums(ConfigOf(record.snapshot))
           /\ \A voter \in record.support: VoteFor(voter, record.candidate, record.term))
    /\ record.candidate \in Server /\ record.term \in Nat
    /\ record.snapshot \in Seq(LogEntry)
    /\ \A index \in DOMAIN record.snapshot: record.snapshot[index].term < record.term
    /\ RecordedCampaignRequests(record.candidate, record.term) = CampaignRequests(record.candidate, record.term, record.snapshot)
    /\ record.term <= currentTerm[record.candidate]
    /\ (record.term = currentTerm[record.candidate] => votedFor[record.candidate] = record.candidate)
    /\ \A response \in messages:
           /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
           /\ response.msource = record.candidate /\ response.mterm = record.term
           => response.mdest = record.candidate
    /\ (/\ record.term = currentTerm[record.candidate]
           /\ state[record.candidate] \in {Candidate, Leader}
        => record.snapshot = CampaignPrefix(log[record.candidate], record.term))

LocalAppendRecord(record) == "prefix" \in DOMAIN record

LocalAppendOrigin(history, leader, term, entries) ==
    \E record \in history:
        /\ LocalAppendRecord(record) /\ record.candidate = leader /\ record.term = term
        /\ record.prefix \in Seq(LogEntry) /\ IsPrefix(entries, record.prefix)

LocalAppendCoverage(history) ==
    \A actor \in Server: state[actor] \in {Candidate, Leader} =>
        ((\E index \in DOMAIN log[actor]: log[actor][index].term = currentTerm[actor]) =>
            LocalAppendOrigin(history, actor, currentTerm[actor], log[actor]))

CampaignHistory(history) ==
    /\ MembershipElectionBase /\ GrantedVotesRecorded /\ TermOrderingInv
    /\ LocalAppendCoverage(history)
    /\ IsFiniteSet(history)
    /\ \A record \in history: CampaignHistoryRecord(record)
    /\ \A left, right \in history:
           left.candidate = right.candidate /\ left.term = right.term => left.snapshot = right.snapshot
    /\ \A candidate \in Server: state[candidate] \in {Candidate, Leader} =>
           \E record \in history:
               /\ record.candidate = candidate /\ record.term = currentTerm[candidate]
               /\ record.snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])

HistoryStarted(history, candidate, term) ==
    \E record \in history: record.candidate = candidate /\ record.term = term

HistoryCampaignSnapshot(history, candidate, term, snapshot) ==
    \E record \in history:
        record.candidate = candidate /\ record.term = term /\ record.snapshot = snapshot

CampaignView(history) ==
    {[candidate |-> record.candidate, term |-> record.term, snapshot |-> record.snapshot]: record \in history}

\* The selected family captures campaigns and the prefixes actually appended
\* by leaders. Both kinds of record share the immutable election snapshot.
\* Keeping this update explicit lets every certificate use the same family.
CapturedElectionSupport(actor) ==
    CHOOSE support \in Quorums(ConfigOf(CampaignPrefix(log[actor], currentTerm[actor]))):
        support \subseteq votesGranted[actor]

CampaignHistoryStep(history, larger) ==
    /\ (\A candidate \in Server: Timeout(candidate) =>
           larger = history \cup {[candidate |-> candidate,
                                  term |-> currentTerm[candidate] + 1,
                                  snapshot |-> log[candidate]]})
    /\ (\A actor \in Server: \A payload \in ClientPayload: ClientRequest(actor, payload) =>
           larger = history \cup {[candidate |-> actor, term |-> currentTerm[actor],
                                  snapshot |-> CampaignPrefix(log[actor], currentTerm[actor]),
                                  prefix |-> log'[actor],
                                  support |-> CapturedElectionSupport(actor)]})
    /\ ((/\ ~(\E candidate \in Server: Timeout(candidate))
           /\ ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)))
        => larger = history)

CampaignHistoryContextStep(history, larger) ==
    /\ CampaignHistory(history) /\ CampaignHistoryStep(history, larger)
    /\ CampaignHistory(larger)'

HistoryVoteSupport(history, candidate, term, support) ==
    /\ candidate \in Server /\ HistoryStarted(history, candidate, term)
    /\ support \subseteq Server
    /\ \A voter \in support: VoteFor(voter, candidate, term)

HistoryElectionCertificate(history, candidate, term, snapshot, occurrence, support) ==
    /\ candidate \in Server /\ term \in Nat /\ snapshot \in Seq(LogEntry)
    /\ HistoryCampaignSnapshot(history, candidate, term, snapshot)
    /\ occurrence = LatestConfigurationOccurrence(snapshot)
    /\ occurrence.members \subseteq Server /\ occurrence.members # {}
    /\ support \in Quorums(occurrence.members)
    /\ HistoryVoteSupport(history, candidate, term, support)

VoteGrantCore == VoteCurrentInv /\ VoteUniqueInv
StartedGrantInv(voteHistory) ==
    \A voter, candidate \in Server, term \in Nat:
        Started(voteHistory, voter, term) /\ Grant(voter, candidate, term) => voter = candidate

StartedCurrentInv(voteHistory) ==
    \A voter \in Server, term \in Nat:
        Started(voteHistory, voter, term) /\ currentTerm[voter] = term => votedFor[voter] = voter

VoteRecordInv(voteHistory) ==
    /\ VoteCurrentInv /\ VoteUniqueInv
    /\ StartedGrantInv(voteHistory) /\ StartedCurrentInv(voteHistory)

ActiveVotesInv(voteHistory) ==
    \A candidate \in Server: state[candidate] \in {Candidate, Leader} =>
        /\ Started(voteHistory, candidate, currentTerm[candidate])
        /\ \A voter \in votesGranted[candidate]: VoteFor(voter, candidate, currentTerm[candidate])

VoteEvidenceInv(voteHistory) ==
    /\ TypeOK /\ SendInvariant /\ LogStructureInv /\ CampaignHistory(voteHistory)
    /\ VoteRecordInv(voteHistory) /\ ActiveVotesInv(voteHistory)

MembershipVotesInv(voteHistory) ==
    /\ MembershipStructureInv /\ CampaignHistory(voteHistory)
    /\ VoteRecordInv(voteHistory) /\ ActiveVotesInv(voteHistory)

VoteSupport(voteHistory, candidate, term, support) ==
    /\ candidate \in Server /\ Started(voteHistory, candidate, term)
    /\ support \subseteq Server /\ \A voter \in support: VoteFor(voter, candidate, term)
CampaignHistoryStartConsequence ==
    \A history, candidate, term:
        CampaignHistory(history) =>
            (HistoryStarted(history, candidate, term) <=> Started(history, candidate, term))
\* A self-vote has a captured snapshot even when there is no wire request.
\* These request-shaped witnesses are proof data, never protocol messages.
RecordedVoteRequests(voteHistory, candidate, term) ==
    RecordedCampaignRequests(candidate, term) \cup
    {[mtype |-> RequestVoteRequest, mterm |-> term,
      mlastLogTerm |-> LastTerm(record.snapshot), mlastLogIndex |-> Len(record.snapshot),
      msource |-> candidate, mdest |-> candidate]:
        record \in {item \in voteHistory: item.candidate = candidate /\ item.term = term}}
RecordedVoteRequestNumericConsequence ==
    \A history, candidate, term, request:
        /\ TypeOK /\ CampaignHistory(history) /\ candidate \in Server /\ term \in Nat
        /\ request \in RecordedVoteRequests(history, candidate, term)
        => request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
MembershipCampaignsInv(voteHistory) ==
    /\ MembershipVotesInv(voteHistory)
    /\ TermOrderingInv
    /\ CampaignSnapshotInv
    /\ PositiveVoteResponseRequestInv

\* Coverage here is for current leaders. Certificates needed after a leader
\* becomes inactive require the later historical-entry ancestry argument.
CurrentElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) ==
    /\ CampaignHistory(voteHistory)
    /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
    /\ candidate \in Server
    /\ term = currentTerm[candidate]
    /\ state[candidate] = Leader
    /\ snapshot = CampaignPrefix(log[candidate], term)
    /\ snapshot \in Seq(LogEntry)
    /\ \A index \in DOMAIN snapshot: snapshot[index].term < term
    /\ occurrence = LatestConfigurationOccurrence(snapshot)
    /\ occurrence.members \subseteq Server
    /\ occurrence.members # {}
    /\ RecordedCampaignRequests(candidate, term) = CampaignRequests(candidate, term, snapshot)
    /\ support \in Quorums(occurrence.members)
    /\ VoteSupport(voteHistory, candidate, term, support)
    /\ \A voter \in support \ {candidate}:
           \E request \in CampaignRequests(candidate, term, snapshot):
               /\ request \in messages
               /\ request.mdest = voter
\* A snapshot captured from a current campaign can outlive its owner. This
\* predicate keeps the snapshot fixed rather than reading the owner's new log.
\* Its evidence alone is not a historical-prefix uniqueness assertion: later
\* entry ancestry must attach witnesses captured from actual campaigns to the
\* surviving entries or request edges that need them.
RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support) ==
    /\ CampaignHistory(voteHistory)
    /\ HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
    /\ candidate \in Server
    /\ term \in Nat
    /\ snapshot \in Seq(LogEntry)
    /\ \A index \in DOMAIN snapshot: snapshot[index].term < term
    /\ occurrence = LatestConfigurationOccurrence(snapshot)
    /\ occurrence.members \subseteq Server
    /\ occurrence.members # {}
    /\ RecordedCampaignRequests(candidate, term) = CampaignRequests(candidate, term, snapshot)
    /\ support \in Quorums(occurrence.members)
    /\ VoteSupport(voteHistory, candidate, term, support)
    /\ \A voter \in support \ {candidate}:
           \E request \in CampaignRequests(candidate, term, snapshot):
               /\ request \in messages
               /\ request.mdest = voter
------------------------------------------------------------------------

LEMMA PreTermIndexProperties ==
    \A entries \in Seq(LogEntry), term \in Nat:
        /\ PreTermIndexes(entries, term) \subseteq 1..Len(entries)
        /\ CampaignPrefixIndex(entries, term) \in 0..Len(entries)
        /\ (CampaignPrefixIndex(entries, term) = 0
            <=> PreTermIndexes(entries, term) = {})
        /\ (PreTermIndexes(entries, term) # {}
            => CampaignPrefixIndex(entries, term) \in PreTermIndexes(entries, term))
        /\ \A index \in PreTermIndexes(entries, term):
                index <= CampaignPrefixIndex(entries, term)
    BY LenProperties, PositiveIndexMaxOrZeroProperties, SMT
    DEF PreTermIndexes, CampaignPrefixIndex

LEMMA OrderedPreTermIndexes ==
    \A entries \in Seq(LogEntry), term \in Nat:
        TermsOrdered(entries) =>
            PreTermIndexes(entries, term) = 1..CampaignPrefixIndex(entries, term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW term \in Nat,
                      TermsOrdered(entries)
             PROVE PreTermIndexes(entries, term) =
                       1..CampaignPrefixIndex(entries, term)
    BY SMT
<1>maximum.
        /\ PreTermIndexes(entries, term) \subseteq 1..Len(entries)
        /\ CampaignPrefixIndex(entries, term) \in 0..Len(entries)
        /\ (PreTermIndexes(entries, term) # {}
            => CampaignPrefixIndex(entries, term) \in PreTermIndexes(entries, term))
        /\ \A index \in PreTermIndexes(entries, term):
                index <= CampaignPrefixIndex(entries, term)
    BY PreTermIndexProperties, SMT
<1>downward. \A index \in 1..CampaignPrefixIndex(entries, term):
        entries[index].term < term
    <2> SUFFICES ASSUME NEW index \in 1..CampaignPrefixIndex(entries, term)
                 PROVE entries[index].term < term
        BY SMT
    <2>positions.
            /\ index \in DOMAIN entries
            /\ CampaignPrefixIndex(entries, term) \in PreTermIndexes(entries, term)
            /\ CampaignPrefixIndex(entries, term) \in DOMAIN entries
            /\ index <= CampaignPrefixIndex(entries, term)
        BY <1>maximum, PreTermIndexProperties, LenProperties, SMT
    <2>types.
            /\ entries[index].term \in Nat
            /\ entries[CampaignPrefixIndex(entries, term)].term \in Nat
        BY <2>positions, ElementOfSeq, LenProperties, SMT DEF LogEntry
    <2>order.
            /\ entries[index].term <= entries[CampaignPrefixIndex(entries, term)].term
            /\ entries[CampaignPrefixIndex(entries, term)].term < term
        BY <2>positions, SMT DEF TermsOrdered, PreTermIndexes
    <2> QED BY <2>types, <2>order, SMT
<1> QED BY <1>maximum, <1>downward, LenProperties, SMT DEF PreTermIndexes

LEMMA CampaignPrefixProperties ==
    \A entries \in Seq(LogEntry), term \in Nat:
        TermsOrdered(entries) =>
            /\ CampaignPrefix(entries, term) \in Seq(LogEntry)
            /\ Len(CampaignPrefix(entries, term)) = CampaignPrefixIndex(entries, term)
            /\ \A index \in DOMAIN CampaignPrefix(entries, term):
                    /\ index \in DOMAIN entries
                    /\ CampaignPrefix(entries, term)[index] = entries[index]
                    /\ CampaignPrefix(entries, term)[index].term < term
    BY PreTermIndexProperties, OrderedPreTermIndexes, SubSeqProperties,
       ElementOfSeq, LenProperties, SMT DEF CampaignPrefix, PreTermIndexes

LEMMA CampaignPrefixBeforeTerm ==
    \A entries \in Seq(LogEntry), term \in Nat:
        (\A index \in DOMAIN entries: entries[index].term < term)
        => CampaignPrefix(entries, term) = entries
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW term \in Nat,
                      \A index \in DOMAIN entries: entries[index].term < term
             PROVE CampaignPrefix(entries, term) = entries
    BY SMT
<1>indexes. PreTermIndexes(entries, term) = 1..Len(entries)
    BY LenProperties, SMT DEF PreTermIndexes
<1>bounds.
        /\ Len(entries) \in Nat
        /\ CampaignPrefixIndex(entries, term) \in 0..Len(entries)
        /\ \A index \in PreTermIndexes(entries, term):
                index <= CampaignPrefixIndex(entries, term)
    BY PreTermIndexProperties, LenProperties, SMT
<1>member. Len(entries) > 0 => Len(entries) \in PreTermIndexes(entries, term)
    BY <1>indexes, <1>bounds, SMT
<1>last. CampaignPrefixIndex(entries, term) = Len(entries)
    BY <1>bounds, <1>member, SMT
<1> QED BY <1>last, WholeSequencePrefix, SMT DEF CampaignPrefix

LEMMA PreTermIndexesOnCurrentTermAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        entry.term = term =>
            PreTermIndexes(Append(entries, entry), term) = PreTermIndexes(entries, term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                      NEW term \in Nat, entry.term = term
             PROVE PreTermIndexes(Append(entries, entry), term) =
                       PreTermIndexes(entries, term)
    BY SMT
<1>append.
        /\ DOMAIN entries = 1..Len(entries)
        /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
        /\ Len(entries) \in Nat
        /\ \A index \in DOMAIN entries:
                Append(entries, entry)[index] = entries[index]
        /\ Append(entries, entry)[Len(entries) + 1] = entry
    BY AppendProperties, LenProperties, SMT
<1> QED BY <1>append, SMT DEF PreTermIndexes

LEMMA CampaignPrefixOnCurrentTermAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        entry.term = term =>
            CampaignPrefix(Append(entries, entry), term) = CampaignPrefix(entries, term)
    BY PreTermIndexesOnCurrentTermAppend, PreTermIndexProperties,
       AppendPreservesSequencePrefix, SMT DEF CampaignPrefix, CampaignPrefixIndex

LEMMA ElectionConfigIndexesInCampaignPrefix ==
    \A entries \in Seq(LogEntry), term \in Nat:
        TermsOrdered(entries) =>
            ElectionConfigIndexes(entries, term) =
                ConfigChangeIndexes(CampaignPrefix(entries, term))
    BY OrderedPreTermIndexes, PreTermIndexProperties, ConfigurationIndexesOnPrefix,
       LenProperties, SMT
    DEF ElectionConfigIndexes, ConfigChangeIndexes, CampaignPrefix, PreTermIndexes

LEMMA ElectionConfigIsCampaignConfiguration ==
    \A entries \in Seq(LogEntry), term \in Nat:
        TermsOrdered(entries) =>
            ElectionConfig(entries, term) = ConfigOf(CampaignPrefix(entries, term))
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW term \in Nat,
                      TermsOrdered(entries)
             PROVE ElectionConfig(entries, term) = ConfigOf(CampaignPrefix(entries, term))
    BY SMT
<1>prefix.
        /\ CampaignPrefix(entries, term) \in Seq(LogEntry)
        /\ \A index \in DOMAIN CampaignPrefix(entries, term):
                CampaignPrefix(entries, term)[index] = entries[index]
    BY CampaignPrefixProperties, SMT
<1>indexes. ElectionConfigIndexes(entries, term) =
               ConfigChangeIndexes(CampaignPrefix(entries, term))
    BY SMT, ElectionConfigIndexesInCampaignPrefix
<1>last.
        /\ MaxOrZero(ElectionConfigIndexes(entries, term)) =
               LastConfigChangeIndex(CampaignPrefix(entries, term))
        /\ (LastConfigChangeIndex(CampaignPrefix(entries, term)) # 0 =>
               LastConfigChangeIndex(CampaignPrefix(entries, term))
                   \in DOMAIN CampaignPrefix(entries, term))
    BY <1>prefix, <1>indexes, ConfigurationIndexProperties, Zenon
    DEF LastConfigChangeIndex, ConfigChangeIndexes
<1> QED BY <1>prefix, <1>last, SMT DEF ElectionConfig, ConfigOf

LEMMA TimeoutCampaignSnapshot ==
    \A actor \in Server:
        /\ TypeOK /\ SendInvariant /\ LogTermBoundInv /\ Timeout(actor)
        => RecordedCampaignRequests(actor, currentTerm[actor])' =
               CampaignRequests(actor, currentTerm'[actor],
                   CampaignPrefix(log'[actor], currentTerm'[actor]))
<1> SUFFICES ASSUME NEW actor \in Server, TypeOK, SendInvariant,
                      LogTermBoundInv, Timeout(actor)
             PROVE RecordedCampaignRequests(actor, currentTerm[actor])' =
                       CampaignRequests(actor, currentTerm'[actor],
                           CampaignPrefix(log'[actor], currentTerm'[actor]))
    BY SMT
<1>types.
        /\ log[actor] \in Seq(LogEntry)
        /\ currentTerm[actor] \in Nat
        /\ currentTerm'[actor] = currentTerm[actor] + 1
        /\ log'[actor] = log[actor]
    BY SMT DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, Timeout
<1>old_terms. \A index \in DOMAIN log[actor]:
        log[actor][index].term < currentTerm'[actor]
    BY <1>types, ElementOfSeq, LenProperties, SMT DEF LogTermBoundInv, LogEntry
<1>snapshot. CampaignPrefix(log'[actor], currentTerm'[actor]) = log[actor]
    BY <1>types, <1>old_terms, CampaignPrefixBeforeTerm, SMT
<1>old_requests. RecordedCampaignRequests(actor, currentTerm'[actor]) = {}
    BY <1>types, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, SendInvariant, RecordedCampaignRequests
<1>new_requests. RecordedCampaignRequests(actor, currentTerm[actor])' =
        RequestVoteRequests(actor, currentTerm[actor] + 1)
    BY <1>types, <1>old_requests, SMT
    DEF RecordedCampaignRequests, Timeout, WithMessages, RequestVoteRequests
<1> QED BY <1>types, <1>snapshot, <1>new_requests, SMT
    DEF RequestVoteRequests, CampaignRequests, LastConfiguration

LEMMA ClientRequestPreservesCampaignPrefix ==
    \A server, actor \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(actor, payload) =>
            CampaignPrefix(log'[server], currentTerm'[server]) =
                CampaignPrefix(log[server], currentTerm[server])
    BY ClientRequestAppendsCurrentTerm, CampaignPrefixOnCurrentTermAppend, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, ClientRequest

LEMMA NewPositiveVoteResponseReceiveOrigin ==
    TypeOK /\ [Next]_vars =>
        \A response \in messages' \ messages:
            /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
            => \E request \in messages:
                   /\ request.mtype = RequestVoteRequest
                   /\ request.mterm = response.mterm
                   /\ request.msource = response.mdest
                   /\ request.mdest = response.msource
                   /\ HandleRequestVoteRequest(response.msource, response.mdest, request)
<1> SUFFICES ASSUME TypeOK, [Next]_vars,
                      NEW response \in messages' \ messages,
                      response.mtype = RequestVoteResponse, response.mvoteGranted
             PROVE \E request \in messages:
                       /\ request.mtype = RequestVoteRequest
                       /\ request.mterm = response.mterm
                       /\ request.msource = response.mdest
                       /\ request.mdest = response.msource
                       /\ HandleRequestVoteRequest(response.msource, response.mdest, request)
    BY SMT
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
    BY MessageTypesDistinct, SMT DEF Timeout, RequestVoteRequests, WithMessages
<1>append. \A actor, peer \in Server: ~AppendEntries(actor, peer)
    BY MessageTypesDistinct, SMT
    DEF AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages
<1>not_append. \A request \in messages:
        ~HandleAppendEntriesRequest(request.mdest, request.msource, request)
    BY MessageTypesDistinct, SMT
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>receive. PICK request \in messages: Receive(request)
    BY <1>changed, <1>other_actions, <1>timeout, <1>append, SMT DEF Next, vars
<1>handled.
        /\ request.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(request.mdest, request.msource, request)
    BY <1>receive, <1>not_append, MessageTypesDistinct, SMT
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteResponse,
        HandleAppendEntriesResponse
<1>types.
        /\ request.mterm \in Nat
        /\ request.msource \in Server /\ request.mdest \in Server
        /\ currentTerm[request.mdest] \in Nat
    BY <1>receive, MessageFieldsTypeOK, SMT DEF TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>fields.
        /\ request.mterm = response.mterm
        /\ request.msource = response.mdest
        /\ request.mdest = response.msource
    BY <1>receive, <1>handled, <1>types, SMT
    DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages
<1> QED BY <1>receive, <1>handled, <1>fields, SMT

LEMMA NewPositiveVoteResponseRequest ==
    TypeOK /\ [Next]_vars =>
        \A response \in messages' \ messages:
            /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
            => \E request \in messages:
                   /\ request.mtype = RequestVoteRequest
                   /\ request.mterm = response.mterm
                   /\ request.msource = response.mdest
                   /\ request.mdest = response.msource
    BY NewPositiveVoteResponseReceiveOrigin, SMT

LEMMA GrantedVotesRecordedInit == Init => GrantedVotesRecorded
    BY ServerStatesDistinct, SMT DEF GrantedVotesRecorded, Init, InitServerVars

LEMMA GrantedVotesRecordedNext ==
    ASSUME TypeOK, GrantedVotesRecorded, [Next]_vars
    PROVE GrantedVotesRecorded'
<1>messages. messages \subseteq messages' BY MessagesMonotonicNext, SMT
<1>stutter. CASE UNCHANGED vars
    BY <1>stutter, SMT DEF GrantedVotesRecorded, VoteFor, Grant, vars
<1>restart. CASE \E actor \in Server: Restart(actor)
    BY <1>restart, <1>messages, ServerStatesDistinct, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, Restart, TypeOK,
        ServerVarsTypeOK, CandidateVarsTypeOK
<1>timeout. CASE \E actor \in Server: Timeout(actor)
    BY <1>timeout, <1>messages, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, Timeout, TypeOK,
        ServerVarsTypeOK, CandidateVarsTypeOK
<1>leader. CASE \E actor \in Server: BecomeLeader(actor)
    BY <1>leader, <1>messages, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, BecomeLeader, TypeOK,
        ServerVarsTypeOK, CandidateVarsTypeOK
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>client, <1>messages, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, ClientRequest
<1>commit. CASE \E actor \in Server: AdvanceCommitIndex(actor)
    BY <1>commit, <1>messages, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, AdvanceCommitIndex
<1>append. CASE \E actor, peer \in Server: AppendEntries(actor, peer)
    BY <1>append, <1>messages, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, AppendEntries
<1>stepdown. CASE \E actor \in Server: LeaderStepDown(actor)
    BY <1>stepdown, <1>messages, ServerStatesDistinct, SMT
    DEF GrantedVotesRecorded, VoteFor, Grant, LeaderStepDown, TypeOK,
        ServerVarsTypeOK, CandidateVarsTypeOK
<1>receive. CASE \E message \in messages: Receive(message)
    <2>message. PICK message \in messages: Receive(message) BY <1>receive, SMT
    <2>update. CASE UpdateTerm(message.mdest, message.msource, message)
        BY <2>message, <2>update, <1>messages, MessageFieldsTypeOK,
           ServerStatesDistinct, SMT
        DEF GrantedVotesRecorded, VoteFor, Grant, UpdateTerm, TypeOK, MsgTypeOK,
            ServerVarsTypeOK, CandidateVarsTypeOK
    <2>vote_request. CASE /\ message.mtype = RequestVoteRequest
                         /\ HandleRequestVoteRequest(message.mdest, message.msource, message)
        BY <2>message, <2>vote_request, <1>messages, MessageFieldsTypeOK, SMT
        DEF GrantedVotesRecorded, VoteFor, Grant, HandleRequestVoteRequest,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, CandidateVarsTypeOK
    <2>vote_response. CASE /\ message.mtype = RequestVoteResponse
                          /\ HandleRequestVoteResponse(message.mdest, message.msource, message)
        BY <2>message, <2>vote_response, <1>messages, MessageFieldsTypeOK, SMTT(20)
        DEF GrantedVotesRecorded, VoteFor, Grant, HandleRequestVoteResponse,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, CandidateVarsTypeOK
    <2>append_request. CASE /\ message.mtype = AppendEntriesRequest
                           /\ HandleAppendEntriesRequest(message.mdest, message.msource, message)
        BY <2>message, <2>append_request, <1>messages, MessageFieldsTypeOK, SMT
        DEF GrantedVotesRecorded, VoteFor, Grant, HandleAppendEntriesRequest,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, CandidateVarsTypeOK
    <2>append_response. CASE /\ message.mtype = AppendEntriesResponse
                            /\ HandleAppendEntriesResponse(message.mdest, message.msource, message)
        BY <2>message, <2>append_response, <1>messages, MessageFieldsTypeOK, SMT
        DEF GrantedVotesRecorded, VoteFor, Grant, HandleAppendEntriesResponse,
            TypeOK, MsgTypeOK, ServerVarsTypeOK, CandidateVarsTypeOK
    <2> QED BY <2>message, <2>update, <2>vote_request, <2>vote_response,
        <2>append_request, <2>append_response, SMT DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader, <1>client,
    <1>commit, <1>append, <1>stepdown, <1>receive, SMT DEF Next

LEMMA TimeoutActorsAreUnique ==
    ASSUME TypeOK, NEW left \in Server, NEW right \in Server, Timeout(left), Timeout(right)
    PROVE left = right
    BY SMT DEF Timeout, TypeOK, ServerVarsTypeOK

LEMMA ClientAppendActorsAreUnique ==
    ASSUME TypeOK, NEW left \in Server, NEW right \in Server,
           NEW first \in ClientPayload, NEW second \in ClientPayload,
           ClientRequest(left, first), ClientRequest(right, second)
    PROVE left = right
<1>append. PICK entry \in LogEntry: log'[left] = Append(log[left], entry)
    BY ClientRequestAppendsCurrentTerm, SMT
<1>length. Len(log'[left]) = Len(log[left]) + 1 /\ Len(log[left]) \in Nat
    BY <1>append, AppendProperties, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>length, SMT DEF ClientRequest, TypeOK, LogVarsTypeOK

LEMMA UnchangedTermsExcludeTimeout ==
    ASSUME TypeOK, UNCHANGED currentTerm
    PROVE ~\E candidate \in Server: Timeout(candidate)
    BY SMT DEF Timeout, TypeOK, ServerVarsTypeOK

LEMMA UnchangedLogsExcludeClientAppend ==
    ASSUME TypeOK, UNCHANGED log
    PROVE ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
<1> SUFFICES ASSUME NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload)
             PROVE FALSE BY SMT
<1>length. Len(log'[actor]) = Len(log[actor]) + 1 /\ Len(log[actor]) \in Nat
    BY ClientRequestAppendsCurrentTerm, AppendProperties, LenProperties, SMT DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>length, SMT

LEMMA ActiveCampaignRoleWithoutTermChange ==
    ASSUME TypeOK, [Next]_vars, NEW candidate \in Server,
           state'[candidate] \in {Candidate, Leader}, currentTerm'[candidate] = currentTerm[candidate]
    PROVE state[candidate] \in {Candidate, Leader}
<1>unchanged. UNCHANGED state => state[candidate] \in {Candidate, Leader} BY SMT
<1>timeout. \A actor \in Server:
        Timeout(actor) => state[candidate] \in {Candidate, Leader}
    BY SMT DEF Timeout, TypeOK, ServerVarsTypeOK
<1>leader. \A actor \in Server:
        BecomeLeader(actor) => state[candidate] \in {Candidate, Leader}
    BY SMT DEF BecomeLeader, TypeOK, ServerVarsTypeOK
<1>retirement. \A actor \in Server:
        Restart(actor) \/ LeaderStepDown(actor) => state[candidate] \in {Candidate, Leader}
    BY ServerStatesDistinct, SMT
    DEF Restart, LeaderStepDown, TypeOK, ServerVarsTypeOK
<1>update. \A message \in messages:
        UpdateTerm(message.mdest, message.msource, message) =>
            state[candidate] \in {Candidate, Leader}
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
    DEF UpdateTerm, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>append_request. \A message \in messages:
        HandleAppendEntriesRequest(message.mdest, message.msource, message) =>
            state[candidate] \in {Candidate, Leader}
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
    DEF HandleAppendEntriesRequest, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>frames.
        /\ \A actor \in Server, payload \in ClientPayload:
               ClientRequest(actor, payload) => UNCHANGED state
        /\ \A actor \in Server: AdvanceCommitIndex(actor) => UNCHANGED state
        /\ \A actor, peer \in Server: AppendEntries(actor, peer) => UNCHANGED state
        /\ \A message \in messages:
               HandleRequestVoteRequest(message.mdest, message.msource, message)
                   \/ HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED state
    BY Zenon
    DEF ClientRequest, AdvanceCommitIndex, AppendEntries, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>timeout, <1>leader, <1>retirement, <1>update,
    <1>append_request, <1>frames, SMT DEF Next, vars, Receive, HandleMsg

LEMMA ActiveCampaignChangesTermOnlyOnTimeout ==
    ASSUME TypeOK, [Next]_vars, NEW candidate \in Server,
           state'[candidate] \in {Candidate, Leader}, currentTerm'[candidate] # currentTerm[candidate]
    PROVE Timeout(candidate)
    BY ServerStatesDistinct, StoredMessageFieldsTypeOK, SMT
    DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        TypeOK, ServerVarsTypeOK

LEMMA ActiveCampaignKeepsLogWithoutClientAppend ==
    ASSUME TypeOK, [Next]_vars, NEW actor \in Server,
           state'[actor] \in {Candidate, Leader}, currentTerm'[actor] = currentTerm[actor],
           ~(\E leader \in Server, payload \in ClientPayload: ClientRequest(leader, payload))
    PROVE log'[actor] = log[actor]
<1>unchanged. UNCHANGED log => log'[actor] = log[actor] BY SMT
<1>append_request. \A message \in messages:
        HandleAppendEntriesRequest(message.mdest, message.msource, message)
            => log'[actor] = log[actor]
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMTT(20)
    DEF HandleAppendEntriesRequest, TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>frames.
        /\ \A server \in Server:
               Restart(server) \/ Timeout(server) \/ BecomeLeader(server)
                   \/ AdvanceCommitIndex(server) \/ LeaderStepDown(server)
                   => UNCHANGED log
        /\ \A sender, recipient \in Server:
               AppendEntries(sender, recipient) => UNCHANGED log
        /\ \A message \in messages:
               UpdateTerm(message.mdest, message.msource, message)
                   \/ HandleRequestVoteRequest(message.mdest, message.msource, message)
                   \/ HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED log
    BY Zenon
    DEF Restart, Timeout, BecomeLeader, AdvanceCommitIndex, LeaderStepDown,
        AppendEntries, UpdateTerm, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>append_request, <1>frames, SMT
    DEF Next, vars, Receive, HandleMsg

LEMMA ActiveCampaignKeepsSnapshotWithoutTermChange ==
    ASSUME TypeOK, [Next]_vars, NEW candidate \in Server,
           state'[candidate] \in {Candidate, Leader}, currentTerm'[candidate] = currentTerm[candidate]
    PROVE /\ state[candidate] \in {Candidate, Leader}
          /\ CampaignPrefix(log'[candidate], currentTerm'[candidate]) = CampaignPrefix(log[candidate], currentTerm[candidate])
<1>role. state[candidate] \in {Candidate, Leader}
    BY ActiveCampaignRoleWithoutTermChange, SMT
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>role, <1>client, ClientRequestPreservesCampaignPrefix, SMT
<1>other. CASE ~\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>log. log'[candidate] = log[candidate]
        BY <1>other, ActiveCampaignKeepsLogWithoutClientAppend, SMT
    <2> QED BY <1>role, <2>log, SMT
<1> QED BY <1>client, <1>other, SMT

LEMMA SameTermSelfVoteIsPermanent ==
    ASSUME TypeOK, [Next]_vars, NEW candidate \in Server,
           currentTerm'[candidate] = currentTerm[candidate], votedFor[candidate] = candidate
    PROVE votedFor'[candidate] = candidate
<1>unchanged. UNCHANGED votedFor => votedFor'[candidate] = candidate BY SMT
<1>timeout. \A actor \in Server:
        Timeout(actor) => votedFor'[candidate] = candidate
    BY SMT DEF Timeout, TypeOK, ServerVarsTypeOK
<1>update. \A message \in messages:
        UpdateTerm(message.mdest, message.msource, message)
            => votedFor'[candidate] = candidate
    BY MessageFieldsTypeOK, SMT
    DEF UpdateTerm, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>request. \A message \in messages:
        HandleRequestVoteRequest(message.mdest, message.msource, message)
            => votedFor'[candidate] = candidate
    BY MessageFieldsTypeOK, NilNotServer, SMT
    DEF HandleRequestVoteRequest, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>frames.
        /\ \A actor \in Server:
               Restart(actor) \/ BecomeLeader(actor)
                   \/ AdvanceCommitIndex(actor) \/ LeaderStepDown(actor)
                   => UNCHANGED votedFor
        /\ \A actor \in Server, payload \in ClientPayload:
               ClientRequest(actor, payload) => UNCHANGED votedFor
        /\ \A actor, peer \in Server:
               AppendEntries(actor, peer) => UNCHANGED votedFor
        /\ \A message \in messages:
               HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesRequest(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED votedFor
    BY Zenon
    DEF Restart, BecomeLeader, AdvanceCommitIndex, LeaderStepDown, ClientRequest,
        AppendEntries, HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>timeout, <1>update, <1>request, <1>frames, SMT
    DEF Next, vars, Receive, HandleMsg

LEMMA HistoricalSelfVoteExcludesNewConflictingGrants ==
    ASSUME TypeOK, [Next]_vars, NEW record, CampaignHistoryRecord(record)
    PROVE \A response \in messages':
              /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
              /\ response.msource = record.candidate /\ response.mterm = record.term
              => response.mdest = record.candidate
<1> SUFFICES ASSUME NEW response \in messages',
                      response.mtype = RequestVoteResponse, response.mvoteGranted,
                      response.msource = record.candidate, response.mterm = record.term
             PROVE response.mdest = record.candidate
    BY SMT
<1>old. CASE response \in messages
    BY <1>old, SMT DEF CampaignHistoryRecord
<1>new. CASE response \notin messages
    <2>request. PICK request \in messages:
            /\ request.mtype = RequestVoteRequest
            /\ request.mterm = response.mterm
            /\ request.msource = response.mdest
            /\ request.mdest = response.msource
            /\ HandleRequestVoteRequest(response.msource, response.mdest, request)
        BY <1>new, NewPositiveVoteResponseReceiveOrigin, SMT
    <2>types.
            /\ request.msource \in Server /\ request.mdest \in Server
            /\ request.mterm \in Nat /\ record.candidate \in Server
            /\ record.term \in Nat /\ currentTerm[record.candidate] \in Nat
        BY <2>request, MessageFieldsTypeOK, SMT
        DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, CampaignHistoryRecord
    <2>grant.
            /\ currentTerm[record.candidate] = record.term
            /\ votedFor[record.candidate] \in {Nil, response.mdest}
        BY <1>new, <2>request, <2>types, SMT
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages
    <2>self. votedFor[record.candidate] = record.candidate
        BY <2>grant, SMT DEF CampaignHistoryRecord
    <2> QED BY <2>types, <2>grant, <2>self, NilNotServer, SMT
<1> QED BY <1>old, <1>new, SMT

LEMMA HistoricalCampaignRequestsAreFixed ==
    ASSUME TypeOK, SendInvariant, [Next]_vars, NEW candidate \in Server, NEW term \in Nat,
           term <= currentTerm[candidate]
    PROVE RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
<1>unchanged. UNCHANGED messages =>
        RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY SMT DEF RecordedCampaignRequests
<1>timeout. \A actor \in Server:
        Timeout(actor) =>
            RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY SMT
    DEF RecordedCampaignRequests, Timeout, RequestVoteRequests, WithMessages,
        TypeOK, ServerVarsTypeOK
<1>append. \A actor, peer \in Server:
        AppendEntries(actor, peer) =>
            RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY MessageTypesDistinct, SMT
    DEF RecordedCampaignRequests, AppendEntries, AppendEntriesMessage,
        Send, WithMessage, WithMessages
<1>vote_request. \A message \in messages:
        HandleRequestVoteRequest(message.mdest, message.msource, message) =>
            RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY MessageTypesDistinct, SMT
    DEF RecordedCampaignRequests, HandleRequestVoteRequest, Send, WithMessage, WithMessages
<1>append_request. \A message \in messages:
        HandleAppendEntriesRequest(message.mdest, message.msource, message) =>
            RecordedCampaignRequests(candidate, term)' = RecordedCampaignRequests(candidate, term)
    BY MessageTypesDistinct, SMT
    DEF RecordedCampaignRequests, HandleAppendEntriesRequest, Send, WithMessage, WithMessages
<1>frames.
        /\ \A actor \in Server:
               Restart(actor) \/ BecomeLeader(actor)
                   \/ AdvanceCommitIndex(actor) \/ LeaderStepDown(actor)
                   => UNCHANGED messages
        /\ \A actor \in Server, payload \in ClientPayload:
               ClientRequest(actor, payload) => UNCHANGED messages
        /\ \A message \in messages:
               UpdateTerm(message.mdest, message.msource, message)
                   \/ HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED messages
    BY Zenon
    DEF Restart, BecomeLeader, AdvanceCommitIndex, LeaderStepDown, ClientRequest,
        UpdateTerm, HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>timeout, <1>append, <1>vote_request,
    <1>append_request, <1>frames, SMT DEF Next, vars, Receive, HandleMsg

LEMMA CampaignHistoryRecordNext ==
    ASSUME TypeOK, SendInvariant, [Next]_vars, NEW record, CampaignHistoryRecord(record)
    PROVE CampaignHistoryRecord(record)'
<1>types. currentTerm[record.candidate] \in Nat /\ currentTerm'[record.candidate] \in Nat
    BY ServerVarsTypeOKNext, SMT DEF CampaignHistoryRecord, TypeOK, ServerVarsTypeOK
<1>bound. record.term <= currentTerm'[record.candidate]
    BY <1>types, CurrentTermsMonotonicNext, SMT DEF CampaignHistoryRecord
<1>same. record.term = currentTerm'[record.candidate] => record.term = currentTerm[record.candidate]
    BY <1>types, CurrentTermsMonotonicNext, SMT DEF CampaignHistoryRecord
<1>vote. record.term = currentTerm'[record.candidate] => votedFor'[record.candidate] = record.candidate
    BY <1>same, SameTermSelfVoteIsPermanent, SMT DEF CampaignHistoryRecord
<1>snapshot. record.term = currentTerm'[record.candidate] /\ state'[record.candidate] \in {Candidate, Leader}
          => record.snapshot = CampaignPrefix(log'[record.candidate], record.term)
    BY <1>same, ActiveCampaignKeepsSnapshotWithoutTermChange, SMT DEF CampaignHistoryRecord
<1>grants. \A response \in messages':
        /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
        /\ response.msource = record.candidate /\ response.mterm = record.term
        => response.mdest = record.candidate
    BY HistoricalSelfVoteExcludesNewConflictingGrants, SMT
<1>requests. RecordedCampaignRequests(record.candidate, record.term)' = CampaignRequests(record.candidate, record.term, record.snapshot)
    BY HistoricalCampaignRequestsAreFixed, SMT DEF CampaignHistoryRecord
<1> QED BY <1>bound, <1>vote, <1>snapshot, <1>grants, <1>requests, MessagesMonotonicNext, SMT
    DEF CampaignHistoryRecord, VoteFor, Grant

LEMMA TimeoutCapturesCampaignHistoryRecord ==
    ASSUME TypeOK, SendInvariant, LogTermBoundInv, NEW candidate \in Server, Timeout(candidate),
           NEW snapshot \in Seq(LogEntry), snapshot = log[candidate], NEW term \in Nat, term = currentTerm[candidate] + 1
    PROVE CampaignHistoryRecord([candidate |-> candidate, term |-> term, snapshot |-> snapshot])'
<1> DEFINE fresh == [candidate |-> candidate, term |-> term, snapshot |-> snapshot]
<1>types. log[candidate] \in Seq(LogEntry) /\ currentTerm[candidate] \in Nat
    BY SMT DEF TypeOK, LogVarsTypeOK, ServerVarsTypeOK
<1>old_terms. \A index \in DOMAIN log[candidate]: log[candidate][index].term < currentTerm[candidate] + 1
    BY <1>types, ElementOfSeq, SMT DEF LogTermBoundInv, LogEntry
<1>snapshot. CampaignPrefix(log'[candidate], currentTerm[candidate] + 1) = log[candidate]
    BY <1>types, <1>old_terms, CampaignPrefixBeforeTerm, SMT DEF Timeout
<1>grants. \A response \in messages':
        /\ response.mtype = RequestVoteResponse /\ response.mvoteGranted
        /\ response.msource = candidate /\ response.mterm = currentTerm[candidate] + 1
        => response.mdest = candidate
    BY <1>types, MessageTypesDistinct, SMT
    DEF SendInvariant, Timeout, RequestVoteRequests, WithMessages
<1>requests. RecordedCampaignRequests(candidate, term)' = CampaignRequests(candidate, term, snapshot)
    BY <1>types, <1>snapshot, TimeoutCampaignSnapshot, SMT DEF Timeout, TypeOK, ServerVarsTypeOK
<1> QED BY <1>types, <1>old_terms, <1>snapshot, <1>grants, <1>requests, SMT
    DEF fresh, CampaignHistoryRecord, Timeout, TypeOK, ServerVarsTypeOK

LEMMA CampaignHistoryWithoutTimeoutNext ==
    ASSUME TypeOK, SendInvariant, LogTermBoundInv, [Next]_vars, NEW history, CampaignHistory(history),
           ~(\E candidate \in Server: Timeout(candidate)),
           ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    PROVE CampaignHistory(history)'
<1>records. \A record \in history: CampaignHistoryRecord(record)'
    BY CampaignHistoryRecordNext, SMT DEF CampaignHistory
<1>coverage. \A candidate \in Server: state'[candidate] \in {Candidate, Leader} =>
        \E record \in history:
            /\ record.candidate = candidate /\ record.term = currentTerm'[candidate]
            /\ record.snapshot = CampaignPrefix(log'[candidate], currentTerm'[candidate])
    BY ActiveCampaignChangesTermOnlyOnTimeout, ActiveCampaignKeepsSnapshotWithoutTermChange, SMT
    DEF CampaignHistory
<1>local. LocalAppendCoverage(history)'
    <2> SUFFICES ASSUME NEW actor \in Server, state'[actor] \in {Candidate, Leader},
                          NEW index \in DOMAIN log'[actor], log'[actor][index].term = currentTerm'[actor]
                 PROVE LocalAppendOrigin(history, actor, currentTerm'[actor], log'[actor])
        BY SMT DEF LocalAppendCoverage
    <2>term. currentTerm'[actor] = currentTerm[actor]
        BY ActiveCampaignChangesTermOnlyOnTimeout, SMT
    <2>log. log'[actor] = log[actor]
        BY <2>term, ActiveCampaignKeepsLogWithoutClientAppend, SMT
    <2>active. state[actor] \in {Candidate, Leader}
        BY <2>term, ActiveCampaignKeepsSnapshotWithoutTermChange, SMT
    <2> QED BY <2>term, <2>log, <2>active, SMT
        DEF CampaignHistory, LocalAppendCoverage, LocalAppendOrigin
<1> QED BY <1>records, <1>coverage, <1>local, MembershipElectionBaseNext, GrantedVotesRecordedNext, TermOrderingInvNext, SMT DEF CampaignHistory, OrderingBase

------------------------------------------------------------------------

LEMMA ContinuingLeaderCampaignPrefix ==
    \A server \in Server:
        /\ TypeOK /\ [Next]_vars
        /\ state[server] = Leader /\ state'[server] = Leader
        => CampaignPrefix(log'[server], currentTerm'[server]) =
               CampaignPrefix(log[server], currentTerm[server])
    BY ClientRequestPreservesCampaignPrefix,
       ContinuingLeaderFrameExceptClientRequest, SMT DEF Next

LEMMA CampaignSnapshotInvNext ==
    /\ TypeOK /\ SendInvariant /\ LogTermBoundInv /\ CampaignSnapshotInv
    /\ [Next]_vars
    => CampaignSnapshotInv'
<1>timeout. \A actor \in Server:
        /\ TypeOK /\ SendInvariant /\ LogTermBoundInv /\ CampaignSnapshotInv
        /\ Timeout(actor)
        => CampaignSnapshotInv'
    <2> SUFFICES ASSUME NEW actor \in Server, TypeOK, SendInvariant,
                          LogTermBoundInv, CampaignSnapshotInv, Timeout(actor),
                          NEW candidate \in Server,
                          state'[candidate] \in {Candidate, Leader}
                 PROVE RecordedCampaignRequests(candidate, currentTerm[candidate])' =
                           CampaignRequests(candidate, currentTerm'[candidate],
                               CampaignPrefix(log'[candidate], currentTerm'[candidate]))
        BY SMT DEF CampaignSnapshotInv
    <2>same. CASE candidate = actor
        BY <2>same, TimeoutCampaignSnapshot, SMT
    <2>other. CASE candidate # actor
        BY <2>other, SMT
        DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, CampaignSnapshotInv,
            Timeout, WithMessages, RequestVoteRequests, RecordedCampaignRequests
    <2> QED BY <2>same, <2>other, SMT
<1>client. \A actor \in Server, payload \in ClientPayload:
        TypeOK /\ CampaignSnapshotInv /\ ClientRequest(actor, payload)
        => CampaignSnapshotInv'
    BY ClientRequestPreservesCampaignPrefix, SMT
    DEF CampaignSnapshotInv, RecordedCampaignRequests, ClientRequest
<1>others.
        /\ TypeOK /\ CampaignSnapshotInv
        /\ \/ UNCHANGED vars
           \/ \E actor \in Server: Restart(actor)
           \/ \E actor \in Server: BecomeLeader(actor)
           \/ \E actor \in Server: AdvanceCommitIndex(actor)
           \/ \E actor, peer \in Server: AppendEntries(actor, peer)
           \/ \E actor \in Server: LeaderStepDown(actor)
           \/ \E message \in messages: Receive(message)
        => CampaignSnapshotInv'
    BY ServerStatesDistinct, MessageTypesDistinct, MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK,
        CampaignSnapshotInv, RecordedCampaignRequests, vars, Restart,
        BecomeLeader, AdvanceCommitIndex, AppendEntries, AppendEntriesMessage,
        LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages
<1> QED BY <1>timeout, <1>client, <1>others, SMT DEF Next

LEMMA PositiveVoteResponseRequestInvNext ==
    TypeOK /\ PositiveVoteResponseRequestInv /\ [Next]_vars
    => PositiveVoteResponseRequestInv'
    BY NewPositiveVoteResponseRequest, MessagesMonotonicNext, SMT
    DEF PositiveVoteResponseRequestInv

LEMMA PositivePeerGrantHasCampaignRequest ==
    ASSUME CampaignSnapshotInv, PositiveVoteResponseRequestInv,
           NEW candidate \in Server, NEW voter \in Server,
           state[candidate] \in {Candidate, Leader},
           Grant(voter, candidate, currentTerm[candidate])
    PROVE \E request \in CampaignRequests(candidate, currentTerm[candidate],
                          CampaignPrefix(log[candidate], currentTerm[candidate])):
              /\ request \in messages
              /\ request.mdest = voter
    BY SMT DEF CampaignSnapshotInv, PositiveVoteResponseRequestInv,
        RecordedCampaignRequests, Grant

LEMMA LocalAppendOriginIsMonotone ==
    ASSUME NEW history, NEW larger, history \subseteq larger,
           NEW leader, NEW term, NEW entries, LocalAppendOrigin(history, leader, term, entries)
    PROVE LocalAppendOrigin(larger, leader, term, entries)
    BY SMT DEF LocalAppendOrigin

LEMMA CampaignHistoryInit == Init => CampaignHistory({})
    BY MembershipElectionBaseInit, GrantedVotesRecordedInit, TermOrderingInvInit, ServerStatesDistinct, FS_EmptySet, SMT
    DEF CampaignHistory, LocalAppendCoverage, Init, InitServerVars

LEMMA CampaignHistoryNext ==
    ASSUME TypeOK, SendInvariant, LogTermBoundInv, [Next]_vars,
           NEW history, CampaignHistory(history)
    PROVE \E larger:
              /\ history \subseteq larger /\ CampaignHistory(larger)'
              /\ CampaignHistoryStep(history, larger)
<1>state_base. MembershipElectionBase' /\ GrantedVotesRecorded' /\ TermOrderingInv'
    BY MembershipElectionBaseNext, GrantedVotesRecordedNext, TermOrderingInvNext, SMT DEF CampaignHistory, OrderingBase
<1>records. \A record \in history: CampaignHistoryRecord(record)'
    BY CampaignHistoryRecordNext, SMT DEF CampaignHistory
<1>timeout. CASE \E candidate \in Server: Timeout(candidate)
    <2>actor. PICK candidate \in Server: Timeout(candidate) BY <1>timeout, SMT
    <2>frozen. PICK snapshot \in Seq(LogEntry): snapshot = log[candidate]
        BY SMT DEF TypeOK, LogVarsTypeOK
    <2>term. PICK term \in Nat: term = currentTerm[candidate] + 1
        BY SMT DEF TypeOK, ServerVarsTypeOK
    <2> DEFINE fresh == [candidate |-> candidate, term |-> term, snapshot |-> snapshot]
    <2>fresh. CampaignHistoryRecord(fresh)'
        BY <2>actor, <2>frozen, <2>term, TimeoutCapturesCampaignHistoryRecord, SMT DEF fresh
    <2>unique. \A record \in history: record.candidate = candidate => record.term < term
        BY <2>term, SMT DEF CampaignHistory, CampaignHistoryRecord, TypeOK, ServerVarsTypeOK
    <2>coverage. \A actor \in Server: state'[actor] \in {Candidate, Leader} =>
            \E record \in history \cup {fresh}:
                /\ record.candidate = actor /\ record.term = currentTerm'[actor]
                /\ record.snapshot = CampaignPrefix(log'[actor], currentTerm'[actor])
        BY <2>actor, <2>frozen, <2>term, <2>fresh, SMT
        DEF CampaignHistory, CampaignHistoryRecord, fresh, Timeout, TypeOK, ServerVarsTypeOK
    <2>local. LocalAppendCoverage(history \cup {fresh})'
        <3> SUFFICES ASSUME NEW actor \in Server, state'[actor] \in {Candidate, Leader},
                              NEW index \in DOMAIN log'[actor], log'[actor][index].term = currentTerm'[actor]
                     PROVE LocalAppendOrigin(history \cup {fresh}, actor, currentTerm'[actor], log'[actor])
            BY SMT DEF LocalAppendCoverage
        <3>same. CASE actor = candidate
            BY <3>same, <2>actor, SMT
            DEF LogTermBoundInv, Timeout, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
        <3>other. CASE actor # candidate
            BY <3>other, <2>actor, SMT
            DEF CampaignHistory, LocalAppendCoverage, LocalAppendOrigin, Timeout,
                TypeOK, ServerVarsTypeOK, LogVarsTypeOK
        <3> QED BY <3>same, <3>other, SMT
    <2>result. CampaignHistory(history \cup {fresh})'
        BY <1>state_base, <1>records, <2>fresh, <2>unique, <2>coverage, <2>local, FS_AddElement, SMT
        DEF CampaignHistory, fresh
    <2>step. CampaignHistoryStep(history, history \cup {fresh})
        BY <2>actor, <2>frozen, <2>term, TimeoutActorsAreUnique, SMT
        DEF CampaignHistoryStep, fresh, Timeout, ClientRequest, TypeOK, ServerVarsTypeOK
    <2> QED BY <2>result, <2>step, SMT
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>client, SMT
    <2>old. PICK old \in history:
            /\ old.candidate = actor /\ old.term = currentTerm[actor]
            /\ old.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
        BY <2>actor, SMT DEF CampaignHistory, ClientRequest
    <2>frozen. PICK fresh:
        fresh = [candidate |-> actor, term |-> currentTerm[actor],
                 snapshot |-> CampaignPrefix(log[actor], currentTerm[actor]), prefix |-> log'[actor],
                 support |-> CapturedElectionSupport(actor)]
        BY SMT
    <2>support_exists. \E support \in Quorums(ConfigOf(CampaignPrefix(log[actor], currentTerm[actor]))):
        support \subseteq votesGranted[actor]
        BY <2>actor, <2>old, ElectionConfigIsCampaignConfiguration, SMT
        DEF CampaignHistory, MembershipElectionBase, LeaderQuorumInv, ClientRequest, TermOrderingInv, LogTermsMonotonic, TermsOrdered, TypeOK, LogVarsTypeOK, ServerVarsTypeOK
    <2>support. fresh.support \in Quorums(ConfigOf(fresh.snapshot))
        /\ \A voter \in fresh.support: VoteFor(voter, fresh.candidate, fresh.term)'
        BY <2>actor, <2>frozen, <2>support_exists, SMT
        DEF CampaignHistory, GrantedVotesRecorded, ClientRequest, VoteFor, Grant, CapturedElectionSupport
    <2>fresh. CampaignHistoryRecord(fresh)'
        BY <1>records, <2>old, <2>frozen, <2>support, SMT DEF CampaignHistoryRecord
    <2>no_timeout. ~\E candidate \in Server: Timeout(candidate)
        BY <2>actor, UnchangedTermsExcludeTimeout, SMT DEF ClientRequest
    <2>coverage. \A candidate \in Server: state'[candidate] \in {Candidate, Leader} =>
        \E record \in history:
            /\ record.candidate = candidate /\ record.term = currentTerm'[candidate]
            /\ record.snapshot = CampaignPrefix(log'[candidate], currentTerm'[candidate])
        BY <2>actor, ActiveCampaignKeepsSnapshotWithoutTermChange, SMT
        DEF CampaignHistory, ClientRequest
    <2>local. LocalAppendCoverage(history \cup {fresh})'
        BY <2>actor, <2>frozen, ClientRequestLogTypeOK, WholeSequencePrefix, LenProperties, SMT
        DEF CampaignHistory, LocalAppendCoverage, LocalAppendOrigin, LocalAppendRecord,
            ClientRequest, TypeOK, LogVarsTypeOK, IsPrefix
    <2>result. CampaignHistory(history \cup {fresh})'
        BY <1>state_base, <1>records, <2>old, <2>frozen, <2>fresh, <2>coverage, <2>local, FS_AddElement, SMT
        DEF CampaignHistory
    <2>step. CampaignHistoryStep(history, history \cup {fresh})
        <3>actors. \A other \in Server: \A value \in ClientPayload:
            ClientRequest(other, value) => other = actor
            BY <2>actor, ClientAppendActorsAreUnique, SMT
        <3> QED BY <2>actor, <2>frozen, <2>no_timeout, <3>actors, SMT
            DEF CampaignHistoryStep
    <2> QED BY <2>result, <2>step, SMT
<1>other. CASE /\ ~(\E candidate \in Server: Timeout(candidate))
               /\ ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    <2>result. CampaignHistory(history)'
        BY <1>other, CampaignHistoryWithoutTimeoutNext, SMT
    <2>step. CampaignHistoryStep(history, history)
        BY <1>other, SMT DEF CampaignHistoryStep
    <2> QED BY <2>result, <2>step, SMT
<1> QED BY <1>timeout, <1>client, <1>other, SMT

LEMMA LocalAppendOriginsFrameWithoutClient ==
    ASSUME NEW history, NEW larger, CampaignHistoryContextStep(history, larger),
           ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)),
           NEW leader, NEW term, NEW entries
    PROVE LocalAppendOrigin(larger, leader, term, entries) <=> LocalAppendOrigin(history, leader, term, entries)
    BY SMT DEF CampaignHistoryContextStep, CampaignHistoryStep, LocalAppendOrigin, LocalAppendRecord

LEMMA UnchangedLogsAndTermsKeepSelectedHistory ==
    ASSUME TypeOK, NEW history, NEW larger, CampaignHistoryContextStep(history, larger),
           UNCHANGED <<log, currentTerm>>
    PROVE larger = history
    BY UnchangedLogsExcludeClientAppend, UnchangedTermsExcludeTimeout, SMT
    DEF CampaignHistoryContextStep, CampaignHistoryStep

LEMMA ClientAppendHasRecordedOrigin ==
    ASSUME TypeOK, NEW history, NEW larger, CampaignHistoryStep(history, larger),
           NEW actor \in Server, NEW payload \in ClientPayload, ClientRequest(actor, payload),
           NEW entries \in Seq(LogEntry), entries = log'[actor],
           NEW term \in Nat, term = currentTerm[actor]
    PROVE LocalAppendOrigin(larger, actor, term, entries)
    BY WholeSequencePrefix, LenProperties, SMT
    DEF CampaignHistoryStep, LocalAppendOrigin, LocalAppendRecord, IsPrefix

LEMMA HistorySnapshotIsUnique ==
    ASSUME NEW history, CampaignHistory(history), NEW candidate \in Server, NEW term \in Nat,
           NEW left, NEW right, HistoryCampaignSnapshot(history, candidate, term, left),
           HistoryCampaignSnapshot(history, candidate, term, right)
    PROVE left = right
    BY SMT DEF CampaignHistory, HistoryCampaignSnapshot

LEMMA VoteGrantCoreInit == Init => VoteGrantCore
    BY SMT DEF VoteGrantCore, VoteCurrentInv, VoteUniqueInv, Grant, Init

LEMMA VoteCurrentRecordsNext ==
    ASSUME TypeOK, SendInvariant, VoteCurrentInv, [Next]_vars
    PROVE VoteCurrentInv'
<1>stutter. CASE UNCHANGED vars
    BY <1>stutter, SMT DEF VoteCurrentInv, Grant, vars
<1>restart. CASE \E actor \in Server: Restart(actor)
    BY <1>restart, SMT DEF VoteCurrentInv, Grant, Restart
<1>timeout. CASE \E actor \in Server: Timeout(actor)
    BY <1>timeout, MessageTypesDistinct, MessageFieldsTypeOK, SMTT(20)
    DEF VoteCurrentInv, Grant, Timeout, RequestVoteRequests, WithMessages,
        TypeOK, MsgTypeOK, ServerVarsTypeOK, SendInvariant
<1>leader. CASE \E actor \in Server: BecomeLeader(actor)
    BY <1>leader, SMT DEF VoteCurrentInv, Grant, BecomeLeader
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>client, SMT DEF VoteCurrentInv, Grant, ClientRequest
<1>commit. CASE \E actor \in Server: AdvanceCommitIndex(actor)
    BY <1>commit, SMT DEF VoteCurrentInv, Grant, AdvanceCommitIndex
<1>append. CASE \E actor, peer \in Server: AppendEntries(actor, peer)
    BY <1>append, MessageTypesDistinct, SMT
    DEF VoteCurrentInv, Grant, AppendEntries, AppendEntriesMessage,
        Send, WithMessage, WithMessages
<1>stepdown. CASE \E actor \in Server: LeaderStepDown(actor)
    BY <1>stepdown, SMT DEF VoteCurrentInv, Grant, LeaderStepDown
<1>receive. CASE \E message \in messages: Receive(message)
    <2>message. PICK message \in messages: Receive(message) BY <1>receive, SMT
    <2>update. CASE UpdateTerm(message.mdest, message.msource, message)
        BY <2>message, <2>update, MessageFieldsTypeOK, SMTT(20)
        DEF VoteCurrentInv, Grant, UpdateTerm, TypeOK, MsgTypeOK,
            ServerVarsTypeOK, SendInvariant
    <2>vote_request. CASE /\ message.mtype = RequestVoteRequest
                         /\ HandleRequestVoteRequest(message.mdest, message.msource, message)
        BY <2>message, <2>vote_request, MessageFieldsTypeOK,
           MessageTypesDistinct, NilNotServer, SMTT(20)
        DEF VoteCurrentInv, Grant, HandleRequestVoteRequest, Send,
            WithMessage, WithMessages, TypeOK, MsgTypeOK, ServerVarsTypeOK
    <2>vote_response. CASE /\ message.mtype = RequestVoteResponse
                          /\ HandleRequestVoteResponse(message.mdest, message.msource, message)
        BY <2>message, <2>vote_response, SMT
        DEF VoteCurrentInv, Grant, HandleRequestVoteResponse
    <2>append_request. CASE /\ message.mtype = AppendEntriesRequest
                           /\ HandleAppendEntriesRequest(message.mdest, message.msource, message)
        BY <2>message, <2>append_request, MessageTypesDistinct, SMT
        DEF VoteCurrentInv, Grant, HandleAppendEntriesRequest,
            Send, WithMessage, WithMessages
    <2>append_response. CASE /\ message.mtype = AppendEntriesResponse
                            /\ HandleAppendEntriesResponse(message.mdest, message.msource, message)
        BY <2>message, <2>append_response, SMT
        DEF VoteCurrentInv, Grant, HandleAppendEntriesResponse
    <2> QED BY <2>message, <2>update, <2>vote_request, <2>vote_response,
        <2>append_request, <2>append_response, SMT DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader, <1>client,
    <1>commit, <1>append, <1>stepdown, <1>receive, SMT DEF Next

LEMMA VoteUniqueRecordsNext ==
    ASSUME TypeOK, SendInvariant, VoteGrantCore, [Next]_vars
    PROVE VoteUniqueInv'
<1>unchanged. UNCHANGED messages => VoteUniqueInv'
    BY SMT DEF VoteGrantCore, VoteUniqueInv, Grant
<1>timeout. \A actor \in Server: Timeout(actor) => VoteUniqueInv'
    BY MessageTypesDistinct, SMT
    DEF VoteGrantCore, VoteUniqueInv, Grant, Timeout, RequestVoteRequests, WithMessages
<1>append. \A actor, peer \in Server: AppendEntries(actor, peer) => VoteUniqueInv'
    BY MessageTypesDistinct, SMT
    DEF VoteGrantCore, VoteUniqueInv, Grant, AppendEntries, AppendEntriesMessage,
        Send, WithMessage, WithMessages
<1>vote_request. \A message \in messages:
        message.mtype = RequestVoteRequest /\
        HandleRequestVoteRequest(message.mdest, message.msource, message)
            => VoteUniqueInv'
    BY MessageFieldsTypeOK, MessageTypesDistinct, NilNotServer, SMTT(20)
    DEF VoteGrantCore, VoteCurrentInv, VoteUniqueInv, Grant, HandleRequestVoteRequest,
        Send, WithMessage, WithMessages, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>append_request. \A message \in messages:
        HandleAppendEntriesRequest(message.mdest, message.msource, message)
            => VoteUniqueInv'
    BY MessageTypesDistinct, SMT
    DEF VoteGrantCore, VoteUniqueInv, Grant, HandleAppendEntriesRequest,
        Send, WithMessage, WithMessages
<1>frames.
        /\ \A actor \in Server:
               Restart(actor) \/ BecomeLeader(actor)
                   \/ AdvanceCommitIndex(actor) \/ LeaderStepDown(actor)
                   => UNCHANGED messages
        /\ \A actor \in Server, payload \in ClientPayload:
               ClientRequest(actor, payload) => UNCHANGED messages
        /\ \A message \in messages:
               UpdateTerm(message.mdest, message.msource, message)
                   \/ HandleRequestVoteResponse(message.mdest, message.msource, message)
                   \/ HandleAppendEntriesResponse(message.mdest, message.msource, message)
                   => UNCHANGED messages
    BY Zenon
    DEF Restart, BecomeLeader, AdvanceCommitIndex, LeaderStepDown, ClientRequest,
        UpdateTerm, HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>unchanged, <1>timeout, <1>append, <1>vote_request,
    <1>append_request, <1>frames, SMT DEF Next, vars, Receive, HandleMsg

LEMMA HistoryVoteSupportRetained ==
    ASSUME TypeOK, [Next]_vars, NEW history, NEW larger, history \subseteq larger,
           NEW candidate \in Server, NEW term \in Nat, NEW support,
           HistoryVoteSupport(history, candidate, term, support)
    PROVE HistoryVoteSupport(larger, candidate, term, support)'
    BY MessagesMonotonicNext, SMT DEF HistoryVoteSupport, HistoryStarted, VoteFor, Grant

LEMMA HistoryElectionCertificateRetained ==
    ASSUME TypeOK, [Next]_vars, NEW history, NEW larger, history \subseteq larger,
           NEW candidate \in Server, NEW term \in Nat, NEW snapshot \in Seq(LogEntry),
           NEW occurrence, NEW support,
           HistoryElectionCertificate(history, candidate, term, snapshot, occurrence, support)
    PROVE HistoryElectionCertificate(larger, candidate, term, snapshot, occurrence, support)'
    BY HistoryVoteSupportRetained, SMT DEF HistoryElectionCertificate, HistoryCampaignSnapshot

LEMMA CurrentLeaderHasHistoryElectionCertificate ==
    ASSUME MembershipStructureInv, TermOrderingInv, GrantedVotesRecorded, NEW history, CampaignHistory(history),
           NEW candidate \in Server, state[candidate] = Leader
    PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
              /\ HistoryElectionCertificate(history, candidate, currentTerm[candidate], snapshot, occurrence, support)
              /\ snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])
<1>record. PICK record \in history:
        /\ record.candidate = candidate /\ record.term = currentTerm[candidate]
        /\ record.snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])
    BY SMT DEF CampaignHistory
<1>types. record.snapshot \in Seq(LogEntry) /\ currentTerm[candidate] \in Nat
          /\ log[candidate] \in Seq(LogEntry) /\ TermsOrdered(log[candidate])
    BY <1>record, SMT
    DEF CampaignHistory, CampaignHistoryRecord, MembershipStructureInv, ReplicationBoundsInv,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK, TermOrderingInv, LogTermsMonotonic,
        TermsOrdered
<1>config. ConfigOf(record.snapshot) = ElectionConfig(log[candidate], currentTerm[candidate])
    BY <1>record, <1>types, ElectionConfigIsCampaignConfiguration, SMT
<1>quorum. PICK support \in Quorums(ConfigOf(record.snapshot)): support \subseteq votesGranted[candidate]
    BY <1>config, SMT DEF MembershipStructureInv, MembershipElectionBase, LeaderQuorumInv
<1>members. ConfigOf(record.snapshot) \subseteq Server /\ ConfigOf(record.snapshot) # {}
    BY <1>types, ConfigurationType, SMT
<1>votes. HistoryVoteSupport(history, candidate, currentTerm[candidate], support)
    BY <1>record, <1>quorum, <1>members, SMT
    DEF HistoryVoteSupport, HistoryStarted, GrantedVotesRecorded, Quorums
<1> QED BY <1>record, <1>types, <1>quorum, <1>members, <1>votes, SMT
    DEF HistoryElectionCertificate, HistoryCampaignSnapshot, LatestConfigurationOccurrence

LEMMA CampaignSnapshotInView ==
    ASSUME NEW history, NEW candidate, NEW term, NEW snapshot
    PROVE HistoryCampaignSnapshot(history, candidate, term, snapshot)
          <=> [candidate |-> candidate, term |-> term, snapshot |-> snapshot] \in CampaignView(history)
    BY Zenon DEF HistoryCampaignSnapshot, CampaignView

LEMMA CampaignStartInView ==
    ASSUME NEW history, NEW candidate, NEW term
    PROVE HistoryStarted(history, candidate, term)
          <=> \E snapshot:
                  [candidate |-> candidate, term |-> term, snapshot |-> snapshot] \in CampaignView(history)
    BY Zenon DEF HistoryStarted, CampaignView

LEMMA CampaignHistoryStartIsStarted ==
    ASSUME NEW history, CampaignHistory(history), NEW candidate, NEW term
    PROVE HistoryStarted(history, candidate, term) <=> Started(history, candidate, term)
<1> SUFFICES ASSUME HistoryStarted(history, candidate, term)
             PROVE Started(history, candidate, term)
    BY SMT DEF HistoryStarted, Started
<1>record. PICK record \in history:
        record.candidate = candidate /\ record.term = term
    BY SMT DEF HistoryStarted
<1>bounds. candidate \in Server /\ term \in Nat /\ term <= currentTerm[candidate]
    BY <1>record, SMT DEF CampaignHistory, CampaignHistoryRecord
<1> QED BY <1>record, <1>bounds, SMT DEF Started

LEMMA CampaignHistoryStartRule == CampaignHistoryStartConsequence
    BY CampaignHistoryStartIsStarted, SMT DEF CampaignHistoryStartConsequence

LEMMA CampaignViewFramesStarted ==
    ASSUME NEW history, NEW larger, CampaignHistoryContextStep(history, larger),
           CampaignView(larger) = CampaignView(history)
    PROVE \A candidate, term: Started(larger, candidate, term)' <=> Started(history, candidate, term)
<1>rule. CampaignHistoryStartConsequence'
    BY CampaignHistoryStartRule, PTL
<1> QED BY <1>rule, CampaignStartInView, CampaignHistoryStartIsStarted, SMT
    DEF CampaignHistoryContextStep, CampaignHistoryStartConsequence

LEMMA RecordedVoteRequestFields ==
    ASSUME TypeOK, NEW voteHistory, CampaignHistory(voteHistory),
           NEW candidate \in Server, NEW term \in Nat,
           NEW request \in RecordedVoteRequests(voteHistory, candidate, term)
    PROVE request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
    BY MessageFieldsTypeOK, LastTermTypeOK, LenProperties, SMT
    DEF RecordedVoteRequests, RecordedCampaignRequests, CampaignHistory, CampaignHistoryRecord, TypeOK, MsgTypeOK

LEMMA RecordedVoteRequestNumericRule == RecordedVoteRequestNumericConsequence
    BY RecordedVoteRequestFields, SMT DEF RecordedVoteRequestNumericConsequence

LEMMA RecordedVoteRequestFieldsAfter ==
    ASSUME TypeOK', NEW history, CampaignHistory(history)', NEW candidate \in Server,
           NEW term \in Nat, NEW request \in RecordedVoteRequests(history, candidate, term)'
    PROVE request.mlastLogTerm \in Nat /\ request.mlastLogIndex \in Nat
<1>rule. RecordedVoteRequestNumericConsequence'
    BY RecordedVoteRequestNumericRule, PTL
<1> QED BY <1>rule, SMT DEF RecordedVoteRequestNumericConsequence

LEMMA RecordedVoteRequestsUseSnapshot ==
    ASSUME NEW voteHistory, CampaignHistory(voteHistory), NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot, HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot),
           NEW request \in RecordedVoteRequests(voteHistory, candidate, term)
    PROVE request.mlastLogTerm = LastTerm(snapshot) /\ request.mlastLogIndex = Len(snapshot)
    BY SMT DEF RecordedVoteRequests, RecordedCampaignRequests, HistoryCampaignSnapshot,
        CampaignHistory, CampaignHistoryRecord, CampaignRequests

LEMMA RecordedVoteRequestsMonotone ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, voteHistory \subseteq nextVoteHistory,
           messages \subseteq messages', NEW candidate, NEW term
    PROVE RecordedVoteRequests(voteHistory, candidate, term) \subseteq RecordedVoteRequests(nextVoteHistory, candidate, term)'
    BY SMT DEF RecordedVoteRequests, RecordedCampaignRequests

LEMMA NewHistoricalCampaignIsTimeout ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           NEW candidate \in Server, NEW term \in Nat,
           HistoryStarted(nextVoteHistory, candidate, term), ~HistoryStarted(voteHistory, candidate, term)
    PROVE /\ Timeout(candidate) /\ term = currentTerm[candidate] + 1
          /\ HistoryCampaignSnapshot(nextVoteHistory, candidate, term, log[candidate])
<1>timeout. CASE \E actor \in Server: Timeout(actor)
    <2>actor. PICK actor \in Server: Timeout(actor) BY <1>timeout, SMT
    <2> QED BY <2>actor, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, HistoryStarted, HistoryCampaignSnapshot
<1>other. CASE ~\E actor \in Server: Timeout(actor)
    <2>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        <3>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
            BY <2>client, SMT
        <3> QED BY <3>actor, SMT
            DEF CampaignHistoryContextStep, CampaignHistoryStep, HistoryStarted,
                CampaignHistory, ClientRequest
    <2>frame. CASE ~\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>other, <2>frame, SMT DEF CampaignHistoryContextStep, CampaignHistoryStep, HistoryStarted
    <2> QED BY <2>client, <2>frame, SMT
<1> QED BY <1>timeout, <1>other, SMT

LEMMA ExistingTermCampaignSnapshotBeforeStep ==
    ASSUME TypeOK, NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory), NEW candidate \in Server,
           NEW term \in Nat, term <= currentTerm[candidate], NEW snapshot,
           HistoryCampaignSnapshot(nextVoteHistory, candidate, term, snapshot)
    PROVE HistoryCampaignSnapshot(voteHistory, candidate, term, snapshot)
<1>timeout. CASE \E actor \in Server: Timeout(actor)
    <2>actor. PICK actor \in Server: Timeout(actor) BY <1>timeout, SMT
    <2> QED BY <2>actor, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, HistoryCampaignSnapshot, TypeOK, ServerVarsTypeOK
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>client, SMT
    <2> QED BY <2>actor, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, CampaignHistory, HistoryCampaignSnapshot, ClientRequest
<1>other. CASE /\ ~(\E actor \in Server: Timeout(actor))
               /\ ~(\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload))
    BY <1>other, SMT DEF CampaignHistoryContextStep, CampaignHistoryStep
<1> QED BY <1>timeout, <1>client, <1>other, SMT

LEMMA CampaignHistoryContextMonotone ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE voteHistory \subseteq nextVoteHistory
    BY SMT DEF CampaignHistoryContextStep, CampaignHistoryStep

LEMMA GrowingCampaignHistoriesKeepSnapshots ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           NEW candidate, NEW term, NEW left, NEW right,
           HistoryCampaignSnapshot(voteHistory, candidate, term, left),
           HistoryCampaignSnapshot(nextVoteHistory, candidate, term, right)
    PROVE left = right
    BY CampaignHistoryContextMonotone, SMT
    DEF CampaignHistoryContextStep, CampaignHistory, HistoryCampaignSnapshot

LEMMA UnchangedTermsKeepCampaignHistory ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           TypeOK, UNCHANGED currentTerm
    PROVE CampaignView(nextVoteHistory) = CampaignView(voteHistory)
<1>no_timeout. ~\E candidate \in Server: Timeout(candidate)
    BY UnchangedTermsExcludeTimeout, SMT
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>client, SMT
    <2>old. \E record \in voteHistory:
        /\ record.candidate = actor /\ record.term = currentTerm[actor]
        /\ record.snapshot = CampaignPrefix(log[actor], currentTerm[actor])
        BY <2>actor, SMT DEF CampaignHistoryContextStep, CampaignHistory, ClientRequest
    <2> QED BY <2>actor, <2>old, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, CampaignView
<1>other. CASE ~\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>other, <1>no_timeout, SMT DEF CampaignHistoryContextStep, CampaignHistoryStep
<1> QED BY <1>client, <1>other, SMT

LEMMA NoTimeoutKeepsCampaignView ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory),
           ~(\E actor \in Server: Timeout(actor))
    PROVE CampaignView(nextVoteHistory) = CampaignView(voteHistory)
<1>client. CASE \E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    <2>actor. PICK actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
        BY <1>client, SMT
    <2> QED BY <2>actor, SMT
        DEF CampaignHistoryContextStep, CampaignHistoryStep, CampaignHistory, CampaignView, ClientRequest
<1>other. CASE ~\E actor \in Server, payload \in ClientPayload: ClientRequest(actor, payload)
    BY <1>other, SMT DEF CampaignHistoryContextStep, CampaignHistoryStep
<1> QED BY <1>client, <1>other, SMT

LEMMA TimeoutGrantUnchanged ==
    \A i \in Server: Timeout(i) => \A voter, candidate, term:
        Grant(voter, candidate, term)' <=> Grant(voter, candidate, term)
    BY SMT, MessageTypesDistinct DEF Timeout, WithMessages, RequestVoteRequests, Grant

LEMMA VoteRecordInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE VoteEvidenceInv(voteHistory) /\ [Next]_vars => VoteRecordInv(nextVoteHistory)'
<1> SUFFICES ASSUME VoteEvidenceInv(voteHistory), [Next]_vars PROVE VoteRecordInv(nextVoteHistory)' BY SMT
<1>current. VoteCurrentInv'
    BY VoteCurrentRecordsNext, SMT DEF VoteEvidenceInv, VoteRecordInv
<1>unique. VoteUniqueInv'
    BY VoteUniqueRecordsNext, SMT DEF VoteEvidenceInv, VoteRecordInv, VoteGrantCore
<1> QED BY <1>current, <1>unique, SMT
    DEF VoteRecordInv, StartedGrantInv, StartedCurrentInv, Started,
        CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord, Grant

LEMMA ActiveVotesInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE VoteEvidenceInv(voteHistory) /\ [Next]_vars => ActiveVotesInv(nextVoteHistory)'
<1> SUFFICES ASSUME VoteEvidenceInv(voteHistory), [Next]_vars PROVE ActiveVotesInv(nextVoteHistory)' BY SMT
<1>before. GrantedVotesRecorded BY SMT DEF VoteEvidenceInv, ActiveVotesInv, GrantedVotesRecorded
<1>after. GrantedVotesRecorded' BY <1>before, GrantedVotesRecordedNext, SMT DEF VoteEvidenceInv
<1> QED BY <1>after, SMT
    DEF ActiveVotesInv, GrantedVotesRecorded, Started, CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord

LEMMA VoteForUnique ==
    ASSUME NEW voteHistory, VoteRecordInv(voteHistory), NEW voter \in Server, NEW left \in Server,
           NEW right \in Server, NEW term \in Nat,
           Started(voteHistory, left, term), Started(voteHistory, right, term),
           VoteFor(voter, left, term), VoteFor(voter, right, term)
    PROVE left = right
    BY SMT DEF VoteRecordInv, VoteUniqueInv, StartedGrantInv, VoteFor

LEMMA IntersectingVoteSupportsUnique ==
    ASSUME NEW voteHistory, VoteRecordInv(voteHistory), NEW left \in Server, NEW right \in Server,
           NEW term \in Nat, NEW first, NEW second,
           VoteSupport(voteHistory, left, term, first), VoteSupport(voteHistory, right, term, second),
           first \cap second # {}
    PROVE left = right
<1>voter. PICK voter \in first \cap second: TRUE BY SMT
<1> QED BY <1>voter, VoteForUnique, SMT DEF VoteSupport


LEMMA VoteSupportEvidenceRetained ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE [Next]_vars => \A candidate, term, support:
        VoteSupport(voteHistory, candidate, term, support) => VoteSupport(nextVoteHistory, candidate, term, support)'
    BY CampaignHistoryContextMonotone, MessagesMonotonicNext, SMT
    DEF VoteSupport, Started, VoteFor, Grant, CampaignHistoryContextStep, CampaignHistory, CampaignHistoryRecord

LEMMA ActiveLeaderHasVoteSupport ==
    ASSUME NEW voteHistory
    PROVE MembershipVotesInv(voteHistory) => \A leader \in Server: state[leader] = Leader =>
        \E quorum \in Quorums(ElectionConfig(log[leader], currentTerm[leader])):
            VoteSupport(voteHistory, leader, currentTerm[leader], quorum)
    BY SMT DEF MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        TypeOK, CandidateVarsTypeOK, MembershipElectionBase, LeaderQuorumInv, ActiveVotesInv, VoteSupport

LEMMA MembershipVotesInvInit == Init => MembershipVotesInv({})
    BY MembershipStructureInvInit, CampaignHistoryInit, VoteGrantCoreInit, GrantedVotesRecordedInit,
       ServerStatesDistinct, SMT
    DEF MembershipVotesInv, VoteRecordInv, VoteGrantCore, StartedGrantInv,
        StartedCurrentInv, ActiveVotesInv, Started, Init, InitServerVars

LEMMA MembershipVotesInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory, CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE MembershipVotesInv(voteHistory) /\ [Next]_vars => MembershipVotesInv(nextVoteHistory)'
    BY MembershipStructureInvNext, VoteRecordInvNext, ActiveVotesInvNext, SMT
    DEF MembershipVotesInv, MembershipStructureInv, ReplicationBoundsInv,
        VoteEvidenceInv, CampaignHistoryContextStep

LEMMA CurrentLeaderHasElectionCertificate ==
    ASSUME NEW voteHistory
    PROVE MembershipCampaignsInv(voteHistory) => \A candidate \in Server:
        state[candidate] = Leader =>
            \E snapshot \in Seq(LogEntry): \E occurrence, support:
                CurrentElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                           snapshot, occurrence, support)
<1> SUFFICES ASSUME MembershipCampaignsInv(voteHistory), NEW candidate \in Server,
                      state[candidate] = Leader
             PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
                       CurrentElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                                  snapshot, occurrence, support)
    BY SMT
<1> DEFINE snapshot == CampaignPrefix(log[candidate], currentTerm[candidate])
           occurrence == LatestConfigurationOccurrence(snapshot)
<1>types.
        /\ log[candidate] \in Seq(LogEntry)
        /\ currentTerm[candidate] \in Nat
        /\ TermsOrdered(log[candidate])
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, TypeOK, ServerVarsTypeOK, LogVarsTypeOK,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>prefix.
        /\ snapshot \in Seq(LogEntry)
        /\ \A index \in DOMAIN snapshot: snapshot[index].term < currentTerm[candidate]
    BY <1>types, CampaignPrefixProperties, SMT DEF snapshot
<1>members.
        /\ occurrence.members = ElectionConfig(log[candidate], currentTerm[candidate])
        /\ occurrence.members \subseteq Server
        /\ occurrence.members # {}
    BY <1>types, <1>prefix, ElectionConfigIsCampaignConfiguration, ConfigurationType, SMT
    DEF snapshot, occurrence, LatestConfigurationOccurrence
<1>support. PICK support \in Quorums(ElectionConfig(log[candidate], currentTerm[candidate])):
        VoteSupport(voteHistory, candidate, currentTerm[candidate], support)
    BY ActiveLeaderHasVoteSupport, SMT DEF MembershipCampaignsInv
<1>peers. \A voter \in support \ {candidate}:
        \E request \in CampaignRequests(candidate, currentTerm[candidate], snapshot):
            /\ request \in messages
            /\ request.mdest = voter
    BY <1>support, PositivePeerGrantHasCampaignRequest, SMT
    DEF MembershipCampaignsInv, VoteSupport, VoteFor, snapshot
<1>history. CampaignHistory(voteHistory)
          /\ HistoryCampaignSnapshot(voteHistory, candidate, currentTerm[candidate], snapshot)
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, CampaignHistory, HistoryCampaignSnapshot, snapshot
<1> QED BY <1>prefix, <1>members, <1>support, <1>peers, <1>history, SMT
    DEF CurrentElectionCertificate, MembershipCampaignsInv, CampaignSnapshotInv,
        snapshot, occurrence

------------------------------------------------------------------------

LEMMA MembershipCampaignsInvInit ==
    Init => MembershipCampaignsInv({})
    BY MembershipVotesInvInit, TermOrderingInvInit, ServerStatesDistinct, SMT
    DEF MembershipCampaignsInv, CampaignSnapshotInv, PositiveVoteResponseRequestInv,
        Init, InitServerVars

LEMMA MembershipCampaignsInvNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE MembershipCampaignsInv(voteHistory) /\ [Next]_vars => MembershipCampaignsInv(nextVoteHistory)'
    BY MembershipVotesInvNext, TermOrderingInvNext, CampaignSnapshotInvNext,
       PositiveVoteResponseRequestInvNext, LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, OrderingBase

LEMMA MembershipCampaignStepExists ==
    ASSUME NEW voteHistory, MembershipCampaignsInv(voteHistory), [Next]_vars
    PROVE \E nextVoteHistory: CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    BY CampaignHistoryNext, LogStructureImpliesTermBound, SMT
    DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, CampaignHistoryContextStep

LEMMA HistoryElectionCertificateIsRetained ==
    ASSUME NEW voteHistory, CampaignHistory(voteHistory), NEW candidate \in Server, NEW term \in Nat,
           NEW snapshot \in Seq(LogEntry), NEW occurrence, NEW support,
           HistoryElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    PROVE RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
<1>record. PICK record \in voteHistory:
        record.candidate = candidate /\ record.term = term /\ record.snapshot = snapshot
    BY SMT DEF HistoryElectionCertificate, HistoryCampaignSnapshot
<1>data. CampaignHistoryRecord(record)
    BY <1>record, SMT DEF CampaignHistory
<1>peers. \A voter \in support \ {candidate}: \E request \in CampaignRequests(candidate, term, snapshot):
        request \in messages /\ request.mdest = voter
    <2> SUFFICES ASSUME NEW voter \in support \ {candidate}
                 PROVE \E request \in CampaignRequests(candidate, term, snapshot): request \in messages /\ request.mdest = voter BY SMT
    <2>member. voter \in ConfigOf(snapshot) \ {candidate}
        BY SMT DEF HistoryElectionCertificate, LatestConfigurationOccurrence, Quorums
    <2>request. PICK request \in CampaignRequests(candidate, term, snapshot): request.mdest = voter
        BY <2>member, SMT DEF CampaignRequests
    <2> QED BY <1>record, <1>data, <2>request, SMT DEF CampaignHistoryRecord, RecordedCampaignRequests
<1> QED BY <1>record, <1>data, <1>peers, SMT
    DEF RetainedElectionCertificate, HistoryElectionCertificate, HistoryVoteSupport,
        VoteSupport, Started, HistoryStarted, CampaignHistoryRecord

LEMMA LocalAppendOriginHasRetainedElection ==
    ASSUME NEW voteHistory, CampaignHistory(voteHistory), NEW leader \in Server, NEW term \in Nat,
           NEW entries, LocalAppendOrigin(voteHistory, leader, term, entries)
    PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
        RetainedElectionCertificate(voteHistory, leader, term, snapshot, occurrence, support)
<1>record. PICK record \in voteHistory:
        /\ LocalAppendRecord(record) /\ record.candidate = leader /\ record.term = term
        /\ record.prefix \in Seq(LogEntry) /\ IsPrefix(entries, record.prefix)
    BY SMT DEF LocalAppendOrigin
<1>data. record.snapshot \in Seq(LogEntry)
         /\ record.support \in Quorums(ConfigOf(record.snapshot))
         /\ \A voter \in record.support: VoteFor(voter, leader, term)
    BY <1>record, SMT DEF CampaignHistory, CampaignHistoryRecord, LocalAppendRecord
<1>config. ConfigOf(record.snapshot) \in (SUBSET Server) \ { {} }
    BY <1>data, ConfigurationType, SMT
<1>history. HistoryElectionCertificate(voteHistory, leader, term, record.snapshot,
        LatestConfigurationOccurrence(record.snapshot), record.support)
    BY <1>record, <1>data, <1>config, SMT
    DEF HistoryElectionCertificate, HistoryVoteSupport, HistoryStarted, HistoryCampaignSnapshot, LatestConfigurationOccurrence, Quorums
<1>retained. RetainedElectionCertificate(voteHistory, leader, term, record.snapshot,
        LatestConfigurationOccurrence(record.snapshot), record.support)
    BY <1>history, <1>data, HistoryElectionCertificateIsRetained, SMT
<1> QED BY <1>data, <1>retained, SMT

------------------------------------------------------------------------

LEMMA StartedCampaignRequestsFixed ==
    ASSUME NEW voteHistory, CampaignHistory(voteHistory)
    PROVE \A candidate \in Server, term \in Nat:
        /\ TypeOK /\ SendInvariant /\ Started(voteHistory, candidate, term)
        /\ [Next]_vars
        => RecordedCampaignRequests(candidate, term)' =
               RecordedCampaignRequests(candidate, term)
<1> SUFFICES ASSUME NEW candidate \in Server, NEW term \in Nat,
                      TypeOK, SendInvariant, Started(voteHistory, candidate, term), [Next]_vars
             PROVE RecordedCampaignRequests(candidate, term)' =
                       RecordedCampaignRequests(candidate, term)
    BY SMT
<1>term. term <= currentTerm[candidate]
    BY SMT DEF Started, CampaignHistory, CampaignHistoryRecord
<1>timeouts. \A actor \in Server:
        /\ TypeOK /\ SendInvariant /\ Timeout(actor)
        /\ term <= currentTerm[candidate]
        => RecordedCampaignRequests(candidate, term)' =
               RecordedCampaignRequests(candidate, term)
    BY SMT
    DEF TypeOK, ServerVarsTypeOK, Timeout, RequestVoteRequests,
        WithMessages, RecordedCampaignRequests
<1>others.
        /\ TypeOK
        /\ \/ UNCHANGED vars
           \/ \E actor \in Server: Restart(actor)
           \/ \E actor \in Server: BecomeLeader(actor)
           \/ \E actor \in Server, payload \in ClientPayload:
                  ClientRequest(actor, payload)
           \/ \E actor \in Server: AdvanceCommitIndex(actor)
           \/ \E actor, peer \in Server: AppendEntries(actor, peer)
           \/ \E actor \in Server: LeaderStepDown(actor)
           \/ \E message \in messages: Receive(message)
        => RecordedCampaignRequests(candidate, term)' =
               RecordedCampaignRequests(candidate, term)
    BY MessageTypesDistinct, SMT
    DEF RecordedCampaignRequests, vars, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, AppendEntriesMessage, LeaderStepDown,
        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>term, <1>timeouts, <1>others, SMT DEF Next

LEMMA CaptureCurrentElectionCertificate ==
    ASSUME NEW voteHistory
    PROVE \A candidate \in Server, term \in Nat, snapshot \in Seq(LogEntry):
    \A occurrence, support:
        CurrentElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        => RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
    BY SMT DEF CurrentElectionCertificate, RetainedElectionCertificate

LEMMA RetainedElectionCertificateNext ==
    ASSUME NEW voteHistory, NEW nextVoteHistory,
           CampaignHistoryContextStep(voteHistory, nextVoteHistory)
    PROVE \A candidate \in Server, term \in Nat, snapshot \in Seq(LogEntry):
    \A occurrence, support:
        /\ TypeOK /\ SendInvariant /\ [Next]_vars
        /\ RetainedElectionCertificate(voteHistory, candidate, term, snapshot, occurrence, support)
        => RetainedElectionCertificate(nextVoteHistory, candidate, term, snapshot, occurrence, support)'
    BY StartedCampaignRequestsFixed, VoteSupportEvidenceRetained,
       MessagesMonotonicNext, CampaignHistoryContextMonotone, SMT
    DEF RetainedElectionCertificate, VoteSupport, HistoryCampaignSnapshot, CampaignHistoryContextStep

LEMMA ClientRequestCapturesElectionCertificate ==
    ASSUME NEW voteHistory
    PROVE \A candidate \in Server, payload \in ClientPayload:
        MembershipCampaignsInv(voteHistory) /\ ClientRequest(candidate, payload) =>
        \E snapshot \in Seq(LogEntry): \E occurrence, support:
            /\ RetainedElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                           snapshot, occurrence, support)
            /\ snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])
            /\ IsPrefix(snapshot, log'[candidate])
            /\ Len(snapshot) < Len(log'[candidate])
<1> SUFFICES ASSUME NEW candidate \in Server, NEW payload \in ClientPayload,
                      MembershipCampaignsInv(voteHistory), ClientRequest(candidate, payload)
             PROVE \E snapshot \in Seq(LogEntry): \E occurrence, support:
                       /\ RetainedElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                                      snapshot, occurrence, support)
                       /\ snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])
                       /\ IsPrefix(snapshot, log'[candidate])
                       /\ Len(snapshot) < Len(log'[candidate])
    BY SMT
<1>types.
        /\ TypeOK
        /\ currentTerm[candidate] \in Nat
        /\ log[candidate] \in Seq(LogEntry)
        /\ TermsOrdered(log[candidate])
    BY SMT DEF MembershipCampaignsInv, MembershipVotesInv, MembershipStructureInv,
        ReplicationBoundsInv, TypeOK, ServerVarsTypeOK, LogVarsTypeOK,
        TermOrderingInv, LogTermsMonotonic, TermsOrdered
<1>certificate. PICK snapshot, occurrence, support:
        /\ snapshot \in Seq(LogEntry)
        /\ CurrentElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                      snapshot, occurrence, support)
    BY CurrentLeaderHasElectionCertificate, SMT DEF ClientRequest
<1>entry. PICK entry \in LogEntry:
        /\ entry.term = currentTerm[candidate]
        /\ log'[candidate] = Append(log[candidate], entry)
    BY <1>types, ClientRequestAppendsCurrentTerm, SMT
<1>prefix.
        /\ snapshot = CampaignPrefix(log[candidate], currentTerm[candidate])
        /\ Len(snapshot) = CampaignPrefixIndex(log[candidate], currentTerm[candidate])
        /\ Len(snapshot) <= Len(log[candidate])
    BY <1>types, <1>certificate, CampaignPrefixProperties, PreTermIndexProperties, SMT
    DEF CurrentElectionCertificate
<1>retained. RetainedElectionCertificate(voteHistory, candidate, currentTerm[candidate],
                                       snapshot, occurrence, support)
    BY <1>types, <1>certificate, CaptureCurrentElectionCertificate, SMT
<1>post_prefix.
        /\ IsPrefix(snapshot, log'[candidate])
        /\ Len(snapshot) < Len(log'[candidate])
    BY <1>types, <1>certificate, <1>entry, <1>prefix, AppendPreservesSequencePrefix,
       AppendProperties, LenProperties, SMT DEF IsPrefix, CampaignPrefix
<1> QED BY <1>certificate, <1>prefix, <1>retained, <1>post_prefix, SMT

=======================================================================
