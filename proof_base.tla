------------------------------ MODULE proof_base ------------------------------
\* proof_base.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_library

\* A campaign and its leader use the configuration inherited before their
\* term. Appending further entries in that term cannot change this choice.
ElectionConfigIndexes(entries, term) ==
    {index \in ConfigChangeIndexes(entries): entries[index].term < term}

ElectionConfig(entries, term) ==
    LET index == MaxOrZero(ElectionConfigIndexes(entries, term))
    IN IF index = 0 THEN InitialConfig ELSE entries[index].members

\* Retained peer requests witness campaigns with a peer destination. Singleton
\* self-campaigns use the finite records in proof_election_history.
Started(history, candidate, term) ==
    /\ candidate \in Server /\ term \in Nat
    /\ term <= currentTerm[candidate]
    /\ \E record \in history: record.candidate = candidate /\ record.term = term

CandidateCurrentTermFree ==
    \A server \in Server:
        state[server] = Candidate =>
            \A index \in DOMAIN log[server]:
                log[server][index].term < currentTerm[server]

LogTermBoundInv ==
    \A server \in Server: \A index \in DOMAIN log[server]:
        log[server][index].term <= currentTerm[server]

\* This is the election configuration, even after same-term changes append.
LeaderQuorumInv ==
    \A server \in Server:
        state[server] = Leader =>
            \E quorum \in Quorums(ElectionConfig(log[server], currentTerm[server])):
                quorum \subseteq votesGranted[server]

MembershipElectionBase == CandidateCurrentTermFree /\ LeaderQuorumInv

\* Type preservation is conditional on the replication bounds. The structural
\* induction proves these bounds together with TypeOK, without safety premises.
NextIndexBound ==
    \A i, j \in Server:
        state[i] = Leader =>
            /\ nextIndex[i][j] <= Len(log[i]) + 1
            /\ matchIndex[i][j] <= Len(log[i])

RequestIndexBound ==
    \A m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ m.mterm = currentTerm[m.msource]
        /\ state[m.msource] \in {Candidate, Leader}
        => m.mprevLogIndex + Len(m.mentries) <= Len(log[m.msource])

ResponseTermBound ==
    \A m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ m.mmatchIndex > 0
        => m.mterm <= currentTerm[m.mdest]

ResponseIndexBound ==
    \A m \in messages:
        /\ m.mtype = AppendEntriesResponse
        /\ m.mterm = currentTerm[m.mdest]
        /\ state[m.mdest] \in {Candidate, Leader}
        => m.mmatchIndex <= Len(log[m.mdest])

ReplicationBoundsInv ==
    /\ TypeOK
    /\ SendInvariant
    /\ NextIndexBound
    /\ RequestIndexBound
    /\ ResponseTermBound
    /\ ResponseIndexBound

\* These properties survive even when the only remaining copy of an entry is
\* in an undelivered request. They do not assert agreement or log matching.
EntryStructure(entries, term) ==
    \A index \in DOMAIN entries: entries[index].term <= term

LogStructureInv ==
    \A server \in Server: EntryStructure(log[server], currentTerm[server])

RequestStructureInv ==
    \A message \in messages:
        message.mtype = AppendEntriesRequest =>
            EntryStructure(message.mentries, message.mterm)

MembershipStructureInv ==
    /\ ReplicationBoundsInv
    /\ LogStructureInv
    /\ RequestStructureInv
    /\ MembershipElectionBase

Grant(voter, candidate, term) ==
    \E message \in messages:
        /\ message.mtype = RequestVoteResponse
        /\ message.mterm = term
        /\ message.mvoteGranted
        /\ message.msource = voter
        /\ message.mdest = candidate

\* The caller's configuration decides whether a self-vote is eligible.
\* VoteSupport additionally requires evidence that the campaign started.
VoteFor(voter, candidate, term) ==
    voter = candidate \/ Grant(voter, candidate, term)

VoteCurrentInv ==
    \A voter, candidate \in Server, term \in Nat:
        Grant(voter, candidate, term) /\ currentTerm[voter] = term
        => votedFor[voter] = candidate

VoteUniqueInv ==
    \A voter, left, right \in Server, term \in Nat:
        Grant(voter, left, term) /\ Grant(voter, right, term) => left = right

\* This pre-state layer suffices for ordering; no election uniqueness or
\* agreement property is assumed.
OrderingBase == TypeOK /\ LogTermBoundInv

LogTermsMonotonic ==
    \A server \in Server:
    \A first, last \in DOMAIN log[server]:
        first <= last => log[server][first].term <= log[server][last].term

\* A nonempty request orders its first entry after its preceding entry.
MessageTermsMonotonic ==
    \A m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ m.mprevLogIndex > 0
        /\ m.mentries # << >>
        => m.mprevLogTerm <= m.mentries[1].term

TermOrderingInv == LogTermsMonotonic /\ MessageTermsMonotonic

LEMMA ConfigurationQuorumNonempty ==
    \A config \in SUBSET Server: \A quorum \in Quorums(config):
        quorum # {}
    BY ServerOK, FiniteSetSubsetsAreFinite, ConfigurationQuorumProperties, FS_EmptySet, SMT

LEMMA ConfigurationIndexProperties ==
    \A entries \in Seq(LogEntry):
        /\ ConfigChangeIndexes(entries) \subseteq 1..Len(entries)
        /\ LastConfigChangeIndex(entries) \in 0..Len(entries)
        /\ (LastConfigChangeIndex(entries) = 0
            <=> ConfigChangeIndexes(entries) = {})
        /\ (LastConfigChangeIndex(entries) # 0
            => LastConfigChangeIndex(entries) \in ConfigChangeIndexes(entries))
        /\ \A index \in ConfigChangeIndexes(entries):
                index <= LastConfigChangeIndex(entries)
    BY LenProperties, PositiveIndexMaxOrZeroProperties, SMT
    DEF ConfigChangeIndexes, LastConfigChangeIndex

LEMMA ConfigurationIndexesOnAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry:
        ConfigChangeIndexes(Append(entries, entry)) =
            IF entry.members # Nil
            THEN ConfigChangeIndexes(entries) \cup {Len(entries) + 1}
            ELSE ConfigChangeIndexes(entries)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry
             PROVE ConfigChangeIndexes(Append(entries, entry)) =
                       IF entry.members # Nil
                       THEN ConfigChangeIndexes(entries) \cup {Len(entries) + 1}
                       ELSE ConfigChangeIndexes(entries)
    BY SMT
<1>append.
        /\ DOMAIN entries = 1..Len(entries)
        /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
        /\ Len(entries) \in Nat
        /\ \A index \in DOMAIN entries:
                Append(entries, entry)[index] = entries[index]
        /\ Append(entries, entry)[Len(entries) + 1] = entry
    BY AppendProperties, LenProperties, SMT
<1> QED BY <1>append, SMT DEF ConfigChangeIndexes

LEMMA ConfigurationOnAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry:
        ConfigOf(Append(entries, entry)) =
            IF entry.members # Nil THEN entry.members ELSE ConfigOf(entries)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry
             PROVE ConfigOf(Append(entries, entry)) =
                       IF entry.members # Nil
                       THEN entry.members ELSE ConfigOf(entries)
    BY SMT
<1>indexes. ConfigChangeIndexes(Append(entries, entry)) =
                IF entry.members # Nil
                THEN ConfigChangeIndexes(entries) \cup {Len(entries) + 1}
                ELSE ConfigChangeIndexes(entries)
    BY SMT, ConfigurationIndexesOnAppend
<1>config. CASE entry.members # Nil
    <2>last. LastConfigChangeIndex(Append(entries, entry)) = Len(entries) + 1
        BY <1>config, <1>indexes, LenProperties, ConfigurationIndexProperties,
           MaxOrZeroAddingLastIndex, SMT DEF LastConfigChangeIndex
    <2> QED BY <1>config, <2>last, AppendProperties, LenProperties, SMT
        DEF ConfigOf
<1>noConfig. CASE entry.members = Nil
    <2>last. LastConfigChangeIndex(Append(entries, entry)) =
                 LastConfigChangeIndex(entries)
        BY <1>noConfig, <1>indexes, SMT DEF LastConfigChangeIndex
    <2> QED BY <1>noConfig, <2>last, ConfigurationIndexProperties,
        AppendProperties, LenProperties, SMT DEF ConfigOf, ConfigChangeIndexes
<1> QED BY <1>config, <1>noConfig, SMT

LEMMA ConfigurationIndexesOnPrefix ==
    \A entries \in Seq(LogEntry): \A cut \in 0..Len(entries):
        ConfigChangeIndexes(SubSeq(entries, 1, cut)) =
            ConfigChangeIndexes(entries) \cap (1..cut)
    BY SubSeqProperties, LenProperties, SMT DEF ConfigChangeIndexes

LEMMA ConfigurationType ==
    \A entries \in Seq(LogEntry): ConfigOf(entries) \in (SUBSET Server) \ { {} }
    BY ConfigurationIndexProperties, InitialConfigOK, ElementOfSeq, SMT
    DEF ConfigOf, ConfigChangeIndexes, LogEntry

LEMMA ElectionConfigIndexesOnAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        entry.term >= term =>
            ElectionConfigIndexes(Append(entries, entry), term) =
                ElectionConfigIndexes(entries, term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                      NEW term \in Nat, entry.term >= term
             PROVE ElectionConfigIndexes(Append(entries, entry), term) =
                       ElectionConfigIndexes(entries, term)
    BY SMT
<1>indexes. ConfigChangeIndexes(Append(entries, entry)) =
                IF entry.members # Nil
                THEN ConfigChangeIndexes(entries) \cup {Len(entries) + 1}
                ELSE ConfigChangeIndexes(entries)
    BY SMT, ConfigurationIndexesOnAppend
<1>append.
        /\ \A index \in ConfigChangeIndexes(entries):
                Append(entries, entry)[index] = entries[index]
        /\ Append(entries, entry)[Len(entries) + 1] = entry
    BY ConfigurationIndexProperties, AppendProperties, LenProperties, SMT
<1>term_type. entry.term \in Nat
    BY SMT DEF LogEntry
<1> QED BY <1>indexes, <1>append, <1>term_type, SMT DEF ElectionConfigIndexes

LEMMA ElectionConfigBeforeTerm ==
    \A entries \in Seq(LogEntry), term \in Nat:
        (\A index \in DOMAIN entries: entries[index].term < term)
        => ElectionConfig(entries, term) = ConfigOf(entries)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW term \in Nat,
                      \A index \in DOMAIN entries: entries[index].term < term
             PROVE ElectionConfig(entries, term) = ConfigOf(entries)
    BY SMT
<1>indexes. ElectionConfigIndexes(entries, term) = ConfigChangeIndexes(entries)
    BY SMT DEF ElectionConfigIndexes, ConfigChangeIndexes
<1> QED BY <1>indexes, SMT
    DEF ElectionConfig, ConfigOf, LastConfigChangeIndex

LEMMA ElectionConfigOnCurrentTermAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        entry.term = term =>
            ElectionConfig(Append(entries, entry), term) =
                ElectionConfig(entries, term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                      NEW term \in Nat, entry.term = term
             PROVE ElectionConfig(Append(entries, entry), term) =
                       ElectionConfig(entries, term)
    BY SMT
<1>indexes. ElectionConfigIndexes(Append(entries, entry), term) =
                ElectionConfigIndexes(entries, term)
    BY ElectionConfigIndexesOnAppend, SMT
<1>bound. ElectionConfigIndexes(entries, term) \subseteq 1..Len(entries)
    BY LenProperties, SMT DEF ElectionConfigIndexes, ConfigChangeIndexes
<1>index. MaxOrZero(ElectionConfigIndexes(entries, term)) \in 0..Len(entries)
    BY <1>bound, LenProperties, PositiveIndexMaxOrZeroProperties, SMT
<1>append. \A index \in 1..Len(entries):
               Append(entries, entry)[index] = entries[index]
    BY AppendProperties, LenProperties, SMT
<1> QED BY <1>indexes, <1>index, <1>append, SMT
    DEF ElectionConfig

LEMMA MembershipMessageEndpoints ==
    MsgTypeOK => \A message \in messages:
        /\ message.msource \in Server
        /\ message.mdest \in Server
        /\ message.mterm \in Nat
    BY SMT DEF MsgTypeOK, Message, RequestVoteRequestMessage,
        RequestVoteResponseMessage, AppendEntriesRequestMessage,
        AppendEntriesResponseMessage

LEMMA ClientRequestAppendsCurrentTerm ==
    \A server \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(server, payload) =>
        \E entry \in LogEntry:
            /\ entry.term = currentTerm[server]
            /\ entry.value = payload.value
            /\ entry.members = payload.members
            /\ log'[server] = Append(log[server], entry)
<1> SUFFICES ASSUME NEW server \in Server, NEW payload \in ClientPayload,
                    TypeOK, ClientRequest(server, payload)
             PROVE \E entry \in LogEntry:
                /\ entry.term = currentTerm[server]
                /\ entry.value = payload.value
                /\ entry.members = payload.members
                /\ log'[server] = Append(log[server], entry)
    BY SMT
<1> DEFINE entry == [term |-> currentTerm[server],
                      value |-> payload.value, members |-> payload.members]
<1>term. currentTerm[server] \in Nat
    BY SMT DEF TypeOK, ServerVarsTypeOK
<1>entry. entry \in LogEntry
    BY <1>term, SMT DEF entry, ClientPayload, LogEntry
<1>domain. server \in DOMAIN log
    BY SMT DEF TypeOK, LogVarsTypeOK
<1>log. log'[server] = Append(log[server], entry)
    BY <1>domain, SMT DEF ClientRequest, entry
<1> QED BY <1>entry, <1>log, SMT DEF entry

LEMMA ClientRequestPreservesElectionConfig ==
    \A server \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(server, payload) =>
            ElectionConfig(log'[server], currentTerm'[server]) =
                ElectionConfig(log[server], currentTerm[server])
    BY ClientRequestAppendsCurrentTerm, ElectionConfigOnCurrentTermAppend, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, ClientRequest

LEMMA BecomeLeaderUsesElectionConfig ==
    \A server \in Server:
        TypeOK /\ CandidateCurrentTermFree /\ BecomeLeader(server) =>
            \E quorum \in Quorums(ElectionConfig(log[server], currentTerm[server])):
                quorum \subseteq votesGranted[server]
<1> SUFFICES ASSUME NEW server \in Server, TypeOK, CandidateCurrentTermFree,
                    BecomeLeader(server)
             PROVE \E quorum \in Quorums(ElectionConfig(log[server], currentTerm[server])):
                       quorum \subseteq votesGranted[server]
    BY SMT
<1>config. ElectionConfig(log[server], currentTerm[server]) = LastConfiguration(server)
    BY ElectionConfigBeforeTerm, SMT DEF BecomeLeader, TypeOK, ServerVarsTypeOK,
        LogVarsTypeOK, CandidateCurrentTermFree, LastConfiguration
<1> QED BY <1>config, SMT DEF BecomeLeader

LEMMA CandidateCurrentTermFreeNext ==
    /\ TypeOK /\ LogTermBoundInv /\ CandidateCurrentTermFree
    /\ [Next]_vars
    => CandidateCurrentTermFree'
<1> USE ServerStatesDistinct
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, CandidateCurrentTermFree
<1>timeout. \A server \in Server:
        /\ TypeOK /\ LogTermBoundInv /\ CandidateCurrentTermFree /\ Timeout(server)
        => CandidateCurrentTermFree'
    <2> SUFFICES ASSUME NEW server \in Server, TypeOK, LogTermBoundInv,
                          CandidateCurrentTermFree, Timeout(server),
                          NEW candidate \in Server, state'[candidate] = Candidate,
                          NEW index \in DOMAIN log'[candidate]
                 PROVE log'[candidate][index].term < currentTerm'[candidate]
        BY SMT
    <2>same. CASE candidate = server
        <3>bound. log[candidate][index].term <= currentTerm[candidate]
            BY <2>same, SMT DEF LogTermBoundInv, Timeout
        <3>terms.
                /\ currentTerm'[candidate] = currentTerm[candidate] + 1
                /\ currentTerm[candidate] \in Nat
                /\ log'[candidate] = log[candidate]
            BY <2>same, SMT DEF Timeout
        <3>entry. log[candidate][index].term \in Nat
            BY <3>terms, ElementOfSeq, SMT DEF LogEntry
        <3> QED BY <3>bound, <3>terms, <3>entry, SMT
    <2>other. CASE candidate # server
        BY <2>other, SMT DEF Timeout
    <2> QED BY <2>same, <2>other, SMT
<1>others.
        /\ TypeOK /\ CandidateCurrentTermFree
        /\ \/ UNCHANGED vars
           \/ \E server \in Server: Restart(server)
           \/ \E server \in Server: BecomeLeader(server)
           \/ \E server \in Server, payload \in ClientPayload:
                  ClientRequest(server, payload)
           \/ \E server \in Server: AdvanceCommitIndex(server)
           \/ \E server, peer \in Server: AppendEntries(server, peer)
           \/ \E server \in Server: LeaderStepDown(server)
           \/ \E message \in messages: Receive(message)
        => CandidateCurrentTermFree'
    BY MembershipMessageEndpoints, SMT
    DEF vars, Restart, BecomeLeader, ClientRequest, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1> QED BY <1>timeout, <1>others, SMT DEF Next

LEMMA ContinuingLeaderFrameExceptClientRequest ==
    \A server \in Server:
        /\ TypeOK
        /\ state[server] = Leader /\ state'[server] = Leader
        /\ \/ UNCHANGED vars
           \/ \E actor \in Server: Restart(actor)
           \/ \E actor \in Server: Timeout(actor)
           \/ \E actor \in Server: BecomeLeader(actor)
           \/ \E actor \in Server: AdvanceCommitIndex(actor)
           \/ \E actor, peer \in Server: AppendEntries(actor, peer)
           \/ \E actor \in Server: LeaderStepDown(actor)
           \/ \E message \in messages: Receive(message)
        => /\ currentTerm'[server] = currentTerm[server]
           /\ log'[server] = log[server]
           /\ votesGranted[server] \subseteq votesGranted'[server]
    BY ServerStatesDistinct, MembershipMessageEndpoints, SMT
    DEF TypeOK, ServerVarsTypeOK, CandidateVarsTypeOK, LogVarsTypeOK,
        vars, Restart, Timeout, BecomeLeader, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse

LEMMA ContinuingLeaderElectionEvidence ==
    \A server \in Server:
        /\ TypeOK /\ [Next]_vars
        /\ state[server] = Leader /\ state'[server] = Leader
        => /\ ElectionConfig(log'[server], currentTerm'[server]) =
                  ElectionConfig(log[server], currentTerm[server])
           /\ votesGranted[server] \subseteq votesGranted'[server]
<1>clients. \A server, actor \in Server, payload \in ClientPayload:
        /\ TypeOK /\ ClientRequest(actor, payload)
        => /\ ElectionConfig(log'[server], currentTerm'[server]) =
                  ElectionConfig(log[server], currentTerm[server])
           /\ votesGranted[server] \subseteq votesGranted'[server]
    BY ClientRequestPreservesElectionConfig, SMT
    DEF TypeOK, ServerVarsTypeOK, CandidateVarsTypeOK, LogVarsTypeOK,
        ClientRequest
<1> QED BY <1>clients, ContinuingLeaderFrameExceptClientRequest, SMT
    DEF Next

LEMMA NewLeaderUsesBecomeLeader ==
    \A server \in Server:
        /\ TypeOK /\ [Next]_vars
        /\ state[server] # Leader /\ state'[server] = Leader
        => BecomeLeader(server)
    BY ServerStatesDistinct, MembershipMessageEndpoints, SMT
    DEF TypeOK, ServerVarsTypeOK, vars, Next, Restart, Timeout,
        ClientRequest, AdvanceCommitIndex, AppendEntries,
        LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse, BecomeLeader

LEMMA LeaderQuorumInvNext ==
    /\ TypeOK /\ CandidateCurrentTermFree /\ LeaderQuorumInv
    /\ [Next]_vars
    => LeaderQuorumInv'
<1> SUFFICES ASSUME TypeOK, CandidateCurrentTermFree, LeaderQuorumInv,
                      [Next]_vars, NEW server \in Server,
                      state'[server] = Leader
             PROVE \E quorum \in Quorums(
                         ElectionConfig(log'[server], currentTerm'[server])):
                       quorum \subseteq votesGranted'[server]
    BY SMT DEF LeaderQuorumInv
<1>continuing. CASE state[server] = Leader
    BY <1>continuing, ContinuingLeaderElectionEvidence, SMT DEF LeaderQuorumInv
<1>new. CASE state[server] # Leader
    <2>action. BecomeLeader(server)
        BY <1>new, NewLeaderUsesBecomeLeader, SMT
    <2>quorum.
            \E quorum \in Quorums(ElectionConfig(log[server], currentTerm[server])):
                quorum \subseteq votesGranted[server]
        BY <2>action, BecomeLeaderUsesElectionConfig, SMT
    <2> QED BY <2>action, <2>quorum, SMT DEF BecomeLeader
<1> QED BY <1>continuing, <1>new, SMT

\* These are fragments of the planned joint induction. TypeOK and log-term
\* bounds are explicit pre-state obligations, not assumed temporal theorems.
LEMMA MembershipElectionBaseInit == Init => MembershipElectionBase
    BY ServerStatesDistinct, SMT DEF Init, InitServerVars, MembershipElectionBase,
        CandidateCurrentTermFree, LeaderQuorumInv

LEMMA MembershipElectionBaseNext ==
    /\ TypeOK /\ LogTermBoundInv /\ MembershipElectionBase
    /\ [Next]_vars
    => MembershipElectionBase'
    BY CandidateCurrentTermFreeNext, LeaderQuorumInvNext, SMT
    DEF MembershipElectionBase

LEMMA WithMessagesTypeOK ==
    \A newMsgs \in SUBSET Message:
    \A msgs \in SUBSET Message:
        WithMessages(msgs, newMsgs) \subseteq Message
    BY SMT DEF WithMessages

LEMMA WithMessageTypeOK ==
    \A m \in Message:
    \A msgs \in SUBSET Message:
        WithMessage(m, msgs) \subseteq Message
    BY WithMessagesTypeOK, Zenon DEF WithMessage

LEMMA LastTermTypeOK ==
    \A l \in Seq(LogEntry): LastTerm(l) \in Nat
    BY SMT, ElementOfSeq, LenProperties DEF LastTerm, LogEntry

LEMMA SubSeqTypeOK ==
    \A entries \in Seq(LogEntry), first \in Nat \ {0}, last \in Nat:
        last <= Len(entries) => SubSeq(entries, first, last) \in Seq(LogEntry)
    BY SMT, ElementOfSeq, LenProperties, SubSeqProperties

LEMMA MessageVariantTypes ==
    /\ RequestVoteRequestMessage \subseteq Message
    /\ RequestVoteResponseMessage \subseteq Message
    /\ AppendEntriesRequestMessage \subseteq Message
    /\ AppendEntriesResponseMessage \subseteq Message
    BY SMT DEF Message

LEMMA MessageFieldsTypeOK ==
    \A m \in Message:
        /\ m.mterm \in Nat
        /\ m.msource \in Server
        /\ m.mdest \in Server
        /\ (m.mtype = RequestVoteRequest =>
            /\ m.mlastLogTerm \in Nat
            /\ m.mlastLogIndex \in Nat)
        /\ (m.mtype = RequestVoteResponse => m.mvoteGranted \in BOOLEAN)
        /\ (m.mtype = AppendEntriesRequest =>
            /\ m.mprevLogIndex \in Nat
            /\ m.mprevLogTerm \in Nat
            /\ m.mentries \in Seq(LogEntry)
            /\ m.mcommitIndex \in Nat)
        /\ (m.mtype = AppendEntriesResponse =>
            /\ m.msuccess \in BOOLEAN
            /\ m.mmatchIndex \in Nat)
<1> USE MessageTypesDistinct
<1>1. \A m \in Message:
        \/ m \in RequestVoteRequestMessage
        \/ m \in RequestVoteResponseMessage
        \/ m \in AppendEntriesRequestMessage
        \/ m \in AppendEntriesResponseMessage
    BY SMT DEF Message
<1> QED BY SMT, <1>1
    DEF MessageTypesDistinct, RequestVoteRequestMessage,
        RequestVoteResponseMessage, AppendEntriesRequestMessage,
        AppendEntriesResponseMessage

LEMMA RequestVoteRequestTypeOK ==
    \A term, lastTerm, lastIndex \in Nat:
    \A source, dest \in Server:
        [mtype         |-> RequestVoteRequest,
         mterm         |-> term,
         mlastLogTerm  |-> lastTerm,
         mlastLogIndex |-> lastIndex,
         msource       |-> source,
         mdest         |-> dest] \in Message
    BY SMT, MessageVariantTypes DEF RequestVoteRequestMessage

LEMMA RequestVoteRequestsTypeOK ==
    \A i \in Server, term \in Nat:
        log \in [Server -> Seq(LogEntry)] =>
            RequestVoteRequests(i, term) \subseteq Message
    BY LastTermTypeOK, LenProperties, RequestVoteRequestTypeOK, ConfigurationType, SMT
        DEF RequestVoteRequests, LastConfiguration

LEMMA RequestVoteResponseTypeOK ==
    \A term \in Nat, granted \in BOOLEAN:
    \A source, dest \in Server:
        [mtype        |-> RequestVoteResponse,
         mterm        |-> term,
         mvoteGranted |-> granted,
         msource      |-> source,
         mdest        |-> dest] \in Message
    BY SMT, MessageVariantTypes DEF RequestVoteResponseMessage

LEMMA AppendEntriesRequestTypeOK ==
    \A term, prevIndex, prevTerm, committed \in Nat:
    \A entries \in Seq(LogEntry):
    \A source, dest \in Server:
        [mtype         |-> AppendEntriesRequest,
         mterm         |-> term,
         mprevLogIndex |-> prevIndex,
         mprevLogTerm  |-> prevTerm,
         mentries      |-> entries,
         mcommitIndex  |-> committed,
         msource       |-> source,
         mdest         |-> dest] \in Message
    BY SMT, MessageVariantTypes DEF AppendEntriesRequestMessage

LEMMA AppendEntriesPrevLogTermTypeOK ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => AppendEntriesPrevLogTerm(i, j) \in Nat
    BY SMT, ElementOfSeq, LenProperties
    DEF AppendEntriesPrevLogTerm, NextIndexBound, TypeOK,
        LeaderVarsTypeOK, LogVarsTypeOK, LogEntry

LEMMA AppendEntriesLastEntryTypeOK ==
    \A i, j \in Server:
        TypeOK =>
            /\ AppendEntriesLastEntry(i, j) \in Nat
            /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY SMT, MinTypeOK, LenProperties
    DEF AppendEntriesLastEntry, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK

LEMMA AppendEntriesEntriesTypeOK ==
    \A i, j \in Server:
        TypeOK => AppendEntriesEntries(i, j) \in Seq(LogEntry)
    BY SMT, AppendEntriesLastEntryTypeOK, SubSeqTypeOK
    DEF AppendEntriesEntries, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK

LEMMA AppendEntriesMessageTypeOK ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => AppendEntriesMessage(i, j) \in Message
<1>prev_log_index. \A i, j \in Server:
        TypeOK => nextIndex[i][j] - 1 \in Nat
    BY SMT DEF TypeOK, LeaderVarsTypeOK
<1> QED BY SMT, <1>prev_log_index, AppendEntriesPrevLogTermTypeOK,
        AppendEntriesLastEntryTypeOK, AppendEntriesEntriesTypeOK,
        MinTypeOK, AppendEntriesRequestTypeOK
    DEF AppendEntriesMessage, TypeOK, ServerVarsTypeOK, LogVarsTypeOK

LEMMA AppendEntriesResponseTypeOK ==
    \A term, matched \in Nat, success \in BOOLEAN:
    \A source, dest \in Server:
        [mtype       |-> AppendEntriesResponse,
         mterm       |-> term,
         msuccess    |-> success,
         mmatchIndex |-> matched,
         msource     |-> source,
         mdest       |-> dest] \in Message
    BY SMT, MessageVariantTypes DEF AppendEntriesResponseMessage

LEMMA TimeoutMsgTypeOK ==
    \A i \in Server: TypeOK /\ Timeout(i) => MsgTypeOK'
<1> USE DEF Timeout, TypeOK, MsgTypeOK, ServerVarsTypeOK,
        LogVarsTypeOK
<1>requests. \A i \in Server:
        TypeOK /\ Timeout(i) =>
            RequestVoteRequests(i, currentTerm[i] + 1) \in SUBSET Message
    BY SMT, RequestVoteRequestsTypeOK
<1> QED BY SMT, <1>requests, WithMessagesTypeOK

LEMMA UnchangedMessagesMsgTypeOK ==
    TypeOK /\ UNCHANGED messages => MsgTypeOK'
    BY SMT DEF TypeOK, MsgTypeOK

LEMMA HandleRequestVoteRequestMsgTypeOK ==
    \A i, j \in Server, m \in messages:
        TypeOK /\ HandleRequestVoteRequest(i, j, m) => MsgTypeOK'
    BY SMT, RequestVoteResponseTypeOK, WithMessageTypeOK
    DEF HandleRequestVoteRequest, Send, TypeOK, MsgTypeOK,
        ServerVarsTypeOK

LEMMA HandleAppendEntriesRequestMsgTypeOK ==
    \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
        => MsgTypeOK'
<1>rejected. \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ Send([mtype       |-> AppendEntriesResponse,
                  mterm       |-> currentTerm[i],
                  msuccess    |-> FALSE,
                  mmatchIndex |-> 0,
                  msource     |-> i,
                  mdest       |-> j])
        => MsgTypeOK'
    <2>response. \A i, j \in Server:
            ServerVarsTypeOK =>
                [mtype       |-> AppendEntriesResponse,
                 mterm       |-> currentTerm[i],
                 msuccess    |-> FALSE,
                 mmatchIndex |-> 0,
                 msource     |-> i,
                 mdest       |-> j] \in Message
        BY AppendEntriesResponseTypeOK, Isa DEF ServerVarsTypeOK
    <2> QED BY SMT, <2>response, WithMessageTypeOK
        DEF Send, TypeOK, MsgTypeOK, ServerVarsTypeOK
<1>accepted. \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ Send([mtype       |-> AppendEntriesResponse,
                  mterm       |-> currentTerm[i],
                  msuccess    |-> TRUE,
                  mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                  msource     |-> i,
                  mdest       |-> j])
        => MsgTypeOK'
    <2>response. \A i, j \in Server, m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            => [mtype       |-> AppendEntriesResponse,
                mterm       |-> currentTerm[i],
                msuccess    |-> TRUE,
                mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                msource     |-> i,
                mdest       |-> j] \in Message
        <3>fields. \A i, j \in Server, m \in messages:
                /\ TypeOK
                /\ m.mtype = AppendEntriesRequest
                => /\ currentTerm[i] \in Nat
                   /\ m.mprevLogIndex \in Nat
                   /\ m.mentries \in Seq(LogEntry)
                   /\ Len(m.mentries) \in Nat
                   /\ m.mprevLogIndex + Len(m.mentries) \in Nat
            BY SMT, MessageFieldsTypeOK, LenProperties
            DEF TypeOK, MsgTypeOK, ServerVarsTypeOK
        <3> QED BY SMT, <3>fields, AppendEntriesResponseTypeOK
    <2> QED BY SMT, <2>response, WithMessageTypeOK
        DEF Send, TypeOK, MsgTypeOK
<1> QED BY SMT, <1>rejected, <1>accepted
    DEF HandleAppendEntriesRequest

LEMMA ReceiveMsgTypeOK ==
    \A m \in messages: TypeOK /\ Receive(m) => MsgTypeOK'
<1> USE DEF Receive, HandleMsg
<1> QED BY SMT, UnchangedMessagesMsgTypeOK,
        HandleRequestVoteRequestMsgTypeOK,
        HandleAppendEntriesRequestMsgTypeOK, MessageFieldsTypeOK
    DEF UpdateTerm, HandleRequestVoteResponse,
        HandleAppendEntriesResponse, TypeOK, MsgTypeOK

LEMMA MsgTypeOKNext ==
    /\ TypeOK
    /\ NextIndexBound
    /\ [Next]_vars
    => MsgTypeOK'
<1> USE DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        CandidateVarsTypeOK, LeaderVarsTypeOK, LogVarsTypeOK, Message, LogEntry
<1>unchanged.
        /\ TypeOK
        /\ \/ UNCHANGED vars
           \/ \E i \in Server: Restart(i) \/ BecomeLeader(i)
                               \/ AdvanceCommitIndex(i) \/ LeaderStepDown(i)
           \/ \E i \in Server, payload \in ClientPayload: ClientRequest(i, payload)
        => MsgTypeOK'
    BY SMT DEF vars, Restart, BecomeLeader, AdvanceCommitIndex,
        LeaderStepDown, ClientRequest
<1> USE DEF Send, WithMessages, RequestVoteRequests
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => MsgTypeOK'
    BY SMT, TimeoutMsgTypeOK DEF Timeout
<1>append_entries. \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ AppendEntries(i, j)
        => MsgTypeOK'
    BY SMT, AppendEntriesMessageTypeOK, WithMessageTypeOK DEF AppendEntries
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => MsgTypeOK'
    BY SMT, ReceiveMsgTypeOK DEF Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1> QED BY SMT, <1>unchanged, <1>timeout, <1>append_entries, <1>receive
    DEF Next, vars

LEMMA ServerVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => ServerVarsTypeOK'
    BY SMT, MessageFieldsTypeOK
    DEF Next, vars, Timeout, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, ServerVarsTypeOK

LEMMA CandidateVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => CandidateVarsTypeOK'
    BY SMT, MessageFieldsTypeOK
    DEF Next, vars, Timeout, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, CandidateVarsTypeOK

LEMMA LeaderVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => LeaderVarsTypeOK'
<1> USE DEF TypeOK, MsgTypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>stutter. TypeOK /\ UNCHANGED vars => LeaderVarsTypeOK'
    BY SMT DEF vars
<1>restart. \A i \in Server:
        TypeOK /\ Restart(i) => LeaderVarsTypeOK'
    BY SMT DEF Restart
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => LeaderVarsTypeOK'
    BY SMT DEF Timeout
<1>leader. \A i \in Server:
        TypeOK /\ BecomeLeader(i) => LeaderVarsTypeOK'
    <2>length. \A i \in Server:
            TypeOK =>
                /\ Len(log[i]) \in Nat
                /\ Len(log[i]) + 1 \in Nat \ {0}
        BY SMT, LenProperties DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>length, SMTT(20) DEF BecomeLeader
<1>client_request. \A i \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(i, payload) => LeaderVarsTypeOK'
    BY SMT DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => LeaderVarsTypeOK'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        TypeOK /\ AppendEntries(i, j) => LeaderVarsTypeOK'
    BY SMT DEF AppendEntries
<1>step_down. \A i \in Server:
        TypeOK /\ LeaderStepDown(i) => LeaderVarsTypeOK'
    BY SMT DEF LeaderStepDown
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => LeaderVarsTypeOK'
    BY SMT, MessageFieldsTypeOK, MaxTypeOK DEF Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1> QED BY SMT, <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next

LEMMA AgreeIndexesTypeOK ==
    \A i \in Server:
        TypeOK =>
            /\ Len(log[i]) \in Nat
            /\ AgreeIndexes(i) \in SUBSET (0..Len(log[i]))
    BY SMT, LenProperties
    DEF AgreeIndexes, TypeOK, LogVarsTypeOK

LEMMA MaxAgreeIndexesTypeOK ==
    \A i \in Server:
        /\ TypeOK
        /\ AgreeIndexes(i) # {}
        => /\ Max(AgreeIndexes(i)) \in AgreeIndexes(i)
           /\ Max(AgreeIndexes(i)) \in Nat
    BY AgreeIndexesTypeOK, BoundedIndexMaxProperties, SMT

LEMMA NewCommitIndexTypeOK ==
    \A i \in Server: TypeOK => NewCommitIndex(i) \in Nat
    BY SMT, MaxAgreeIndexesTypeOK
    DEF NewCommitIndex, TypeOK, LogVarsTypeOK

LEMMA ClientRequestLogTypeOK ==
    \A i \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(i, payload) => LogVarsTypeOK'
    BY ClientRequestAppendsCurrentTerm, AppendProperties, SMT
    DEF TypeOK, LogVarsTypeOK, ClientRequest

LEMMA UnchangedLogVarsTypeOK ==
    TypeOK /\ UNCHANGED <<log, commitIndex>> => LogVarsTypeOK'
    BY SMT DEF TypeOK, LogVarsTypeOK

LEMMA HandleAppendEntriesRequestLogVarsTypeOK ==
    \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
        => LogVarsTypeOK'
<1>commit_index. \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
        => commitIndex' \in [Server -> Nat]
    BY SMT, MessageFieldsTypeOK DEF TypeOK, MsgTypeOK, LogVarsTypeOK
<1>log. \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ m.mentries # << >>
        /\ \/ Len(log[i]) = m.mprevLogIndex
           \/ /\ Len(log[i]) >= m.mprevLogIndex + 1
        /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])]
        => log' \in [Server -> Seq(LogEntry)]
    <2>entry. \A m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ m.mentries # << >>
            => m.mentries[1] \in LogEntry
        BY SMT, MessageFieldsTypeOK, EmptySeq, ElementOfSeq
        DEF TypeOK, MsgTypeOK
    <2>updated_log. \A i \in Server, m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ m.mentries # << >>
            /\ \/ Len(log[i]) = m.mprevLogIndex
               \/ /\ Len(log[i]) >= m.mprevLogIndex + 1
            /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])]
            => /\ Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1]) \in Seq(LogEntry)
        BY SMT, <2>entry, AppendProperties, SubSeqTypeOK, MessageFieldsTypeOK
        DEF TypeOK, LogVarsTypeOK, MsgTypeOK, ServerOK
    <2> QED BY SMT, <2>updated_log DEF TypeOK, LogVarsTypeOK
<1> QED BY SMT, <1>commit_index, <1>log, UnchangedLogVarsTypeOK, MessageFieldsTypeOK, ServerStatesDistinct
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK, MsgTypeOK

LEMMA ReceiveLogVarsTypeOK ==
    \A m \in messages: TypeOK /\ Receive(m) => LogVarsTypeOK'
    BY SMT, HandleAppendEntriesRequestLogVarsTypeOK, UnchangedLogVarsTypeOK,
        MessageFieldsTypeOK
    DEF Receive, HandleMsg, UpdateTerm, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, LogVarsTypeOK

LEMMA LogVarsTypeOKNext == TypeOK /\ [Next]_vars => LogVarsTypeOK'
<1> USE DEF TypeOK, LogVarsTypeOK
<1>unchanged.
        /\ TypeOK
        /\ \/ UNCHANGED vars
           \/ \E i \in Server: Restart(i) \/ Timeout(i) \/ BecomeLeader(i)
                               \/ LeaderStepDown(i)
           \/ \E i, j \in Server: AppendEntries(i, j)
        => LogVarsTypeOK'
    BY SMT DEF vars, Restart, Timeout, BecomeLeader,
        LeaderStepDown, AppendEntries
<1>client_request. \A i \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(i, payload) => LogVarsTypeOK'
    BY SMT, ClientRequestLogTypeOK
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => LogVarsTypeOK'
    BY SMT, NewCommitIndexTypeOK DEF AdvanceCommitIndex
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => LogVarsTypeOK'
    BY SMT, ReceiveLogVarsTypeOK
<1> QED BY SMT, <1>unchanged, <1>client_request, <1>commit, <1>receive
    DEF Next, vars

LEMMA TypeOKInit == Init => TypeOK
    BY SMT DEF Init, InitServerVars, InitCandidateVars, InitLeaderVars,
        InitLogVars, TypeOK, MsgTypeOK, ServerVarsTypeOK, CandidateVarsTypeOK,
        LeaderVarsTypeOK, LogVarsTypeOK

LEMMA TypeOKNext ==
    /\ TypeOK
    /\ NextIndexBound
    /\ [Next]_vars
    => TypeOK'
    BY SMT, MsgTypeOKNext, ServerVarsTypeOKNext, CandidateVarsTypeOKNext,
        LeaderVarsTypeOKNext, LogVarsTypeOKNext
        DEF TypeOK

LEMMA ClientRequestDoesNotShrinkLogs ==
    \A i \in Server, payload \in ClientPayload:
        TypeOK /\ ClientRequest(i, payload) =>
            /\ LogVarsTypeOK'
            /\ \A k \in Server: Len(log[k]) <= Len(log'[k])
    BY ClientRequestLogTypeOK, ClientRequestAppendsCurrentTerm,
       AppendProperties, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK, ClientRequest

LEMMA AppendEntriesMessageIndexBound ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => nextIndex[i][j] - 1 + Len(AppendEntriesEntries(i, j))
            <= Len(log[i])
    BY SMT, AppendEntriesLastEntryTypeOK, SubSeqProperties, LenProperties
    DEF AppendEntriesEntries,
        AppendEntriesLastEntry, NextIndexBound, TypeOK, LeaderVarsTypeOK,
        LogVarsTypeOK

LEMMA StoredMessageFieldsTypeOK ==
    TypeOK =>
        \A m \in messages:
            /\ m.msource \in Server
            /\ m.mdest \in Server
    BY SMT, MessageFieldsTypeOK DEF TypeOK, MsgTypeOK

LEMMA NonShrinkingLogsPreserveRequestIndexBound ==
    /\ TypeOK
    /\ RequestIndexBound
    /\ UNCHANGED <<messages, currentTerm, state>>
    /\ LogVarsTypeOK'
    /\ \A k \in Server: Len(log[k]) <= Len(log'[k])
    => RequestIndexBound'
<1> SUFFICES ASSUME TypeOK, RequestIndexBound,
                      UNCHANGED <<messages, currentTerm, state>>,
                      LogVarsTypeOK',
                      \A k \in Server: Len(log[k]) <= Len(log'[k]),
                      NEW m \in messages',
                      m.mtype = AppendEntriesRequest,
                      m.mterm = currentTerm'[m.msource],
                      state'[m.msource] \in {Candidate, Leader}
             PROVE  m.mprevLogIndex + Len(m.mentries)
                    <= Len(log'[m.msource])
    BY SMT DEF RequestIndexBound
<1>1. m \in messages /\ m.msource \in Server
    BY SMT, StoredMessageFieldsTypeOK
<1>2. m.mprevLogIndex + Len(m.mentries) <= Len(log[m.msource])
    BY SMT, <1>1 DEF RequestIndexBound
<1>3. Len(log[m.msource]) <= Len(log'[m.msource])
    BY SMT, <1>1
<1>4. /\ m.mprevLogIndex \in Nat
       /\ Len(m.mentries) \in Nat
       /\ Len(log[m.msource]) \in Nat
       /\ Len(log'[m.msource]) \in Nat
    BY SMT, <1>1, MessageFieldsTypeOK, LenProperties
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY SMT, <1>2, <1>3, <1>4, NatLeqTransitive

LEMMA NonShrinkingLogsPreserveResponseIndexBound ==
    /\ TypeOK
    /\ ResponseIndexBound
    /\ UNCHANGED <<messages, currentTerm, state>>
    /\ LogVarsTypeOK'
    /\ \A k \in Server: Len(log[k]) <= Len(log'[k])
    => ResponseIndexBound'
<1> SUFFICES ASSUME TypeOK, ResponseIndexBound,
                      UNCHANGED <<messages, currentTerm, state>>,
                      LogVarsTypeOK',
                      \A k \in Server: Len(log[k]) <= Len(log'[k]),
                      NEW m \in messages',
                      m.mtype = AppendEntriesResponse,
                      m.mterm = currentTerm'[m.mdest],
                      state'[m.mdest] \in {Candidate, Leader}
             PROVE  m.mmatchIndex <= Len(log'[m.mdest])
    BY SMT DEF ResponseIndexBound
<1>1. m \in messages /\ m.mdest \in Server
    BY SMT, StoredMessageFieldsTypeOK
<1>2. m.mmatchIndex <= Len(log[m.mdest])
    BY SMT, <1>1 DEF ResponseIndexBound
<1>3. Len(log[m.mdest]) <= Len(log'[m.mdest])
    BY SMT, <1>1
<1>4. /\ m.mmatchIndex \in Nat
       /\ Len(log[m.mdest]) \in Nat
       /\ Len(log'[m.mdest]) \in Nat
    BY SMT, <1>1, MessageFieldsTypeOK, LenProperties
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY SMT, <1>2, <1>3, <1>4, NatLeqTransitive

LEMMA NonShrinkingLogsPreserveNextIndexBound ==
    /\ TypeOK
    /\ NextIndexBound
    /\ UNCHANGED <<state, nextIndex, matchIndex>>
    /\ LogVarsTypeOK'
    /\ \A k \in Server: Len(log[k]) <= Len(log'[k])
    => NextIndexBound'
<1> SUFFICES ASSUME TypeOK, NextIndexBound,
                      UNCHANGED <<state, nextIndex, matchIndex>>, LogVarsTypeOK',
                      \A k \in Server: Len(log[k]) <= Len(log'[k]),
                      NEW i \in Server, NEW j \in Server,
                      state'[i] = Leader
             PROVE  /\ nextIndex'[i][j] <= Len(log'[i]) + 1
                    /\ matchIndex'[i][j] <= Len(log'[i])
    BY SMT DEF NextIndexBound
<1>1. /\ nextIndex[i][j] <= Len(log[i]) + 1
       /\ matchIndex[i][j] <= Len(log[i])
    BY SMT DEF NextIndexBound
<1>2. Len(log[i]) <= Len(log'[i])
    BY SMT
<1>3. /\ nextIndex[i][j] \in Nat
       /\ matchIndex[i][j] \in Nat
       /\ Len(log[i]) \in Nat
       /\ Len(log'[i]) \in Nat
    BY SMT, LenProperties
    DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1> QED BY SMT, <1>1, <1>2, <1>3, NatLeqTransitive

LEMMA TimeoutDoesNotDecreaseTerms ==
    \A i \in Server:
        ServerVarsTypeOK /\ Timeout(i) =>
            \A k \in Server: currentTerm[k] <= currentTerm'[k]
    BY SMT DEF ServerVarsTypeOK, Timeout

LEMMA TimeoutPreservesAppendEntriesMessages ==
    \A i \in Server:
        Timeout(i) =>
            \A m:
                /\ m \in messages'
                /\ m.mtype \in {AppendEntriesRequest, AppendEntriesResponse}
                => m \in messages
<1>1. \A i \in Server: \A m:
        Timeout(i) /\ m \in messages' =>
            m \in messages \/ m \in RequestVoteRequests(i, currentTerm[i] + 1)
    BY SMT DEF Timeout, WithMessages
<1>2. \A i \in Server:
        \A m \in RequestVoteRequests(i, currentTerm[i] + 1):
            m.mtype = RequestVoteRequest
    BY SMT DEF RequestVoteRequests
<1>3. RequestVoteRequest
        \notin {AppendEntriesRequest, AppendEntriesResponse}
    BY SMT, MessageTypesDistinct DEF MessageTypesDistinct
<1> QED BY SMT, <1>1, <1>2, <1>3

LEMMA HandleAppendEntriesRequestPreservesOtherServer ==
    \A m \in messages, k \in Server:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        /\ k # m.mdest
        => /\ currentTerm'[k] = currentTerm[k]
           /\ state'[k] = state[k]
           /\ log'[k] = log[k]
    BY SMT, MessageFieldsTypeOK
    DEF HandleAppendEntriesRequest, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, LogVarsTypeOK

LEMMA HandleAppendEntriesRequestPreservesActiveRecipient ==
    \A m \in messages:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        /\ state'[m.mdest] \in {Candidate, Leader}
        => /\ currentTerm'[m.mdest] = currentTerm[m.mdest]
           /\ state'[m.mdest] = state[m.mdest]
           /\ log'[m.mdest] = log[m.mdest]
    BY SMT, ServerStatesDistinct, MessageFieldsTypeOK
    DEF HandleAppendEntriesRequest, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, LogVarsTypeOK,
        ServerStatesDistinct

LEMMA SendInvariantNext ==
    /\ SendInvariant
    /\ TypeOK
    /\ [Next]_vars
    => SendInvariant'
BY SMT, MessageFieldsTypeOK
DEF Next, Restart, Timeout, BecomeLeader, ClientRequest,
    AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
    HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
    HandleAppendEntriesRequest, HandleAppendEntriesResponse,
    Send, WithMessage, WithMessages, RequestVoteRequests,
    AppendEntriesMessage, vars, TypeOK, MsgTypeOK, ServerVarsTypeOK,
    SendInvariant, MessageTypesDistinct

LEMMA RequestIndexBoundNext ==
    /\ RequestIndexBound
    /\ NextIndexBound
    /\ SendInvariant
    /\ TypeOK
    /\ [Next]_vars
    => RequestIndexBound'
<1> USE ServerStatesDistinct, MessageTypesDistinct
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        SendInvariant, NextIndexBound, RequestIndexBound,
        ServerStatesDistinct
<1>stutter. RequestIndexBound /\ TypeOK /\ UNCHANGED vars => RequestIndexBound'
    BY SMT DEF vars
<1>restart. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ Restart(i) => RequestIndexBound'
    BY SMT, MessageFieldsTypeOK DEF Restart
<1>timeout. \A i \in Server:
            /\ RequestIndexBound
            /\ TypeOK
            /\ SendInvariant
            /\ Timeout(i)
            => RequestIndexBound'
    BY SMT, TimeoutPreservesAppendEntriesMessages, MessageFieldsTypeOK
    DEF Timeout
<1>leader. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ BecomeLeader(i) => RequestIndexBound'
    BY SMT, MessageFieldsTypeOK DEF BecomeLeader
<1>client_request. \A i \in Server, payload \in ClientPayload:
        RequestIndexBound /\ TypeOK /\ ClientRequest(i, payload) => RequestIndexBound'
    BY SMT, ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveRequestIndexBound
    DEF  ClientRequest
<1>commit. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => RequestIndexBound'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        /\ NextIndexBound
        /\ RequestIndexBound
        /\ TypeOK
        /\ AppendEntries(i, j)
        => RequestIndexBound'
    BY SMT, AppendEntriesMessageIndexBound
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ LeaderStepDown(i) => RequestIndexBound'
    BY SMT, MessageFieldsTypeOK DEF LeaderStepDown
<1>receive. \A m \in messages:
        RequestIndexBound /\ TypeOK /\ Receive(m) => RequestIndexBound'
    <2>update_term. \A m \in messages:
            RequestIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                RequestIndexBound'
        BY SMT, MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY SMT, MessageFieldsTypeOK
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages,
            MessageTypesDistinct
    <2>request_vote_response. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY SMT DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => RequestIndexBound'
        <3> SUFFICES ASSUME NEW m \in messages, 
                            RequestIndexBound, TypeOK,
                            m.mtype = AppendEntriesRequest,
                            HandleAppendEntriesRequest(m.mdest, m.msource, m),
                            NEW q \in messages',
                            q.mtype = AppendEntriesRequest,
                            q.mterm = currentTerm'[q.msource],
                            state'[q.msource] \in {Candidate, Leader}
                   PROVE  q.mprevLogIndex + Len(q.mentries)
                          <= Len(log'[q.msource])
            BY SMT DEF RequestIndexBound
        <3>1. q \in messages /\ q.msource \in Server
            BY SMT, MessageFieldsTypeOK
            DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
                TypeOK, MsgTypeOK, MessageTypesDistinct
        <3>same_server. CASE q.msource = m.mdest
            BY SMT, <3>same_server, <3>1, MessageFieldsTypeOK
            DEF HandleAppendEntriesRequest, TypeOK,
                MsgTypeOK, RequestIndexBound, ServerStatesDistinct
        <3>other_server. CASE q.msource # m.mdest
            <4> USE <3>other_server, <3>1
            <4>1. /\ currentTerm'[q.msource] = currentTerm[q.msource]
                  /\ state'[q.msource] = state[q.msource]
                  /\ log'[q.msource] = log[q.msource]
                BY SMT, HandleAppendEntriesRequestPreservesOtherServer
            <4>2. q.mprevLogIndex + Len(q.mentries)
                    <= Len(log[q.msource])
                BY SMT, <3>1, <4>1 DEF RequestIndexBound
            <4> QED BY SMT, <4>1, <4>2
        <3> QED BY SMT, <3>same_server, <3>other_server
    <2>append_entries_response. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY SMT DEF HandleAppendEntriesResponse
    <2> QED BY SMT, <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY SMT, <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next, vars

LEMMA ResponseTermBoundNext ==
    /\ ResponseTermBound
    /\ SendInvariant
    /\ TypeOK
    /\ [Next]_vars
    => ResponseTermBound'
<1> USE ServerStatesDistinct, MessageTypesDistinct
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        SendInvariant, ResponseTermBound
<1>stutter. ResponseTermBound /\ TypeOK /\ UNCHANGED vars => ResponseTermBound'
    BY SMT DEF vars
<1>restart. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ Restart(i) => ResponseTermBound'
    BY SMT DEF Restart
<1>timeout. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ Timeout(i) => ResponseTermBound'
    BY SMT, TimeoutPreservesAppendEntriesMessages, TimeoutDoesNotDecreaseTerms,
        MessageFieldsTypeOK DEF Timeout
<1>leader. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ BecomeLeader(i) => ResponseTermBound'
    BY SMT DEF BecomeLeader
<1>client_request. \A i \in Server, payload \in ClientPayload:
        ResponseTermBound /\ TypeOK /\ ClientRequest(i, payload) => ResponseTermBound'
    BY SMT DEF ClientRequest
<1>commit. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ AdvanceCommitIndex(i) => ResponseTermBound'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        ResponseTermBound /\ TypeOK /\ AppendEntries(i, j) => ResponseTermBound'
    BY SMT, MessageFieldsTypeOK
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ LeaderStepDown(i) => ResponseTermBound'
    BY SMT DEF LeaderStepDown
<1>receive. \A m \in messages:
        /\ ResponseTermBound
        /\ TypeOK
        /\ SendInvariant
        /\ Receive(m)
        => ResponseTermBound'
    BY SMT, MessageFieldsTypeOK
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages,
        MessageTypesDistinct
<1> QED BY SMT, <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA ResponseIndexBoundNext ==
    /\ ResponseTermBound
    /\ RequestIndexBound
    /\ ResponseIndexBound
    /\ TypeOK
    /\ [Next]_vars
    => ResponseIndexBound'
<1> USE ServerStatesDistinct, MessageTypesDistinct
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        RequestIndexBound, ResponseTermBound,
        ResponseIndexBound
<1>stutter. ResponseIndexBound /\ TypeOK /\ UNCHANGED vars => ResponseIndexBound'
    BY SMT DEF vars
<1>restart. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ Restart(i) => ResponseIndexBound'
    BY SMT, MessageFieldsTypeOK DEF Restart
<1>timeout. \A i \in Server:
        ResponseTermBound /\ ResponseIndexBound /\ TypeOK /\ Timeout(i) => ResponseIndexBound'
    <2>same_server. ASSUME NEW i \in Server, NEW m \in messages,
                            ResponseTermBound, ResponseIndexBound, 
                            TypeOK, Timeout(i), m.mdest = i,
                            m.mtype = AppendEntriesResponse,
                            m.mterm = currentTerm'[m.mdest],
                            state'[m.mdest] \in {Candidate, Leader}
                    PROVE  m.mmatchIndex <= Len(log'[m.mdest])
        <3>zero. m.mmatchIndex = 0 =>
                m.mmatchIndex <= Len(log'[m.mdest])
            BY SMT, <2>same_server, MessageFieldsTypeOK, LenProperties
            DEF TypeOK, MsgTypeOK, LogVarsTypeOK, Timeout
        <3>positive. m.mmatchIndex > 0 => FALSE
            BY SMT, <2>same_server, TimeoutDoesNotDecreaseTerms, MessageFieldsTypeOK
            DEF Timeout, TypeOK, MsgTypeOK, ResponseTermBound
        <3> QED BY SMT, <2>same_server, <3>zero, <3>positive, MessageFieldsTypeOK DEF TypeOK, MsgTypeOK
    <2>other_server. \A i \in Server, m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ Timeout(i)
            /\ m.mdest # i
            /\ m.mtype = AppendEntriesResponse
            /\ m.mterm = currentTerm'[m.mdest]
            /\ state'[m.mdest] \in {Candidate, Leader}
            => m.mmatchIndex <= Len(log'[m.mdest])
        BY SMT, MessageFieldsTypeOK
        DEF Timeout, TypeOK, MsgTypeOK, ResponseIndexBound
    <2> QED BY SMT, <2>same_server, <2>other_server,
        TimeoutPreservesAppendEntriesMessages, MessageFieldsTypeOK
        DEF ResponseIndexBound
<1>leader. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ BecomeLeader(i) => ResponseIndexBound'
    BY SMT, MessageFieldsTypeOK DEF BecomeLeader
<1>client_request. \A i \in Server, payload \in ClientPayload:
        ResponseIndexBound /\ TypeOK /\ ClientRequest(i, payload) => ResponseIndexBound'
    BY SMT, ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveResponseIndexBound
    DEF ClientRequest
<1>commit. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => ResponseIndexBound'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        ResponseIndexBound /\ TypeOK /\ AppendEntries(i, j) => ResponseIndexBound'
    BY SMT, MessageFieldsTypeOK
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ LeaderStepDown(i) => ResponseIndexBound'
    BY SMT, MessageFieldsTypeOK DEF LeaderStepDown
<1>receive. \A m \in messages:
        RequestIndexBound /\ ResponseIndexBound /\ TypeOK /\ Receive(m) => ResponseIndexBound'
    <2>update_term. \A m \in messages:
            ResponseIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                ResponseIndexBound'
        BY SMT, MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY SMT, MessageFieldsTypeOK
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages,
            MessageTypesDistinct
    <2>request_vote_response. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY SMT DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ RequestIndexBound
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => ResponseIndexBound'
        <3> SUFFICES ASSUME NEW m \in messages, 
                            RequestIndexBound, ResponseIndexBound, TypeOK,
                            m.mtype = AppendEntriesRequest,
                            HandleAppendEntriesRequest(m.mdest, m.msource, m),
                            NEW q \in messages',
                            q.mtype = AppendEntriesResponse,
                            q.mterm = currentTerm'[q.mdest],
                            state'[q.mdest] \in {Candidate, Leader}
                   PROVE  q.mmatchIndex <= Len(log'[q.mdest])
            BY SMT DEF ResponseIndexBound
        <3>old_response. CASE q \in messages
            <4> USE <3>old_response
            <4>same_server. CASE q.mdest = m.mdest
                BY SMT, <4>same_server, HandleAppendEntriesRequestPreservesActiveRecipient, MessageFieldsTypeOK
                DEF TypeOK, MsgTypeOK, ResponseIndexBound
            <4>other_server. CASE q.mdest # m.mdest
                BY SMT, <4>other_server, HandleAppendEntriesRequestPreservesOtherServer, MessageFieldsTypeOK
                DEF TypeOK, MsgTypeOK, ResponseIndexBound
            <4> QED BY SMT, <4>same_server, <4>other_server
        <3>new_response. CASE q \notin messages
            <4> USE <3>new_response
            <4>location. /\ q.mdest = m.msource
                         /\ currentTerm'[q.mdest] = currentTerm[q.mdest]
                         /\ state'[q.mdest] = state[q.mdest]
                         /\ log'[q.mdest] = log[q.mdest]
                BY SMT, HandleAppendEntriesRequestPreservesOtherServer,
                    MessageFieldsTypeOK
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK
            <4>zero. q.mmatchIndex = 0 =>
                    q.mmatchIndex <= Len(log'[q.mdest])
                BY SMT, <4>location, MessageFieldsTypeOK, LenProperties
                DEF TypeOK, MsgTypeOK, LogVarsTypeOK
            <4>positive. q.mmatchIndex > 0 =>
                    q.mmatchIndex <= Len(log'[q.mdest])
                BY SMT, <4>location, MessageFieldsTypeOK, LenProperties
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK,
                    RequestIndexBound
            <4>cases. q.mmatchIndex = 0 \/ q.mmatchIndex > 0
                BY SMT, MessageFieldsTypeOK
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK
            <4> QED BY SMT, <4>zero, <4>positive, <4>cases
        <3> QED BY SMT, <3>old_response, <3>new_response
    <2>append_entries_response. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY SMT DEF HandleAppendEntriesResponse
    <2> QED BY SMT, <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY SMT, <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA NextIndexBoundNext ==
    (/\ ResponseIndexBound
     /\ NextIndexBound
     /\ TypeOK
     /\ [Next]_vars) => NextIndexBound'
<1> USE ServerStatesDistinct
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        LeaderVarsTypeOK, LogVarsTypeOK, ResponseIndexBound, NextIndexBound
<1>stutter. NextIndexBound /\ TypeOK /\ UNCHANGED vars => NextIndexBound'
    BY SMT DEF vars
<1>restart. \A i \in Server:
        NextIndexBound /\ TypeOK /\ Restart(i) => NextIndexBound'
    BY SMT, LenProperties DEF Restart
<1>timeout. \A i \in Server:
        NextIndexBound /\ TypeOK /\ Timeout(i) => NextIndexBound'
    BY SMT, ServerStatesDistinct, LenProperties
    DEF Timeout, NextIndexBound
<1>leader. \A i \in Server:
        NextIndexBound /\ TypeOK /\ BecomeLeader(i) => NextIndexBound'
    BY LenProperties, SMTT(20) DEF BecomeLeader
<1>client_request. \A i \in Server, payload \in ClientPayload:
        NextIndexBound /\ TypeOK /\ ClientRequest(i, payload) => NextIndexBound'
    BY SMT, ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveNextIndexBound
    DEF ClientRequest
<1>commit. \A i \in Server:
        NextIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => NextIndexBound'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        NextIndexBound /\ TypeOK /\ AppendEntries(i, j) => NextIndexBound'
    BY SMT DEF AppendEntries
<1>step_down. \A i \in Server:
        NextIndexBound /\ TypeOK /\ LeaderStepDown(i) => NextIndexBound'
    BY SMT DEF LeaderStepDown
<1>receive. \A m \in messages:
        ResponseIndexBound /\ NextIndexBound
            /\ TypeOK /\ Receive(m) => NextIndexBound'
    <2>update_term. \A m \in messages:
            NextIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                NextIndexBound'
        BY SMT, MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => NextIndexBound'
        BY SMT DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => NextIndexBound'
        BY SMT DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => NextIndexBound'
        BY SMT, MessageFieldsTypeOK DEF HandleAppendEntriesRequest
    <2>append_entries_response. \A m \in messages:

            /\ ResponseIndexBound
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => NextIndexBound'
        <3> SUFFICES ASSUME NEW m \in messages,
                            ResponseIndexBound,
                            NextIndexBound,
                            TypeOK,
                            m.mtype = AppendEntriesResponse,
                            HandleAppendEntriesResponse(
                                m.mdest, m.msource, m),
                            NEW i \in Server, NEW j \in Server,
                            state'[i] = Leader
                   PROVE  /\ nextIndex'[i][j] <= Len(log'[i]) + 1
                          /\ matchIndex'[i][j] <= Len(log'[i])
            BY SMT DEF NextIndexBound
        <3>changed_server. CASE i = m.mdest
            <4>success. CASE m.msuccess
                BY SMT, <3>changed_server, <4>success, MessageFieldsTypeOK
                DEF HandleAppendEntriesResponse, TypeOK,
                    MsgTypeOK, ResponseIndexBound
            <4>failure. CASE ~m.msuccess
                <5>same_source. CASE j = m.msource
                    <6>log. log'[i] = log[i]
                        BY SMT, <3>changed_server, <4>failure
                        DEF HandleAppendEntriesResponse
                    <6>update. /\ nextIndex'[i][j] =
                                Max({nextIndex[i][j] - 1,
                                    matchIndex[i][j] + 1})
                               /\ UNCHANGED matchIndex
                        BY SMT, <3>changed_server, <4>failure,
                            <5>same_source
                        DEF HandleAppendEntriesResponse
                    <6>bound. /\ Max({nextIndex[i][j] - 1, matchIndex[i][j] + 1}) <= Len(log[i]) + 1
                              /\ matchIndex[i][j] <= Len(log[i])
                        <7>leader. state[i] = Leader
                            BY SMT DEF HandleAppendEntriesResponse
                        <7>next_bound. nextIndex[i][j]
                                <= Len(log[i]) + 1
                            BY SMT, <7>leader, NextIndexBound
                        <7>match_bound. matchIndex[i][j] + 1
                                <= Len(log[i]) + 1
                            BY <7>leader, LenProperties, SMT
                            DEF NextIndexBound, TypeOK, LeaderVarsTypeOK,
                                LogVarsTypeOK
                        <7> QED BY <7>next_bound, <7>match_bound,
                            MaxUpperBound, LenProperties, SMT
                    <6> QED BY SMT, <6>log, <6>update, <6>bound
                <5>other_source. CASE j # m.msource
                    BY SMT, <3>changed_server, <4>failure, <5>other_source,
                        NextIndexBound, LenProperties
                    DEF HandleAppendEntriesResponse, NextIndexBound
                <5> QED BY SMT, <5>same_source, <5>other_source
            <4> QED BY SMT, <3>changed_server, <4>success, <4>failure
        <3>other_server. CASE i # m.mdest
            BY SMT, <3>other_server
            DEF HandleAppendEntriesResponse, NextIndexBound
        <3> QED BY SMT, <3>changed_server, <3>other_server
    <2> QED BY SMT, <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY SMT, <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next, vars

LEMMA MessagesMonotonicNext ==
    [Next]_vars => messages \subseteq messages'
    BY SMT
    DEF Next, Restart, Timeout, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages, vars

LEMMA ReplicationBoundsInvInit == Init => ReplicationBoundsInv
    BY TypeOKInit, ServerStatesDistinct, SMT
    DEF ReplicationBoundsInv, SendInvariant, NextIndexBound, RequestIndexBound,
        ResponseTermBound, ResponseIndexBound, Init, InitServerVars, InitLogVars

LEMMA ReplicationBoundsInvNext ==
    ReplicationBoundsInv /\ [Next]_vars => ReplicationBoundsInv'
    BY TypeOKNext, SendInvariantNext, NextIndexBoundNext,
       RequestIndexBoundNext, ResponseTermBoundNext, ResponseIndexBoundNext, SMT
    DEF ReplicationBoundsInv

LEMMA EntryStructureEmpty ==
    \A term \in Nat: EntryStructure(<< >>, term)
    BY EmptySeq, LenProperties, SMT
    DEF EntryStructure

LEMMA EntryStructureTermMonotonic ==
    \A entries \in Seq(LogEntry), earlier, later \in Nat:
        EntryStructure(entries, earlier) /\ earlier <= later
        => EntryStructure(entries, later)
    BY ElementOfSeq, LenProperties, SMT DEF EntryStructure, LogEntry

LEMMA EntryStructureOnAppend ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        /\ EntryStructure(entries, term)
        /\ entry.term <= term
        => EntryStructure(Append(entries, entry), term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                      NEW term \in Nat, EntryStructure(entries, term),
                      entry.term <= term
             PROVE EntryStructure(Append(entries, entry), term)
    BY SMT
<1>append.
        /\ DOMAIN entries = 1..Len(entries)
        /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
        /\ Len(entries) \in Nat
        /\ \A index \in DOMAIN entries:
                Append(entries, entry)[index] = entries[index]
        /\ Append(entries, entry)[Len(entries) + 1] = entry
    BY AppendProperties, LenProperties, SMT
<1> QED BY <1>append, SMT DEF EntryStructure

LEMMA EntryStructureOnSubSeq ==
    \A entries \in Seq(LogEntry), first \in Nat \ {0}, last, term \in Nat:
        last <= Len(entries) /\ EntryStructure(entries, term)
        => EntryStructure(SubSeq(entries, first, last), term)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry),
                      NEW first \in Nat \ {0}, NEW last \in Nat,
                      NEW term \in Nat, last <= Len(entries),
                      EntryStructure(entries, term)
             PROVE EntryStructure(SubSeq(entries, first, last), term)
    BY SMT
<1>subseq.
        /\ SubSeq(entries, first, last) \in Seq(LogEntry)
        /\ Len(SubSeq(entries, first, last)) =
                IF first <= last THEN last - first + 1 ELSE 0
        /\ \A index \in 1..(last - first + 1):
                SubSeq(entries, first, last)[index] = entries[first + index - 1]
    BY SubSeqTypeOK, SubSeqProperties, ElementOfSeq, LenProperties, SMT
<1>positions.
        \A index \in DOMAIN SubSeq(entries, first, last):
            /\ first + index - 1 \in DOMAIN entries
            /\ SubSeq(entries, first, last)[index] = entries[first + index - 1]
    BY <1>subseq, LenProperties, SMT
<1> QED BY <1>positions, SMT DEF EntryStructure

LEMMA LogStructureImpliesTermBound == LogStructureInv => LogTermBoundInv
    BY SMT DEF LogStructureInv, EntryStructure, LogTermBoundInv

LEMMA CurrentTermsMonotonicNext ==
    TypeOK /\ [Next]_vars =>
        \A server \in Server: currentTerm[server] <= currentTerm'[server]
    BY MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, Next, vars, Restart, Timeout,
        BecomeLeader, ClientRequest, AdvanceCommitIndex, AppendEntries,
        LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse

LEMMA UnchangedLogsPreserveStructure ==
    /\ TypeOK /\ ServerVarsTypeOK' /\ LogStructureInv
    /\ UNCHANGED log
    /\ \A server \in Server: currentTerm[server] <= currentTerm'[server]
    => LogStructureInv'
    BY EntryStructureTermMonotonic, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LogStructureInv

LEMMA ClientRequestPreservesLogStructure ==
    \A actor \in Server, payload \in ClientPayload:
        TypeOK /\ LogStructureInv /\ ClientRequest(actor, payload)
        => LogStructureInv'
    BY ClientRequestAppendsCurrentTerm, EntryStructureOnAppend, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LogStructureInv, ClientRequest

LEMMA ChangedAppendEntriesLog ==
    \A message \in messages:
        /\ TypeOK /\ message.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(message.mdest, message.msource, message)
        /\ log'[message.mdest] # log[message.mdest]
        => /\ message.mterm = currentTerm[message.mdest]
           /\ message.mprevLogIndex \in 0..Len(log[message.mdest])
           /\ message.mentries # << >>
           /\ 1 \in DOMAIN message.mentries
           /\ message.mentries[1] \in LogEntry
           /\ log'[message.mdest] =
                  Append(SubSeq(log[message.mdest], 1, message.mprevLogIndex),
                         message.mentries[1])
    BY MessageFieldsTypeOK, EmptySeq, LenProperties, ElementOfSeq, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK,
        HandleAppendEntriesRequest

LEMMA AppendEntriesRequestPreservesLogStructure ==
    \A message \in messages:
        /\ TypeOK /\ LogStructureInv /\ RequestStructureInv
        /\ message.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(message.mdest, message.msource, message)
        => LogStructureInv'
<1> SUFFICES ASSUME NEW message \in messages, TypeOK, LogStructureInv,
                      RequestStructureInv, message.mtype = AppendEntriesRequest,
                      HandleAppendEntriesRequest(message.mdest, message.msource, message),
                      NEW server \in Server
             PROVE EntryStructure(log'[server], currentTerm'[server])
    BY SMT DEF LogStructureInv
<1>types.
        /\ message.mdest \in Server
        /\ log[server] \in Seq(LogEntry)
        /\ currentTerm[server] \in Nat
    BY MessageFieldsTypeOK, SMT
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>unchanged. CASE log'[server] = log[server]
    BY <1>unchanged, SMT DEF HandleAppendEntriesRequest, LogStructureInv
<1>changed. CASE log'[server] # log[server]
    <2>server. server = message.mdest
        BY <1>types, <1>changed, SMT
        DEF TypeOK, LogVarsTypeOK, HandleAppendEntriesRequest
    <2>shape.
            /\ message.mterm = currentTerm[server]
            /\ message.mprevLogIndex \in 0..Len(log[server])
            /\ 1 \in DOMAIN message.mentries
            /\ message.mentries[1] \in LogEntry
            /\ log'[server] =
                   Append(SubSeq(log[server], 1, message.mprevLogIndex),
                          message.mentries[1])
        BY <1>changed, <2>server, ChangedAppendEntriesLog, SMT
    <2>prefix.
            /\ SubSeq(log[server], 1, message.mprevLogIndex) \in Seq(LogEntry)
            /\ EntryStructure(SubSeq(log[server], 1, message.mprevLogIndex),
                              currentTerm[server])
        BY <1>types, <2>shape, SubSeqTypeOK, EntryStructureOnSubSeq, SMT
        DEF LogStructureInv
    <2>entry. message.mentries[1].term <= currentTerm[server]
        BY <2>shape, SMT DEF RequestStructureInv, EntryStructure
    <2> QED BY <1>types, <2>shape, <2>prefix, <2>entry,
        EntryStructureOnAppend, SMT DEF HandleAppendEntriesRequest
<1> QED BY <1>unchanged, <1>changed, SMT

LEMMA LogStructureInvNext ==
    /\ ReplicationBoundsInv /\ LogStructureInv /\ RequestStructureInv
    /\ [Next]_vars
    => LogStructureInv'
<1>frames.
        /\ TypeOK /\ LogStructureInv /\ [Next]_vars /\ UNCHANGED log
        => LogStructureInv'
    BY CurrentTermsMonotonicNext, ServerVarsTypeOKNext,
       UnchangedLogsPreserveStructure, SMT
<1>clients. \A actor \in Server, payload \in ClientPayload:
        TypeOK /\ LogStructureInv /\ ClientRequest(actor, payload)
        => LogStructureInv'
    BY SMT, ClientRequestPreservesLogStructure
<1>receives. \A message \in messages:
        /\ TypeOK /\ LogStructureInv /\ RequestStructureInv
        /\ [Next]_vars /\ Receive(message)
        => LogStructureInv'
    BY <1>frames, AppendEntriesRequestPreservesLogStructure, SMT
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>frames, <1>clients, <1>receives, SMT
    DEF ReplicationBoundsInv, Next, vars, Restart, Timeout, BecomeLeader,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown

LEMMA AppendEntriesEntriesStructure ==
    \A server, peer \in Server:
        TypeOK /\ LogStructureInv =>
            EntryStructure(AppendEntriesEntries(server, peer), currentTerm[server])
    BY EntryStructureOnSubSeq, AppendEntriesLastEntryTypeOK, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LeaderVarsTypeOK,
        LogStructureInv, AppendEntriesEntries

LEMMA RequestStructureInvNext ==
    /\ TypeOK /\ LogStructureInv /\ RequestStructureInv /\ [Next]_vars
    => RequestStructureInv'
<1>append. \A server, peer \in Server:
        /\ TypeOK /\ LogStructureInv /\ RequestStructureInv
        /\ AppendEntries(server, peer)
        => RequestStructureInv'
    BY AppendEntriesEntriesStructure, SMT
    DEF AppendEntries, Send, WithMessage, WithMessages, AppendEntriesMessage,
        RequestStructureInv
<1>others.
        /\ TypeOK /\ RequestStructureInv
        /\ \/ UNCHANGED vars
           \/ \E server \in Server: Restart(server)
           \/ \E server \in Server: Timeout(server)
           \/ \E server \in Server: BecomeLeader(server)
           \/ \E server \in Server, payload \in ClientPayload:
                  ClientRequest(server, payload)
           \/ \E server \in Server: AdvanceCommitIndex(server)
           \/ \E server \in Server: LeaderStepDown(server)
           \/ \E message \in messages: Receive(message)
        => RequestStructureInv'
    BY MessageTypesDistinct, SMT
    DEF RequestStructureInv, vars, Restart, Timeout, RequestVoteRequests,
        BecomeLeader, ClientRequest, AdvanceCommitIndex, LeaderStepDown,
        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>append, <1>others, SMT DEF Next

LEMMA MembershipStructureInvInit == Init => MembershipStructureInv
    BY ReplicationBoundsInvInit, MembershipElectionBaseInit,
       EntryStructureEmpty, SMT
    DEF MembershipStructureInv, LogStructureInv, RequestStructureInv,
        Init, InitServerVars, InitLogVars

LEMMA MembershipStructureInvNext ==
    MembershipStructureInv /\ [Next]_vars => MembershipStructureInv'
    BY ReplicationBoundsInvNext, LogStructureInvNext, RequestStructureInvNext,
       MembershipElectionBaseNext, LogStructureImpliesTermBound, SMT
    DEF MembershipStructureInv, ReplicationBoundsInv

LEMMA TermOrderingInvInit == Init => TermOrderingInv
    BY SMT DEF Init, InitLogVars, TermOrderingInv,
        LogTermsMonotonic, MessageTermsMonotonic

LEMMA AppendPreservesLogTermsMonotonic ==
    \A entries \in Seq(LogEntry), entry \in LogEntry:
        /\ \A first, last \in DOMAIN entries:
                first <= last => entries[first].term <= entries[last].term
        /\ \A index \in DOMAIN entries: entries[index].term <= entry.term
        => \A first, last \in DOMAIN Append(entries, entry):
                first <= last =>
                    Append(entries, entry)[first].term <=
                        Append(entries, entry)[last].term
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    \A first, last \in DOMAIN entries:
                        first <= last =>
                            entries[first].term <= entries[last].term,
                    \A index \in DOMAIN entries:
                        entries[index].term <= entry.term,
                    NEW first \in DOMAIN Append(entries, entry),
                    NEW last \in DOMAIN Append(entries, entry),
                    first <= last
             PROVE Append(entries, entry)[first].term <=
                       Append(entries, entry)[last].term
    BY SMT
<1>appended. Append(entries, entry) \in Seq(LogEntry)
              /\ Len(Append(entries, entry)) = Len(entries) + 1
    BY AppendProperties, SMT
<1>domain. /\ DOMAIN entries = 1..Len(entries)
             /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
    BY <1>appended, LenProperties, SMT
<1>old_last. CASE last \in DOMAIN entries
    <2>old_first. first \in DOMAIN entries
        BY SMT, <1>old_last, <1>domain
    <2>unchanged. /\ Append(entries, entry)[first] = entries[first]
                    /\ Append(entries, entry)[last] = entries[last]
        BY SMT, <1>old_last, <2>old_first, AppendProperties
    <2> QED BY SMT, <1>old_last, <2>old_first, <2>unchanged
<1>new_last. CASE last \notin DOMAIN entries
    <2>last_index. last = Len(entries) + 1
        BY SMT, <1>new_last, <1>domain
    <2>last_entry. Append(entries, entry)[last] = entry
        BY SMT, <2>last_index, AppendProperties
    <2>old_first. CASE first \in DOMAIN entries
        BY SMT, <2>old_first, <2>last_entry, AppendProperties
    <2>new_first. CASE first \notin DOMAIN entries
        <3>first_index. first = Len(entries) + 1
            BY SMT, <2>new_first, <1>domain
        <3>entry_type. entry.term \in Nat BY SMT DEF LogEntry
        <3> QED BY SMT, <2>last_index, <3>first_index, <3>entry_type
    <2> QED BY SMT, <2>old_first, <2>new_first
<1> QED BY SMT, <1>old_last, <1>new_last

LEMMA PrefixAppendPreservesLogTermsMonotonic ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, cut \in Nat:
        /\ cut <= Len(entries)
        /\ \A first, last \in DOMAIN entries:
                first <= last => entries[first].term <= entries[last].term
        /\ (cut > 0 => entries[cut].term <= entry.term)
        => \A first, last \in DOMAIN Append(SubSeq(entries, 1, cut), entry):
                first <= last =>
                    Append(SubSeq(entries, 1, cut), entry)[first].term <=
                        Append(SubSeq(entries, 1, cut), entry)[last].term
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW cut \in Nat, cut <= Len(entries),
                    \A first, last \in DOMAIN entries:
                        first <= last => entries[first].term <= entries[last].term,
                    cut > 0 => entries[cut].term <= entry.term
             PROVE \A first, last \in DOMAIN Append(SubSeq(entries, 1, cut), entry):
                       first <= last =>
                           Append(SubSeq(entries, 1, cut), entry)[first].term <=
                               Append(SubSeq(entries, 1, cut), entry)[last].term
    BY SMT
<1>prefix. /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
             /\ DOMAIN SubSeq(entries, 1, cut) = 1..cut
             /\ \A index \in 1..cut:
                    SubSeq(entries, 1, cut)[index] = entries[index]
    BY SMT, SubSeqProperties, LenProperties, ElementOfSeq
<1>ordered. \A first, last \in DOMAIN SubSeq(entries, 1, cut):
                first <= last =>
                    SubSeq(entries, 1, cut)[first].term <=
                        SubSeq(entries, 1, cut)[last].term
    BY SMT, <1>prefix, LenProperties
<1>bound. \A index \in DOMAIN SubSeq(entries, 1, cut):
              SubSeq(entries, 1, cut)[index].term <= entry.term
    <2> SUFFICES ASSUME NEW index \in DOMAIN SubSeq(entries, 1, cut)
                 PROVE SubSeq(entries, 1, cut)[index].term <= entry.term
        BY SMT
    <2>indexes. /\ index \in DOMAIN entries
                  /\ cut \in DOMAIN entries
                  /\ index <= cut
                  /\ cut > 0
        BY SMT, <1>prefix, LenProperties
    <2>terms. /\ entries[index].term \in Nat
                /\ entries[cut].term \in Nat
                /\ entry.term \in Nat
        BY SMT, <2>indexes, ElementOfSeq DEF LogEntry
    <2>ordered. entries[index].term <= entries[cut].term
        BY SMT, <2>indexes
    <2> QED BY SMT, <1>prefix, <2>indexes, <2>terms, <2>ordered, NatLeqTransitive
<1> QED BY SMT, <1>prefix, <1>ordered, <1>bound, AppendPreservesLogTermsMonotonic

LEMMA ClientRequestPreservesLogTermsMonotonic ==
    \A i \in Server, payload \in ClientPayload:
        /\ OrderingBase /\ LogTermsMonotonic /\ ClientRequest(i, payload)
        => LogTermsMonotonic'
    BY ClientRequestAppendsCurrentTerm, AppendPreservesLogTermsMonotonic, SMT
    DEF OrderingBase, TypeOK, LogVarsTypeOK, ServerVarsTypeOK,
        LogTermsMonotonic, LogTermBoundInv, ClientRequest

LEMMA HandleAppendEntriesRequestPreservesLogTermsMonotonic ==
    \A m \in messages:
        /\ OrderingBase /\ TermOrderingInv
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => LogTermsMonotonic'
<1> SUFFICES ASSUME NEW m \in messages, OrderingBase,
                    TermOrderingInv, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(m.mdest, m.msource, m),
                    NEW server \in Server
             PROVE \A first, last \in DOMAIN log'[server]:
                       first <= last =>
                           log'[server][first].term <= log'[server][last].term
    BY SMT DEF LogTermsMonotonic
<1>types. /\ log \in [Server -> Seq(LogEntry)]
            /\ m.mdest \in Server
            /\ m.mprevLogIndex \in Nat
            /\ m.mentries \in Seq(LogEntry)
    BY SMT, MessageFieldsTypeOK DEF OrderingBase, TypeOK,
        LogVarsTypeOK, MsgTypeOK
<1>other. CASE server # m.mdest
    BY SMT, <1>other, <1>types
    DEF HandleAppendEntriesRequest, TermOrderingInv, LogTermsMonotonic
<1>same. CASE server = m.mdest
    <2>unchanged. CASE log'[server] = log[server]
        BY SMT, <2>unchanged DEF TermOrderingInv, LogTermsMonotonic
    <2>changed. CASE log'[server] # log[server]
        <3>shape. /\ m.mentries # << >>
                    /\ m.mprevLogIndex <= Len(log[server])
                    /\ (m.mprevLogIndex > 0 =>
                           log[server][m.mprevLogIndex].term = m.mprevLogTerm)
                    /\ log'[server] =
                           Append(SubSeq(log[server], 1, m.mprevLogIndex),
                                  m.mentries[1])
            BY <1>same, <1>types, <2>changed, SMT
            DEF HandleAppendEntriesRequest
        <3>entry. m.mentries[1] \in LogEntry
            BY SMT, <1>types, <3>shape, EmptySeq, LenProperties, ElementOfSeq
        <3>ordered. \A first, last \in DOMAIN log[server]:
                        first <= last =>
                            log[server][first].term <= log[server][last].term
            BY SMT DEF TermOrderingInv, LogTermsMonotonic
        <3>boundary. m.mprevLogIndex > 0 =>
                        log[server][m.mprevLogIndex].term <= m.mentries[1].term
            BY SMT, <3>shape DEF TermOrderingInv, MessageTermsMonotonic
        <3> QED BY SMT, <1>types, <3>shape, <3>entry, <3>ordered, <3>boundary,
            PrefixAppendPreservesLogTermsMonotonic
    <2> QED BY SMT, <2>unchanged, <2>changed
<1> QED BY SMT, <1>other, <1>same

LEMMA AppendEntriesFirstEntrySnapshot ==
    \A i, j \in Server:
        /\ TypeOK /\ AppendEntriesEntries(i, j) # << >>
        => /\ nextIndex[i][j] \in DOMAIN log[i]
           /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    TypeOK, AppendEntriesEntries(i, j) # << >>
             PROVE /\ nextIndex[i][j] \in DOMAIN log[i]
                   /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    BY SMT
<1>types. /\ nextIndex[i][j] \in Nat \ {0}
            /\ log[i] \in Seq(LogEntry)
            /\ Len(log[i]) \in Nat
            /\ AppendEntriesLastEntry(i, j) \in Nat
            /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY SMT, AppendEntriesLastEntryTypeOK, LenProperties
    DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>elements. \A index \in nextIndex[i][j]..AppendEntriesLastEntry(i, j):
                 log[i][index] \in LogEntry
    BY SMT, <1>types, ElementOfSeq
<1>length. Len(AppendEntriesEntries(i, j)) =
               IF nextIndex[i][j] <= AppendEntriesLastEntry(i, j)
               THEN AppendEntriesLastEntry(i, j) - nextIndex[i][j] + 1
               ELSE 0
    BY SMT, <1>types, <1>elements, SubSeqProperties DEF AppendEntriesEntries
<1>nonempty. /\ AppendEntriesEntries(i, j) \in Seq(LogEntry)
               /\ Len(AppendEntriesEntries(i, j)) \in Nat \ {0}
    BY SMT, AppendEntriesEntriesTypeOK, EmptySeq
<1>index. nextIndex[i][j] \in DOMAIN log[i]
    BY SMT, <1>types, <1>length, <1>nonempty, LenProperties
<1>entry. AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    BY SMT, <1>types, <1>elements, <1>length, <1>nonempty, SubSeqProperties
    DEF AppendEntriesEntries
<1> QED BY SMT, <1>index, <1>entry

LEMMA AppendEntriesMessageTermsMonotonic ==
    \A i, j \in Server:
        /\ OrderingBase /\ LogTermsMonotonic
        /\ AppendEntriesMessage(i, j).mprevLogIndex > 0
        /\ AppendEntriesMessage(i, j).mentries # << >>
        => AppendEntriesMessage(i, j).mprevLogTerm <=
               AppendEntriesMessage(i, j).mentries[1].term
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    OrderingBase, LogTermsMonotonic,
                    AppendEntriesMessage(i, j).mprevLogIndex > 0,
                    AppendEntriesMessage(i, j).mentries # << >>
             PROVE AppendEntriesMessage(i, j).mprevLogTerm <=
                       AppendEntriesMessage(i, j).mentries[1].term
    BY SMT
<1>snapshot. /\ nextIndex[i][j] \in DOMAIN log[i]
               /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    BY SMT, AppendEntriesFirstEntrySnapshot
    DEF OrderingBase, AppendEntriesMessage
<1>indexes. /\ nextIndex[i][j] - 1 \in DOMAIN log[i]
              /\ nextIndex[i][j] - 1 <= nextIndex[i][j]
              /\ nextIndex[i][j] - 1 > 0
    BY SMT, <1>snapshot, LenProperties
    DEF AppendEntriesMessage, OrderingBase, TypeOK,
        LogVarsTypeOK, LeaderVarsTypeOK
<1>ordered. log[i][nextIndex[i][j] - 1].term <= log[i][nextIndex[i][j]].term
    BY SMT, <1>snapshot, <1>indexes DEF LogTermsMonotonic
<1> QED BY SMT, <1>snapshot, <1>indexes, <1>ordered
    DEF AppendEntriesMessage, AppendEntriesPrevLogTerm

LEMMA LogTermsMonotonicNext ==
    OrderingBase /\ TermOrderingInv /\ [Next]_vars => LogTermsMonotonic'
<1>client. CASE \E i \in Server, payload \in ClientPayload: ClientRequest(i, payload)
    BY SMT, <1>client, ClientRequestPreservesLogTermsMonotonic DEF TermOrderingInv
<1>append. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY SMT, <1>append, HandleAppendEntriesRequestPreservesLogTermsMonotonic
<1>unchanged. CASE UNCHANGED log
    BY SMT, <1>unchanged DEF TermOrderingInv, LogTermsMonotonic
<1> QED BY SMT, <1>client, <1>append, <1>unchanged
    DEF Next, vars, Restart, Timeout, BecomeLeader, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesResponse

LEMMA MessageTermsMonotonicNext ==
    OrderingBase /\ TermOrderingInv /\ [Next]_vars => MessageTermsMonotonic'
<1> SUFFICES ASSUME OrderingBase, TermOrderingInv, [Next]_vars,
                    NEW m \in messages', m.mtype = AppendEntriesRequest,
                    m.mprevLogIndex > 0, m.mentries # << >>
             PROVE m.mprevLogTerm <= m.mentries[1].term
    BY SMT DEF MessageTermsMonotonic
<1>old. CASE m \in messages
    BY SMT, <1>old DEF TermOrderingInv, MessageTermsMonotonic
<1>new. CASE m \notin messages
    <2>origin. \E i, j \in Server:
                  /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
        <3>append. CASE \E i, j \in Server: AppendEntries(i, j)
            BY SMT, <3>append, <1>new
            DEF AppendEntries, Send, WithMessage, WithMessages
        <3>timeout. CASE \E i \in Server: Timeout(i)
            BY SMT, <3>timeout, <1>new, MessageTypesDistinct
            DEF Timeout, WithMessages, RequestVoteRequests
        <3>receive. CASE \E request \in messages: Receive(request)
            BY <3>receive, <1>new, MessageTypesDistinct, SMT
            DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest,
                HandleAppendEntriesResponse, Send, WithMessage, WithMessages
        <3> QED BY SMT, <3>append, <3>timeout, <3>receive, <1>new
            DEF Next, vars, Restart, BecomeLeader, ClientRequest,
                AdvanceCommitIndex, LeaderStepDown
    <2> QED BY SMT, <2>origin, AppendEntriesMessageTermsMonotonic DEF TermOrderingInv
<1> QED BY SMT, <1>old, <1>new

LEMMA TermOrderingInvNext ==
    OrderingBase /\ TermOrderingInv /\ [Next]_vars => TermOrderingInv'
    BY SMT, LogTermsMonotonicNext, MessageTermsMonotonicNext DEF TermOrderingInv

============================================================================
