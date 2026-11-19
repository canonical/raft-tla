------------------ MODULE proof_inductiveinvariant --------------------
\* proof_inductiveinvariant.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS raft, SequenceTheorems, TLAPS, FiniteSetTheorems, proof_library
LOCAL INSTANCE NaturalsInduction

NextIndexBound ==
    \A i, j \in Server:
        state[i] = Leader =>
            /\ nextIndex[i][j] <= Len(log[i]) + 1
            /\ matchIndex[i][j] <= Len(log[i])

MatchIndexBelowNextIndex ==
    \A i, j \in Server: matchIndex[i][j] < nextIndex[i][j]

\* Once a follower has acknowledged an entry, no further backtracking is needed.
AcknowledgedNextIndexInv ==
    \A i, j \in Server:
        state[i] = Leader /\ matchIndex[i][j] # 0
        => nextIndex[i][j] = matchIndex[i][j] + 1

\* The match index is monotonic during leadership.
MatchIndexMonotonicInv ==
    \A i \in Server:
        state[i] = Leader /\ state'[i] = Leader
        => /\ \A j \in Server: matchIndex[i][j] <= matchIndex'[i][j]

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

Grant(voter, candidate, term) ==
    \E m \in messages:
        /\ m.mtype = RequestVoteResponse
        /\ m.mterm = term
        /\ m.mvoteGranted
        /\ m.msource = voter
        /\ m.mdest = candidate

Started(candidate, term) ==
    \/ Server = {candidate}
    \/ \E m \in messages:
        /\ m.mtype = RequestVoteRequest
        /\ m.mterm = term
        /\ m.msource = candidate

VoteFor(voter, candidate, term) ==
    voter = candidate \/ Grant(voter, candidate, term)

Won(candidate, term) ==
    /\ candidate \in Server
    /\ Started(candidate, term)
    /\ \E Q \in Quorum:
        \A voter \in Q: VoteFor(voter, candidate, term)

VoteCurrentInv ==
    \A voter \in Server, candidate \in Server, term \in Nat:
        /\ Grant(voter, candidate, term)
        /\ currentTerm[voter] = term
        => votedFor[voter] = candidate

VoteUniqueInv ==
    \A voter \in Server, candidate1 \in Server,
      candidate2 \in Server, term \in Nat:
        /\ Grant(voter, candidate1, term)
        /\ Grant(voter, candidate2, term)
        => candidate1 = candidate2

StartedGrantInv ==
    \A voter \in Server, candidate \in Server, term \in Nat:
        /\ Started(voter, term)
        /\ Grant(voter, candidate, term)
        => voter = candidate

StartedCurrentInv ==
    \A voter \in Server, term \in Nat:
        /\ Server # {voter}
        /\ Started(voter, term)
        /\ currentTerm[voter] = term
        => votedFor[voter] = voter

VoteRecordInv ==
    /\ VoteCurrentInv
    /\ VoteUniqueInv
    /\ StartedGrantInv
    /\ StartedCurrentInv

ActiveVotesInv ==
    \A candidate \in Server:
        state[candidate] \in {Candidate, Leader} =>
            /\ Started(candidate, currentTerm[candidate])
            /\ \A voter \in votesGranted[candidate]:
                VoteFor(voter, candidate, currentTerm[candidate])

LeaderQuorumInv ==
    \A i \in Server:
        state[i] = Leader =>
            \E Q \in Quorum: Q \subseteq votesGranted[i]

OwnerActive(owner, term) ==
    /\ currentTerm[owner] = term
    /\ state[owner] \in {Candidate, Leader}

LogHasTermAt(owner, term, index) ==
    /\ index \in DOMAIN log[owner]
    /\ log[owner][index].term = term

TermOwner(owner, term, index) ==
    /\ Won(owner, term)
    /\ term <= currentTerm[owner]
    /\ OwnerActive(owner, term) => LogHasTermAt(owner, term, index)

GrantPrime(voter, candidate, term) ==
    \E m \in messages':
        /\ m.mtype = RequestVoteResponse
        /\ m.mterm = term
        /\ m.mvoteGranted
        /\ m.msource = voter
        /\ m.mdest = candidate

StartedPrime(candidate, term) ==
    \/ Server = {candidate}
    \/ \E m \in messages':
        /\ m.mtype = RequestVoteRequest
        /\ m.mterm = term
        /\ m.msource = candidate

VoteForPrime(voter, candidate, term) ==
    voter = candidate \/ GrantPrime(voter, candidate, term)

WonPrime(candidate, term) ==
    /\ candidate \in Server
    /\ StartedPrime(candidate, term)
    /\ \E Q \in Quorum:
        \A voter \in Q: VoteForPrime(voter, candidate, term)

TermOwnerPrime(owner, term, index) ==
    /\ WonPrime(owner, term)
    /\ term <= currentTerm'[owner]
    /\ /\ currentTerm'[owner] = term
          /\ state'[owner] \in {Candidate, Leader}
       => /\ index \in DOMAIN log'[owner]
          /\ log'[owner][index].term = term

LogElectionInv ==
    \A i \in Server:
    \A index \in DOMAIN log[i]:
        \E owner \in Server:
            TermOwner(owner, log[i][index].term, index)

MessageElectionInv ==
    \A m \in messages:
        m.mtype = AppendEntriesRequest =>
        \A index \in DOMAIN m.mentries:
            \E owner \in Server:
                TermOwner(owner, m.mentries[index].term,
                          m.mprevLogIndex + index)

LogTermBoundInv ==
    \A i \in Server:
    \A index \in DOMAIN log[i]:
        log[i][index].term <= currentTerm[i]

MessageTermBoundInv ==
    \A m \in messages:
        m.mtype = AppendEntriesRequest =>
        \A index \in DOMAIN m.mentries:
            m.mentries[index].term <= m.mterm

CommitIndexBound ==
    \A i \in Server: commitIndex[i] <= Len(log[i])

RequestCommitIndexBound ==
    \A m \in messages:
        m.mtype = AppendEntriesRequest =>
            /\ Len(m.mentries) <= 1
            /\ m.mcommitIndex <= m.mprevLogIndex + Len(m.mentries)

InductiveInvariant ==
    /\ TypeOK
    /\ SendInvariant
    /\ MatchIndexBelowNextIndex
    /\ AcknowledgedNextIndexInv
    /\ NextIndexBound
    /\ RequestIndexBound
    /\ ResponseTermBound
    /\ ResponseIndexBound
    /\ VoteRecordInv
    /\ ActiveVotesInv
    /\ LeaderQuorumInv
    /\ LogElectionInv
    /\ MessageElectionInv
    /\ LogTermBoundInv
    /\ MessageTermBoundInv
    /\ RequestCommitIndexBound

------------------------------------------------------------------------

LEMMA WithMessagesTypeOK ==
    \A newMsgs \in SUBSET Message:
    \A msgs \in SUBSET Message:
        WithMessages(msgs, newMsgs) \subseteq Message
    BY DEF WithMessages

LEMMA WithMessageTypeOK ==
    \A m \in Message:
    \A msgs \in SUBSET Message:
        WithMessage(m, msgs) \subseteq Message
    BY WithMessagesTypeOK, Zenon DEF WithMessage

LEMMA LastTermTypeOK ==
    \A l \in Seq(LogEntry): LastTerm(l) \in Nat
    BY ElementOfSeq, LenProperties DEF LastTerm, LogEntry

LEMMA SubSeqTypeOK ==
    \A entries \in Seq(LogEntry), first \in Nat \ {0}, last \in Nat:
        last <= Len(entries) => SubSeq(entries, first, last) \in Seq(LogEntry)
    BY ElementOfSeq, LenProperties, SubSeqProperties

LEMMA MessageVariantTypes ==
    /\ RequestVoteRequestMessage \subseteq Message
    /\ RequestVoteResponseMessage \subseteq Message
    /\ AppendEntriesRequestMessage \subseteq Message
    /\ AppendEntriesResponseMessage \subseteq Message
    BY DEF Message

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
    BY DEF Message
<1> QED BY <1>1
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
    BY MessageVariantTypes DEF RequestVoteRequestMessage

LEMMA RequestVoteRequestsTypeOK ==
    \A i \in Server, term \in Nat:
        log \in [Server -> Seq(LogEntry)] =>
            RequestVoteRequests(i, term) \subseteq Message
    BY LastTermTypeOK, LenProperties, RequestVoteRequestTypeOK
        DEF RequestVoteRequests

LEMMA RequestVoteResponseTypeOK ==
    \A term \in Nat, granted \in BOOLEAN:
    \A source, dest \in Server:
        [mtype        |-> RequestVoteResponse,
         mterm        |-> term,
         mvoteGranted |-> granted,
         msource      |-> source,
         mdest        |-> dest] \in Message
    BY MessageVariantTypes DEF RequestVoteResponseMessage

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
    BY MessageVariantTypes DEF AppendEntriesRequestMessage

LEMMA AppendEntriesPrevLogTermTypeOK ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => AppendEntriesPrevLogTerm(i, j) \in Nat
    BY ElementOfSeq, LenProperties
    DEF AppendEntriesPrevLogTerm, NextIndexBound, TypeOK,
        LeaderVarsTypeOK, LogVarsTypeOK, LogEntry

LEMMA AppendEntriesLastEntryTypeOK ==
    \A i, j \in Server:
        TypeOK =>
            /\ AppendEntriesLastEntry(i, j) \in Nat
            /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY MinTypeOK, LenProperties
    DEF AppendEntriesLastEntry, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK

LEMMA AppendEntriesEntriesTypeOK ==
    \A i, j \in Server:
        TypeOK => AppendEntriesEntries(i, j) \in Seq(LogEntry)
    BY AppendEntriesLastEntryTypeOK, SubSeqTypeOK
    DEF AppendEntriesEntries, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK

LEMMA AppendEntriesMessageTypeOK ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => AppendEntriesMessage(i, j) \in Message
<1>prev_log_index. \A i, j \in Server:
        TypeOK => nextIndex[i][j] - 1 \in Nat
    BY DEF TypeOK, LeaderVarsTypeOK
<1> QED BY <1>prev_log_index, AppendEntriesPrevLogTermTypeOK,
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
    BY MessageVariantTypes DEF AppendEntriesResponseMessage

LEMMA MsgTypeOKInit == Init => MsgTypeOK
    BY DEF Init, MsgTypeOK, Message

LEMMA TimeoutMsgTypeOK ==
    \A i \in Server: TypeOK /\ Timeout(i) => MsgTypeOK'
<1> USE DEF Timeout, TypeOK, MsgTypeOK, ServerVarsTypeOK,
        LogVarsTypeOK
<1>requests. \A i \in Server:
        TypeOK /\ Timeout(i) =>
            RequestVoteRequests(i, currentTerm[i] + 1) \in SUBSET Message
    BY RequestVoteRequestsTypeOK
<1> QED BY <1>requests, WithMessagesTypeOK

LEMMA UnchangedMessagesMsgTypeOK ==
    TypeOK /\ UNCHANGED messages => MsgTypeOK'
    BY DEF TypeOK, MsgTypeOK

LEMMA HandleRequestVoteRequestMsgTypeOK ==
    \A i, j \in Server, m \in messages:
        TypeOK /\ HandleRequestVoteRequest(i, j, m) => MsgTypeOK'
    BY RequestVoteResponseTypeOK, WithMessageTypeOK
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
    <2> QED BY <2>response, WithMessageTypeOK
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
            BY MessageFieldsTypeOK, LenProperties
            DEF TypeOK, MsgTypeOK, ServerVarsTypeOK
        <3> QED BY <3>fields, AppendEntriesResponseTypeOK
    <2> QED BY <2>response, WithMessageTypeOK
        DEF Send, TypeOK, MsgTypeOK
<1> QED BY <1>rejected, <1>accepted
    DEF HandleAppendEntriesRequest

LEMMA ReceiveMsgTypeOK ==
    \A m \in messages: TypeOK /\ Receive(m) => MsgTypeOK'
<1> USE DEF Receive, HandleMsg
<1> QED BY UnchangedMessagesMsgTypeOK,
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
<1>stutter. TypeOK /\ UNCHANGED vars => MsgTypeOK'
    BY DEF vars
<1>restart. \A i \in Server:
        TypeOK /\ Restart(i) => MsgTypeOK'
    BY DEF Restart
<1>leader. \A i \in Server:
        TypeOK /\ BecomeLeader(i) => MsgTypeOK'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) => MsgTypeOK'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => MsgTypeOK'
    BY DEF AdvanceCommitIndex
<1>step_down. \A i \in Server:
        TypeOK /\ LeaderStepDown(i) => MsgTypeOK'
    BY DEF LeaderStepDown
<1> USE DEF Send, WithMessages, RequestVoteRequests
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => MsgTypeOK'
    BY TimeoutMsgTypeOK DEF Timeout
<1>append_entries. \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ AppendEntries(i, j)
        => MsgTypeOK'
    BY AppendEntriesMessageTypeOK, WithMessageTypeOK DEF AppendEntries
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => MsgTypeOK'
    BY ReceiveMsgTypeOK DEF Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter DEF Next, vars

LEMMA ServerVarsTypeOKInit == Init => ServerVarsTypeOK
    BY DEF Init, InitServerVars, ServerVarsTypeOK

LEMMA ServerVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => ServerVarsTypeOK'
    BY MessageFieldsTypeOK
    DEF Next, vars, Timeout, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, ServerVarsTypeOK

LEMMA CandidateVarsTypeOKInit == Init => CandidateVarsTypeOK
    BY DEF Init, InitCandidateVars, CandidateVarsTypeOK

LEMMA CandidateVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => CandidateVarsTypeOK'
    BY MessageFieldsTypeOK
    DEF Next, vars, Timeout, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, CandidateVarsTypeOK

LEMMA LeaderVarsTypeOKInit == Init => LeaderVarsTypeOK
    BY DEF Init, InitLeaderVars, LeaderVarsTypeOK

LEMMA LeaderVarsTypeOKNext ==
    TypeOK /\ [Next]_vars => LeaderVarsTypeOK'
<1> USE DEF TypeOK, MsgTypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>stutter. TypeOK /\ UNCHANGED vars => LeaderVarsTypeOK'
    BY DEF vars
<1>restart. \A i \in Server:
        TypeOK /\ Restart(i) => LeaderVarsTypeOK'
    BY DEF Restart
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => LeaderVarsTypeOK'
    BY DEF Timeout
<1>leader. \A i \in Server:
        TypeOK /\ BecomeLeader(i) => LeaderVarsTypeOK'
    <2>length. \A i \in Server:
            TypeOK =>
                /\ Len(log[i]) \in Nat
                /\ Len(log[i]) + 1 \in Nat \ {0}
        BY LenProperties DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>length, SMTT(20) DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) => LeaderVarsTypeOK'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => LeaderVarsTypeOK'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        TypeOK /\ AppendEntries(i, j) => LeaderVarsTypeOK'
    BY DEF AppendEntries
<1>step_down. \A i \in Server:
        TypeOK /\ LeaderStepDown(i) => LeaderVarsTypeOK'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => LeaderVarsTypeOK'
    BY MessageFieldsTypeOK, MaxTypeOK DEF Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next

LEMMA AgreeIndexesTypeOK ==
    \A i \in Server:
        TypeOK =>
            /\ Len(log[i]) \in Nat
            /\ AgreeIndexes(i) \in SUBSET (0..Len(log[i]))
    BY LenProperties
    DEF AgreeIndexes, TypeOK, LogVarsTypeOK

LEMMA MaxAgreeIndexesTypeOK ==
    \A i \in Server:
        /\ TypeOK
        /\ AgreeIndexes(i) # {}
        => /\ Max(AgreeIndexes(i)) \in AgreeIndexes(i)
           /\ Max(AgreeIndexes(i)) \in Nat
    BY AgreeIndexesTypeOK, MaxOfBoundedNatSet

LEMMA NewCommitIndexTypeOK ==
    \A i \in Server: TypeOK => NewCommitIndex(i) \in Nat
    BY MaxAgreeIndexesTypeOK
    DEF NewCommitIndex, TypeOK, LogVarsTypeOK

LEMMA ClientLogEntryTypeOK ==
    \A i \in Server, v \in Value:
        TypeOK => [term |-> currentTerm[i], value |-> v] \in LogEntry
    BY DEF TypeOK, ServerVarsTypeOK, LogEntry

LEMMA UnchangedLogVarsTypeOK ==
    TypeOK /\ UNCHANGED <<log, commitIndex>> => LogVarsTypeOK'
    BY DEF TypeOK, LogVarsTypeOK

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
    BY MessageFieldsTypeOK DEF TypeOK, MsgTypeOK, LogVarsTypeOK
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
        BY MessageFieldsTypeOK, EmptySeq, ElementOfSeq
        DEF TypeOK, MsgTypeOK
    <2>updated_log. \A i \in Server, m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ m.mentries # << >>
            /\ \/ Len(log[i]) = m.mprevLogIndex
               \/ /\ Len(log[i]) >= m.mprevLogIndex + 1
            /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])]
            => /\ Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1]) \in Seq(LogEntry)
        BY <2>entry, AppendProperties, SubSeqTypeOK, MessageFieldsTypeOK
        DEF TypeOK, LogVarsTypeOK, MsgTypeOK, ServerOK
    <2> QED BY <2>updated_log DEF TypeOK, LogVarsTypeOK
<1> QED BY <1>commit_index, <1>log, UnchangedLogVarsTypeOK, MessageFieldsTypeOK, ServerStatesDistinct
    DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
        TypeOK, LogVarsTypeOK, ServerVarsTypeOK, MsgTypeOK

LEMMA ReceiveLogVarsTypeOK ==
    \A m \in messages: TypeOK /\ Receive(m) => LogVarsTypeOK'
    BY HandleAppendEntriesRequestLogVarsTypeOK, UnchangedLogVarsTypeOK,
        MessageFieldsTypeOK
    DEF Receive, HandleMsg, UpdateTerm, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesResponse,
        TypeOK, MsgTypeOK, LogVarsTypeOK

LEMMA LogVarsTypeOKInit == Init => LogVarsTypeOK
    BY DEF Init, InitLogVars, LogVarsTypeOK, LogEntry

LEMMA LogVarsTypeOKNext == TypeOK /\ [Next]_vars => LogVarsTypeOK'
<1> USE DEF TypeOK, LogVarsTypeOK
<1>stutter. TypeOK /\ UNCHANGED vars => LogVarsTypeOK'
    BY DEF vars
<1>restart. \A i \in Server:
        TypeOK /\ Restart(i) => LogVarsTypeOK'
    BY DEF Restart
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => LogVarsTypeOK'
    BY DEF Timeout
<1>leader. \A i \in Server:
        TypeOK /\ BecomeLeader(i) => LogVarsTypeOK'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) => LogVarsTypeOK'
    BY ClientLogEntryTypeOK, AppendProperties DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => LogVarsTypeOK'
    BY NewCommitIndexTypeOK DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        TypeOK /\ AppendEntries(i, j) => LogVarsTypeOK'
    BY SMT DEF AppendEntries
<1>step_down. \A i \in Server:
        TypeOK /\ LeaderStepDown(i) => LogVarsTypeOK'
    BY SMT DEF LeaderStepDown
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => LogVarsTypeOK'
    BY ReceiveLogVarsTypeOK
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA TypeOKInit == Init => TypeOK
    BY MsgTypeOKInit, ServerVarsTypeOKInit, CandidateVarsTypeOKInit,
        LeaderVarsTypeOKInit, LogVarsTypeOKInit
        DEF TypeOK

LEMMA TypeOKNext ==
    /\ TypeOK
    /\ NextIndexBound
    /\ [Next]_vars
    => TypeOK'
    BY MsgTypeOKNext, ServerVarsTypeOKNext, CandidateVarsTypeOKNext,
        LeaderVarsTypeOKNext, LogVarsTypeOKNext
        DEF TypeOK


LEMMA RequestCommitIndexBoundInit == Init => RequestCommitIndexBound
    BY SMT DEF Init, RequestCommitIndexBound

LEMMA AppendEntriesMessageCommitIndexBound ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => /\ Len(AppendEntriesEntries(i, j)) <= 1
           /\ Min({commitIndex[i], AppendEntriesLastEntry(i, j)}) <=
                  nextIndex[i][j] - 1 + Len(AppendEntriesEntries(i, j))
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                      TypeOK, NextIndexBound, state[i] = Leader
             PROVE /\ Len(AppendEntriesEntries(i, j)) <= 1
                   /\ Min({commitIndex[i], AppendEntriesLastEntry(i, j)}) <=
                          nextIndex[i][j] - 1 + Len(AppendEntriesEntries(i, j))
    OBVIOUS
<1>types. /\ log[i] \in Seq(LogEntry)
          /\ Len(log[i]) \in Nat
          /\ nextIndex[i][j] \in Nat \ {0}
          /\ commitIndex[i] \in Nat
          /\ nextIndex[i][j] <= Len(log[i]) + 1
    BY LenProperties, SMT DEF TypeOK, LogVarsTypeOK, LeaderVarsTypeOK, NextIndexBound
<1>last. /\ AppendEntriesLastEntry(i, j) \in Nat
         /\ AppendEntriesLastEntry(i, j) <= nextIndex[i][j]
         /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
         /\ nextIndex[i][j] - 1 <= AppendEntriesLastEntry(i, j)
    BY <1>types, MinTypeOK, SMT DEF AppendEntriesLastEntry, Min
<1>length. Len(AppendEntriesEntries(i, j)) =
              AppendEntriesLastEntry(i, j) - nextIndex[i][j] + 1
    BY <1>types, <1>last, SubSeqProperties, SMT DEF AppendEntriesEntries
<1>minimum. Min({commitIndex[i], AppendEntriesLastEntry(i, j)}) <=
                AppendEntriesLastEntry(i, j)
    BY <1>types, <1>last, MinTypeOK, SMT
<1> QED BY <1>types, <1>last, <1>length, <1>minimum, SMT

LEMMA RequestCommitIndexBoundNext ==
    /\ TypeOK
    /\ NextIndexBound
    /\ RequestCommitIndexBound
    /\ [Next]_vars
    => RequestCommitIndexBound'
<1> USE MessageTypesDistinct
    DEF TypeOK, MsgTypeOK, RequestCommitIndexBound
<1>stutter. RequestCommitIndexBound /\ UNCHANGED vars => RequestCommitIndexBound'
    BY SMT DEF vars
<1>append_entries. \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ RequestCommitIndexBound
        /\ AppendEntries(i, j)
        => RequestCommitIndexBound'
    BY AppendEntriesMessageCommitIndexBound, SMT
    DEF AppendEntries, AppendEntriesMessage, Send, WithMessage, WithMessages
<1>others.
        /\ TypeOK
        /\ RequestCommitIndexBound
        /\ \/ \E i \in Server: Restart(i)
           \/ \E i \in Server: Timeout(i)
           \/ \E i \in Server: BecomeLeader(i)
           \/ \E i \in Server, v \in Value: ClientRequest(i, v)
           \/ \E i \in Server: AdvanceCommitIndex(i)
           \/ \E i \in Server: LeaderStepDown(i)
           \/ \E m \in messages: Receive(m)
        => RequestCommitIndexBound'
    BY SMT
    DEF Restart, Timeout, BecomeLeader, ClientRequest, AdvanceCommitIndex,
        LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages, RequestVoteRequests
<1> QED BY <1>stutter, <1>append_entries, <1>others, SMT DEF Next

LEMMA AppendEntriesMessageIndexBound ==
    \A i, j \in Server:
        /\ TypeOK
        /\ NextIndexBound
        /\ state[i] = Leader
        => nextIndex[i][j] - 1 + Len(AppendEntriesEntries(i, j))
            <= Len(log[i])
    BY AppendEntriesLastEntryTypeOK, SubSeqProperties, LenProperties
    DEF AppendEntriesEntries,
        AppendEntriesLastEntry, NextIndexBound, TypeOK, LeaderVarsTypeOK,
        LogVarsTypeOK

LEMMA InductiveInvariantInit == Init => InductiveInvariant
    BY TypeOKInit, RequestCommitIndexBoundInit, ServerStatesDistinct
    DEF InductiveInvariant, MatchIndexBelowNextIndex, AcknowledgedNextIndexInv,
        SendInvariant, NextIndexBound, RequestIndexBound,
        ResponseTermBound, ResponseIndexBound, VoteRecordInv, Grant, Started,
        ActiveVotesInv, LeaderQuorumInv, LogElectionInv, MessageElectionInv,
        VoteCurrentInv, VoteUniqueInv, StartedGrantInv, StartedCurrentInv,
        LogTermBoundInv, MessageTermBoundInv, Init, InitServerVars,
        InitCandidateVars, InitLeaderVars, InitLogVars

LEMMA MatchIndexBelowNextIndexInit == Init => MatchIndexBelowNextIndex
    BY DEF Init, InitLeaderVars, MatchIndexBelowNextIndex

LEMMA UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex ==
    /\ MatchIndexBelowNextIndex
    /\ UNCHANGED <<nextIndex, matchIndex>>
    => MatchIndexBelowNextIndex'
    BY DEF MatchIndexBelowNextIndex

LEMMA RestartPreservesMatchIndexBelowNextIndex ==
    \A i \in Server:
        TypeOK /\ MatchIndexBelowNextIndex /\ Restart(i)
        => MatchIndexBelowNextIndex'
    BY SMT
    DEF Restart, MatchIndexBelowNextIndex, TypeOK, LeaderVarsTypeOK

LEMMA BecomeLeaderPreservesMatchIndexBelowNextIndex ==
    \A i \in Server:
        TypeOK /\ MatchIndexBelowNextIndex /\ BecomeLeader(i)
        => MatchIndexBelowNextIndex'
    BY LenProperties, SMT
    DEF BecomeLeader, MatchIndexBelowNextIndex, TypeOK, LogVarsTypeOK,
        LeaderVarsTypeOK

LEMMA HandleAppendEntriesResponsePreservesMatchIndexBelowNextIndex ==
    \A m \in messages:
        /\ TypeOK
        /\ MatchIndexBelowNextIndex
        /\ m.mtype = AppendEntriesResponse
        /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
        => MatchIndexBelowNextIndex'
    BY MessageFieldsTypeOK, MaxTypeOK, SMT
    DEF HandleAppendEntriesResponse, MatchIndexBelowNextIndex,
        TypeOK, MsgTypeOK, LeaderVarsTypeOK

LEMMA MatchIndexBelowNextIndexNext ==
    /\ TypeOK
    /\ MatchIndexBelowNextIndex
    /\ [Next]_vars
    => MatchIndexBelowNextIndex'
<1>stutter. MatchIndexBelowNextIndex /\ UNCHANGED vars
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF vars
<1>restart. \A i \in Server:
        TypeOK /\ MatchIndexBelowNextIndex /\ Restart(i)
        => MatchIndexBelowNextIndex'
    BY RestartPreservesMatchIndexBelowNextIndex
<1>timeout. \A i \in Server:
        MatchIndexBelowNextIndex /\ Timeout(i)
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF Timeout
<1>leader. \A i \in Server:
        TypeOK /\ MatchIndexBelowNextIndex /\ BecomeLeader(i)
        => MatchIndexBelowNextIndex'
    BY BecomeLeaderPreservesMatchIndexBelowNextIndex
<1>client_request. \A i \in Server, v \in Value:
        MatchIndexBelowNextIndex /\ ClientRequest(i, v)
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF ClientRequest
<1>commit. \A i \in Server:
        MatchIndexBelowNextIndex /\ AdvanceCommitIndex(i)
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex
    DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        MatchIndexBelowNextIndex /\ AppendEntries(i, j)
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF AppendEntries
<1>step_down. \A i \in Server:
        MatchIndexBelowNextIndex /\ LeaderStepDown(i)
        => MatchIndexBelowNextIndex'
    BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF LeaderStepDown
<1>receive. \A m \in messages:
        TypeOK /\ MatchIndexBelowNextIndex /\ Receive(m)
        => MatchIndexBelowNextIndex'
    <2>update_term. \A m \in messages:
            MatchIndexBelowNextIndex /\ UpdateTerm(m.mdest, m.msource, m)
            => MatchIndexBelowNextIndex'
        BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ MatchIndexBelowNextIndex
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => MatchIndexBelowNextIndex'
        BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex
        DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ MatchIndexBelowNextIndex
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => MatchIndexBelowNextIndex'
        BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex
        DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ MatchIndexBelowNextIndex
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => MatchIndexBelowNextIndex'
        BY UnchangedLeaderVarsPreservesMatchIndexBelowNextIndex
        DEF HandleAppendEntriesRequest
    <2>append_entries_response. \A m \in messages:
            /\ TypeOK
            /\ MatchIndexBelowNextIndex
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => MatchIndexBelowNextIndex'
        BY HandleAppendEntriesResponsePreservesMatchIndexBelowNextIndex
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response
        DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader,
    <1>client_request, <1>commit, <1>append_entries, <1>step_down,
    <1>receive
    DEF Next, vars

LEMMA AcknowledgedNextIndexInvNext ==
    /\ TypeOK
    /\ AcknowledgedNextIndexInv
    /\ [Next]_vars
    => AcknowledgedNextIndexInv'
<1> USE DEF AcknowledgedNextIndexInv, TypeOK, LeaderVarsTypeOK, vars
<1>stutter. TypeOK /\ AcknowledgedNextIndexInv /\ UNCHANGED vars
        => AcknowledgedNextIndexInv'
    BY SMT
<1>restart. \A i \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ Restart(i)
        => AcknowledgedNextIndexInv'
    BY ServerStatesDistinct, SMT DEF Restart, ServerVarsTypeOK
<1>timeout. \A i \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ Timeout(i)
        => AcknowledgedNextIndexInv'
    BY ServerStatesDistinct, SMT DEF Timeout, ServerVarsTypeOK
<1>leader. \A i \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ BecomeLeader(i)
        => AcknowledgedNextIndexInv'
    BY SMT DEF BecomeLeader, ServerVarsTypeOK
<1>client_request. \A i \in Server, v \in Value:
        TypeOK /\ AcknowledgedNextIndexInv /\ ClientRequest(i, v)
        => AcknowledgedNextIndexInv'
    BY SMT DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ AdvanceCommitIndex(i)
        => AcknowledgedNextIndexInv'
    BY SMT DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ AppendEntries(i, j)
        => AcknowledgedNextIndexInv'
    BY SMT DEF AppendEntries
<1>step_down. \A i \in Server:
        TypeOK /\ AcknowledgedNextIndexInv /\ LeaderStepDown(i)
        => AcknowledgedNextIndexInv'
    BY ServerStatesDistinct, SMT DEF LeaderStepDown, ServerVarsTypeOK
<1>receive. \A m \in messages:
        TypeOK /\ AcknowledgedNextIndexInv /\ Receive(m)
        => AcknowledgedNextIndexInv'
    <2>update_term. \A m \in messages:
            TypeOK /\ AcknowledgedNextIndexInv /\ UpdateTerm(m.mdest, m.msource, m)
            => AcknowledgedNextIndexInv'
        BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
        DEF UpdateTerm, MsgTypeOK, ServerVarsTypeOK
    <2>request_vote_request. \A m \in messages:
            /\ TypeOK /\ AcknowledgedNextIndexInv
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => AcknowledgedNextIndexInv'
        BY SMT DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ TypeOK /\ AcknowledgedNextIndexInv
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => AcknowledgedNextIndexInv'
        BY SMT DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ TypeOK /\ AcknowledgedNextIndexInv
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => AcknowledgedNextIndexInv'
        <3>frame. \A m \in messages:
                HandleAppendEntriesRequest(m.mdest, m.msource, m)
                => UNCHANGED <<nextIndex, matchIndex>>
            BY DEF HandleAppendEntriesRequest
        <3>leaders. \A m \in messages:
                TypeOK /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
                => \A i \in Server: state'[i] = Leader => state[i] = Leader
            BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
            DEF HandleAppendEntriesRequest, MsgTypeOK, ServerVarsTypeOK
        <3> QED BY <3>frame, <3>leaders, SMT
    <2>append_entries_response.
        ASSUME NEW m \in messages, TypeOK, AcknowledgedNextIndexInv,
               m.mtype = AppendEntriesResponse,
               HandleAppendEntriesResponse(m.mdest, m.msource, m)
        PROVE AcknowledgedNextIndexInv'
        <3> USE <2>append_entries_response
            DEF TypeOK, LeaderVarsTypeOK, AcknowledgedNextIndexInv
        <3>types. /\ m.mdest \in Server /\ m.msource \in Server
                  /\ m.mmatchIndex \in Nat /\ m.msuccess \in BOOLEAN
            BY MessageFieldsTypeOK, SMT DEF MsgTypeOK
        <3> QED BY <3>types, SMT
            DEF HandleAppendEntriesResponse, ServerVarsTypeOK, Max
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response, SMT DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader,
    <1>client_request, <1>commit, <1>append_entries, <1>step_down,
    <1>receive, SMT DEF Next

LEMMA ClientRequestGrowsOwnLog ==
    \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) =>
            Len(log'[i]) = Len(log[i]) + 1
    BY ClientLogEntryTypeOK, AppendProperties
    DEF ClientRequest, TypeOK, ServerVarsTypeOK, LogVarsTypeOK, LogEntry

LEMMA ClientRequestPreservesOtherLogs ==
    \A i, k \in Server, v \in Value:
        /\ TypeOK
        /\ k # i
        /\ ClientRequest(i, v)
        => log'[k] = log[k]
    BY DEF ClientRequest, TypeOK, LogVarsTypeOK

LEMMA ClientRequestDoesNotShrinkLogs ==
    \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) =>
            /\ LogVarsTypeOK'
            /\ \A k \in Server: Len(log[k]) <= Len(log'[k])
<1>type. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) => LogVarsTypeOK'
    BY ClientLogEntryTypeOK, AppendProperties
    DEF ClientRequest, TypeOK, LogVarsTypeOK
<1>length. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) =>
            \A k \in Server: Len(log[k]) <= Len(log'[k])
    <2> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                         TypeOK, ClientRequest(i, v), NEW k \in Server
                PROVE  Len(log[k]) <= Len(log'[k])
        OBVIOUS
    <2>same_server. CASE k = i
        BY <2>same_server, ClientRequestGrowsOwnLog, LenProperties
        DEF TypeOK, LogVarsTypeOK
    <2>other_server. CASE k # i
        BY <2>other_server, ClientRequestPreservesOtherLogs, LenProperties
        DEF TypeOK, LogVarsTypeOK
    <2> QED BY <2>same_server, <2>other_server
<1> QED BY <1>type, <1>length

LEMMA AcceptedAppendEntriesLogLength ==
    \A i, j \in Server, m \in messages:
        /\ TypeOK
        /\ RequestCommitIndexBound
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
        /\ state[i] # Leader
        /\ m.mterm = currentTerm[i]
        /\ \/ m.mprevLogIndex = 0
           \/ /\ m.mprevLogIndex > 0
              /\ m.mprevLogIndex <= Len(log[i])
              /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        => m.mprevLogIndex + Len(m.mentries) <= Len(log'[i])
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                      NEW m \in messages, TypeOK, RequestCommitIndexBound,
                      m.mtype = AppendEntriesRequest,
                      HandleAppendEntriesRequest(i, j, m),
                      state[i] # Leader, m.mterm = currentTerm[i],
                      \/ m.mprevLogIndex = 0
                      \/ /\ m.mprevLogIndex > 0
                         /\ m.mprevLogIndex <= Len(log[i])
                         /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
             PROVE m.mprevLogIndex + Len(m.mentries) <= Len(log'[i])
    OBVIOUS
<1>types. /\ log \in [Server -> Seq(LogEntry)]
          /\ log[i] \in Seq(LogEntry)
          /\ Len(log[i]) \in Nat
          /\ m.mprevLogIndex \in Nat
          /\ m.mprevLogIndex <= Len(log[i])
          /\ m.mentries \in Seq(LogEntry)
          /\ Len(m.mentries) \in Nat
          /\ Len(m.mentries) <= 1
    BY MessageFieldsTypeOK, LenProperties, SMT
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK, RequestCommitIndexBound
<1>changed. CASE /\ m.mentries /= << >>
                 /\ \/ Len(log[i]) = m.mprevLogIndex
                    \/ log[i][m.mprevLogIndex + 1].term /= m.mentries[1].term
    <2>length. /\ Len(m.mentries) = 1
               /\ log'[i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])
        BY <1>types, <1>changed, EmptySeq, SMT DEF HandleAppendEntriesRequest
    <2> QED BY <1>types, <2>length, AppendProperties, SubSeqProperties, SMT
<1>unchanged. CASE ~(/\ m.mentries /= << >>
                    /\ \/ Len(log[i]) = m.mprevLogIndex
                       \/ log[i][m.mprevLogIndex + 1].term /= m.mentries[1].term)
    BY <1>types, <1>unchanged, EmptySeq, SMT DEF HandleAppendEntriesRequest
<1> QED BY <1>changed, <1>unchanged, SMT


LEMMA StoredMessageFieldsTypeOK ==
    TypeOK =>
        \A m \in messages:
            /\ m.msource \in Server
            /\ m.mdest \in Server
    BY MessageFieldsTypeOK DEF TypeOK, MsgTypeOK

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
    BY DEF RequestIndexBound
<1>1. m \in messages /\ m.msource \in Server
    BY StoredMessageFieldsTypeOK
<1>2. m.mprevLogIndex + Len(m.mentries) <= Len(log[m.msource])
    BY <1>1 DEF RequestIndexBound
<1>3. Len(log[m.msource]) <= Len(log'[m.msource])
    BY <1>1
<1>4. /\ m.mprevLogIndex \in Nat
       /\ Len(m.mentries) \in Nat
       /\ Len(log[m.msource]) \in Nat
       /\ Len(log'[m.msource]) \in Nat
    BY <1>1, MessageFieldsTypeOK, LenProperties
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY <1>2, <1>3, <1>4, NatLeqTransitive

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
    BY DEF ResponseIndexBound
<1>1. m \in messages /\ m.mdest \in Server
    BY StoredMessageFieldsTypeOK
<1>2. m.mmatchIndex <= Len(log[m.mdest])
    BY <1>1 DEF ResponseIndexBound
<1>3. Len(log[m.mdest]) <= Len(log'[m.mdest])
    BY <1>1
<1>4. /\ m.mmatchIndex \in Nat
       /\ Len(log[m.mdest]) \in Nat
       /\ Len(log'[m.mdest]) \in Nat
    BY <1>1, MessageFieldsTypeOK, LenProperties
    DEF TypeOK, MsgTypeOK, LogVarsTypeOK
<1> QED BY <1>2, <1>3, <1>4, NatLeqTransitive

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
    BY DEF NextIndexBound
<1>1. /\ nextIndex[i][j] <= Len(log[i]) + 1
       /\ matchIndex[i][j] <= Len(log[i])
    BY DEF NextIndexBound
<1>2. Len(log[i]) <= Len(log'[i])
    BY SMT
<1>3. /\ nextIndex[i][j] \in Nat
       /\ matchIndex[i][j] \in Nat
       /\ Len(log[i]) \in Nat
       /\ Len(log'[i]) \in Nat
    BY LenProperties
    DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1> QED BY <1>1, <1>2, <1>3, NatLeqTransitive

LEMMA TimeoutDoesNotDecreaseTerms ==
    \A i \in Server:
        ServerVarsTypeOK /\ Timeout(i) =>
            \A k \in Server: currentTerm[k] <= currentTerm'[k]
    BY DEF ServerVarsTypeOK, Timeout

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
    BY DEF Timeout, WithMessages
<1>2. \A i \in Server:
        \A m \in RequestVoteRequests(i, currentTerm[i] + 1):
            m.mtype = RequestVoteRequest
    BY DEF RequestVoteRequests
<1>3. RequestVoteRequest
        \notin {AppendEntriesRequest, AppendEntriesResponse}
    BY MessageTypesDistinct DEF MessageTypesDistinct
<1> QED BY <1>1, <1>2, <1>3

LEMMA HandleAppendEntriesRequestPreservesOtherServer ==
    \A m \in messages, k \in Server:
        /\ TypeOK
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        /\ k # m.mdest
        => /\ currentTerm'[k] = currentTerm[k]
           /\ state'[k] = state[k]
           /\ log'[k] = log[k]
    BY MessageFieldsTypeOK
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
    BY ServerStatesDistinct, MessageFieldsTypeOK
    DEF HandleAppendEntriesRequest, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, LogVarsTypeOK,
        ServerStatesDistinct

LEMMA SendInvariantNext ==
    /\ SendInvariant
    /\ TypeOK
    /\ [Next]_vars
    => SendInvariant'
BY MessageFieldsTypeOK
DEF Next, Restart, Timeout, BecomeLeader, ClientRequest,
    AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
    HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
    HandleAppendEntriesRequest, HandleAppendEntriesResponse,
    Send, WithMessage, WithMessages, RequestVoteRequests,
    AppendEntriesMessage, vars, InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK,
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
    BY DEF vars
<1>restart. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ Restart(i) => RequestIndexBound'
    BY MessageFieldsTypeOK DEF Restart
<1>timeout. \A i \in Server:
            /\ RequestIndexBound
            /\ TypeOK
            /\ SendInvariant
            /\ Timeout(i)
            => RequestIndexBound'
    BY TimeoutPreservesAppendEntriesMessages, MessageFieldsTypeOK
    DEF Timeout
<1>leader. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ BecomeLeader(i) => RequestIndexBound'
    BY MessageFieldsTypeOK DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        RequestIndexBound /\ TypeOK /\ ClientRequest(i, v) => RequestIndexBound'
    BY ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveRequestIndexBound
    DEF  ClientRequest
<1>commit. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => RequestIndexBound'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        /\ NextIndexBound
        /\ RequestIndexBound
        /\ TypeOK
        /\ AppendEntries(i, j)
        => RequestIndexBound'
    BY AppendEntriesMessageIndexBound
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        RequestIndexBound /\ TypeOK /\ LeaderStepDown(i) => RequestIndexBound'
    BY MessageFieldsTypeOK DEF LeaderStepDown
<1>receive. \A m \in messages:
        RequestIndexBound /\ TypeOK /\ Receive(m) => RequestIndexBound'
    <2>update_term. \A m \in messages:
            RequestIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                RequestIndexBound'
        BY MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY MessageFieldsTypeOK
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages,
            MessageTypesDistinct
    <2>request_vote_response. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY DEF HandleRequestVoteResponse
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
            BY DEF RequestIndexBound
        <3>1. q \in messages /\ q.msource \in Server
            BY MessageFieldsTypeOK
            DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages,
                TypeOK, MsgTypeOK, MessageTypesDistinct
        <3>same_server. CASE q.msource = m.mdest
            BY <3>same_server, <3>1, MessageFieldsTypeOK
            DEF HandleAppendEntriesRequest, TypeOK,
                MsgTypeOK, RequestIndexBound, ServerStatesDistinct
        <3>other_server. CASE q.msource # m.mdest
            <4> USE <3>other_server, <3>1
            <4>1. /\ currentTerm'[q.msource] = currentTerm[q.msource]
                  /\ state'[q.msource] = state[q.msource]
                  /\ log'[q.msource] = log[q.msource]
                BY HandleAppendEntriesRequestPreservesOtherServer
            <4>2. q.mprevLogIndex + Len(q.mentries)
                    <= Len(log[q.msource])
                BY <3>1, <4>1 DEF RequestIndexBound
            <4> QED BY <4>1, <4>2
        <3> QED BY <3>same_server, <3>other_server
    <2>append_entries_response. \A m \in messages:
            /\ RequestIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => RequestIndexBound'
        BY DEF HandleAppendEntriesResponse
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
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
    BY DEF vars
<1>restart. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ Restart(i) => ResponseTermBound'
    BY DEF Restart
<1>timeout. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ Timeout(i) => ResponseTermBound'
    BY TimeoutPreservesAppendEntriesMessages, TimeoutDoesNotDecreaseTerms,
        MessageFieldsTypeOK DEF Timeout
<1>leader. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ BecomeLeader(i) => ResponseTermBound'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        ResponseTermBound /\ TypeOK /\ ClientRequest(i, v) => ResponseTermBound'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ AdvanceCommitIndex(i) => ResponseTermBound'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        ResponseTermBound /\ TypeOK /\ AppendEntries(i, j) => ResponseTermBound'
    BY MessageFieldsTypeOK
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        ResponseTermBound /\ TypeOK /\ LeaderStepDown(i) => ResponseTermBound'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        /\ ResponseTermBound
        /\ TypeOK
        /\ SendInvariant
        /\ Receive(m)
        => ResponseTermBound'
    BY MessageFieldsTypeOK
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages,
        MessageTypesDistinct
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
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
    BY DEF vars
<1>restart. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ Restart(i) => ResponseIndexBound'
    BY MessageFieldsTypeOK DEF Restart
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
            BY <2>same_server, MessageFieldsTypeOK, LenProperties
            DEF TypeOK, MsgTypeOK, LogVarsTypeOK, Timeout
        <3>positive. m.mmatchIndex > 0 => FALSE
            BY <2>same_server, TimeoutDoesNotDecreaseTerms, MessageFieldsTypeOK
            DEF Timeout, TypeOK, MsgTypeOK, ResponseTermBound
        <3> QED BY <2>same_server, <3>zero, <3>positive, MessageFieldsTypeOK DEF TypeOK, MsgTypeOK
    <2>other_server. \A i \in Server, m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ Timeout(i)
            /\ m.mdest # i
            /\ m.mtype = AppendEntriesResponse
            /\ m.mterm = currentTerm'[m.mdest]
            /\ state'[m.mdest] \in {Candidate, Leader}
            => m.mmatchIndex <= Len(log'[m.mdest])
        BY MessageFieldsTypeOK
        DEF Timeout, TypeOK, MsgTypeOK, ResponseIndexBound
    <2> QED BY <2>same_server, <2>other_server,
        TimeoutPreservesAppendEntriesMessages, MessageFieldsTypeOK
        DEF ResponseIndexBound
<1>leader. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ BecomeLeader(i) => ResponseIndexBound'
    BY MessageFieldsTypeOK DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        ResponseIndexBound /\ TypeOK /\ ClientRequest(i, v) => ResponseIndexBound'
    BY ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveResponseIndexBound
    DEF ClientRequest
<1>commit. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => ResponseIndexBound'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        ResponseIndexBound /\ TypeOK /\ AppendEntries(i, j) => ResponseIndexBound'
    BY MessageFieldsTypeOK
    DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage, MessageTypesDistinct
<1>step_down. \A i \in Server:
        ResponseIndexBound /\ TypeOK /\ LeaderStepDown(i) => ResponseIndexBound'
    BY MessageFieldsTypeOK DEF LeaderStepDown
<1>receive. \A m \in messages:
        RequestIndexBound /\ ResponseIndexBound /\ TypeOK /\ Receive(m) => ResponseIndexBound'
    <2>update_term. \A m \in messages:
            ResponseIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                ResponseIndexBound'
        BY MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY MessageFieldsTypeOK
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages,
            MessageTypesDistinct
    <2>request_vote_response. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY DEF HandleRequestVoteResponse
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
            BY DEF ResponseIndexBound
        <3>old_response. CASE q \in messages
            <4> USE <3>old_response
            <4>same_server. CASE q.mdest = m.mdest
                BY <4>same_server, HandleAppendEntriesRequestPreservesActiveRecipient, MessageFieldsTypeOK
                DEF TypeOK, MsgTypeOK, ResponseIndexBound
            <4>other_server. CASE q.mdest # m.mdest
                BY <4>other_server, HandleAppendEntriesRequestPreservesOtherServer, MessageFieldsTypeOK
                DEF TypeOK, MsgTypeOK, ResponseIndexBound
            <4> QED BY <4>same_server, <4>other_server
        <3>new_response. CASE q \notin messages
            <4> USE <3>new_response
            <4>location. /\ q.mdest = m.msource
                         /\ currentTerm'[q.mdest] = currentTerm[q.mdest]
                         /\ state'[q.mdest] = state[q.mdest]
                         /\ log'[q.mdest] = log[q.mdest]
                BY HandleAppendEntriesRequestPreservesOtherServer,
                    MessageFieldsTypeOK
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK
            <4>zero. q.mmatchIndex = 0 =>
                    q.mmatchIndex <= Len(log'[q.mdest])
                BY <4>location, MessageFieldsTypeOK, LenProperties
                DEF TypeOK, MsgTypeOK, LogVarsTypeOK
            <4>positive. q.mmatchIndex > 0 =>
                    q.mmatchIndex <= Len(log'[q.mdest])
                BY <4>location, MessageFieldsTypeOK, LenProperties
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK,
                    RequestIndexBound
            <4>cases. q.mmatchIndex = 0 \/ q.mmatchIndex > 0
                BY MessageFieldsTypeOK
                DEF HandleAppendEntriesRequest, Send, WithMessage,
                    WithMessages, TypeOK, MsgTypeOK
            <4> QED BY <4>zero, <4>positive, <4>cases
        <3> QED BY <3>old_response, <3>new_response
    <2>append_entries_response. \A m \in messages:
            /\ ResponseIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => ResponseIndexBound'
        BY DEF HandleAppendEntriesResponse
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA NextIndexBoundNext ==
    (/\ ResponseIndexBound
     /\ MatchIndexBelowNextIndex
     /\ NextIndexBound
     /\ TypeOK
     /\ [Next]_vars) => NextIndexBound'
<1> USE ServerStatesDistinct
    DEF TypeOK, MsgTypeOK, ServerVarsTypeOK,
        LeaderVarsTypeOK, LogVarsTypeOK, ResponseIndexBound, NextIndexBound
<1>stutter. NextIndexBound /\ TypeOK /\ UNCHANGED vars => NextIndexBound'
    BY DEF vars
<1>restart. \A i \in Server:
        NextIndexBound /\ TypeOK /\ Restart(i) => NextIndexBound'
    BY LenProperties DEF Restart
<1>timeout. \A i \in Server:
        NextIndexBound /\ TypeOK /\ Timeout(i) => NextIndexBound'
    BY ServerStatesDistinct, LenProperties
    DEF Timeout, NextIndexBound
<1>leader. \A i \in Server:
        NextIndexBound /\ TypeOK /\ BecomeLeader(i) => NextIndexBound'
    BY LenProperties, SMTT(20) DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        NextIndexBound /\ TypeOK /\ ClientRequest(i, v) => NextIndexBound'
    BY ClientRequestDoesNotShrinkLogs,
        NonShrinkingLogsPreserveNextIndexBound
    DEF ClientRequest
<1>commit. \A i \in Server:
        NextIndexBound /\ TypeOK /\ AdvanceCommitIndex(i) => NextIndexBound'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        NextIndexBound /\ TypeOK /\ AppendEntries(i, j) => NextIndexBound'
    BY DEF AppendEntries
<1>step_down. \A i \in Server:
        NextIndexBound /\ TypeOK /\ LeaderStepDown(i) => NextIndexBound'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        MatchIndexBelowNextIndex /\ ResponseIndexBound /\ NextIndexBound
            /\ TypeOK /\ Receive(m) => NextIndexBound'
    <2>update_term. \A m \in messages:
            NextIndexBound /\ TypeOK /\ UpdateTerm(m.mdest, m.msource, m) =>
                NextIndexBound'
        BY MessageFieldsTypeOK DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => NextIndexBound'
        BY DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => NextIndexBound'
        BY DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => NextIndexBound'
        BY MessageFieldsTypeOK DEF HandleAppendEntriesRequest
    <2>append_entries_response. \A m \in messages:
            /\ MatchIndexBelowNextIndex

            /\ ResponseIndexBound
            /\ NextIndexBound
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => NextIndexBound'
        <3> SUFFICES ASSUME NEW m \in messages,
                            MatchIndexBelowNextIndex,
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
            BY DEF NextIndexBound
        <3>changed_server. CASE i = m.mdest
            <4>success. CASE m.msuccess
                BY <3>changed_server, <4>success, MessageFieldsTypeOK
                DEF HandleAppendEntriesResponse, TypeOK,
                    MsgTypeOK, ResponseIndexBound
            <4>failure. CASE ~m.msuccess
                <5>same_source. CASE j = m.msource
                    <6>log. log'[i] = log[i]
                        BY <3>changed_server, <4>failure
                        DEF HandleAppendEntriesResponse
                    <6>update. /\ nextIndex'[i][j] =
                                Max({nextIndex[i][j] - 1,
                                    matchIndex[i][j] + 1})
                               /\ UNCHANGED matchIndex
                        BY <3>changed_server, <4>failure,
                            <5>same_source
                        DEF HandleAppendEntriesResponse
                    <6>bound. /\ Max({nextIndex[i][j] - 1, matchIndex[i][j] + 1}) <= Len(log[i]) + 1
                              /\ matchIndex[i][j] <= Len(log[i])
                        <7>leader. state[i] = Leader
                            BY DEF HandleAppendEntriesResponse
                        <7>next_bound. nextIndex[i][j]
                                <= Len(log[i]) + 1
                            BY <7>leader, NextIndexBound
                        <7>match_less. matchIndex[i][j]
                                < nextIndex[i][j]
                            BY SMTT(30) DEF MatchIndexBelowNextIndex
                        <7>match_bound. matchIndex[i][j] + 1
                                <= Len(log[i]) + 1
                            BY <7>match_less, <7>next_bound,
                                NatLtLeqPlusOne, SMT
                            DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
                        <7> QED BY <7>next_bound, <7>match_bound,
                            MaxUpperBound, LenProperties, SMT
                    <6> QED BY <6>log, <6>update, <6>bound
                <5>other_source. CASE j # m.msource
                    BY <3>changed_server, <4>failure, <5>other_source,
                        NextIndexBound, LenProperties
                    DEF HandleAppendEntriesResponse, NextIndexBound
                <5> QED BY <5>same_source, <5>other_source
            <4> QED BY <3>changed_server, <4>success, <4>failure
        <3>other_server. CASE i # m.mdest
            BY <3>other_server
            DEF HandleAppendEntriesResponse, NextIndexBound
        <3> QED BY <3>changed_server, <3>other_server
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next, vars

LEMMA MessagesMonotonicNext ==
    [Next]_vars => messages \subseteq messages'
    BY
    DEF Next, Restart, Timeout, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        Send, WithMessage, WithMessages, vars

LEMMA WonMonotonicNext ==
    [Next]_vars =>
        \A candidate, term:
            Won(candidate, term) => Won(candidate, term)'
    BY MessagesMonotonicNext DEF Won, Started, VoteFor, Grant

LEMMA VoteRecordInvUnchanged ==
    /\ VoteRecordInv
    /\ UNCHANGED <<messages, currentTerm, votedFor>>
    => VoteRecordInv'
    BY DEF VoteRecordInv, VoteCurrentInv, VoteUniqueInv,
        StartedGrantInv, StartedCurrentInv, Grant, Started

LEMMA TimeoutGrantUnchanged ==
    \A i \in Server:
        Timeout(i) =>
            \A voter, candidate, term:
                Grant(voter, candidate, term)' <=>
                    Grant(voter, candidate, term)
    BY MessageTypesDistinct
    DEF Timeout, WithMessages, RequestVoteRequests, Grant

LEMMA TimeoutStartsElection ==
    \A i \in Server:
        /\ TypeOK
        /\ Timeout(i)
        =>
            \/ Server = {i}
            \/ \E m \in messages':
                /\ m.mtype = RequestVoteRequest
                /\ m.mterm = currentTerm'[i]
                /\ m.msource = i
<1> SUFFICES ASSUME NEW i \in Server, TypeOK, Timeout(i)
             PROVE  \/ Server = {i}
                    \/ \E m \in messages':
                        /\ m.mtype = RequestVoteRequest
                        /\ m.mterm = currentTerm'[i]
                        /\ m.msource = i
    OBVIOUS
<1>singleton. CASE Server = {i}
    BY <1>singleton
<1>multiple. CASE Server # {i}
    <2> USE <1>multiple
    <2>1. Server \ {i} # {} OBVIOUS
    <2>2. PICK j \in Server \ {i} : TRUE BY <2>1
    <2>3. [mtype |-> RequestVoteRequest,
            mterm |-> currentTerm[i] + 1,
            mlastLogTerm |-> LastTerm(log[i]),
            mlastLogIndex |-> Len(log[i]),
            msource |-> i,
            mdest |-> j] \in messages'
        BY DEF Timeout, WithMessages, RequestVoteRequests
    <2>4. currentTerm'[i] = currentTerm[i] + 1
        BY DEF Timeout, TypeOK, ServerVarsTypeOK
    <2>5. \E m \in messages':
                /\ m.mtype = RequestVoteRequest
                /\ m.mterm = currentTerm'[i]
                /\ m.msource = i
        BY <2>3, <2>4
    <2> QED BY <2>5
<1> QED BY <1>singleton, <1>multiple

LEMMA VoteCurrentInvTimeout ==
    \A i \in Server:
    /\ InductiveInvariant
    /\ VoteRecordInv
    /\ Timeout(i)
    => VoteCurrentInv'
<1> SUFFICES ASSUME NEW i \in Server, InductiveInvariant, VoteRecordInv,
                      Timeout(i), NEW voter \in Server,
                      NEW candidate \in Server, NEW term \in Nat,
                      Grant(voter, candidate, term)',
                      currentTerm'[voter] = term
             PROVE  votedFor'[voter] = candidate
    BY DEF VoteCurrentInv
<1>changed_server. CASE voter = i
    <2> USE voter = i
    <2>1. Grant(voter, candidate, term)
        BY TimeoutGrantUnchanged
    <2>2. term <= currentTerm[voter]
        BY <2>1 DEF InductiveInvariant, SendInvariant, Grant
    <2>3. /\ currentTerm'[voter] = currentTerm[voter] + 1
           /\ currentTerm[voter] \in Nat
        BY DEF Timeout, InductiveInvariant, TypeOK, ServerVarsTypeOK
    <2> QED BY <2>2, <2>3
<1>other_server. CASE voter # i
    <2> USE voter # i
    <2>1. Grant(voter, candidate, term)
        BY TimeoutGrantUnchanged
    <2>2. /\ currentTerm'[voter] = currentTerm[voter]
           /\ votedFor'[voter] = votedFor[voter]
        BY DEF Timeout, InductiveInvariant, TypeOK, ServerVarsTypeOK
    <2> QED BY <2>1, <2>2
        DEF VoteRecordInv, VoteCurrentInv
<1> QED BY <1>changed_server, <1>other_server

LEMMA VoteUniqueInvTimeout ==
    \A i \in Server:
    /\ VoteRecordInv
    /\ Timeout(i)
    => VoteUniqueInv'
    BY TimeoutGrantUnchanged
    DEF VoteRecordInv, VoteCurrentInv, VoteUniqueInv,
        StartedGrantInv, StartedCurrentInv

LEMMA StartedGrantInvTimeout ==
    \A i \in Server:
    /\ InductiveInvariant
    /\ VoteRecordInv
    /\ Timeout(i)
    => StartedGrantInv'
    BY TimeoutGrantUnchanged, MessageTypesDistinct
    DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK, SendInvariant,
        VoteRecordInv, VoteCurrentInv, VoteUniqueInv,
        StartedGrantInv, StartedCurrentInv,
        Timeout, WithMessages, RequestVoteRequests, Started, Grant

LEMMA StartedCurrentInvTimeout ==
    \A i \in Server:
    /\ InductiveInvariant
    /\ VoteRecordInv
    /\ Timeout(i)
    => StartedCurrentInv'
    BY MessageTypesDistinct
    DEF InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK,
        VoteRecordInv, VoteCurrentInv, VoteUniqueInv,
        StartedGrantInv, StartedCurrentInv,
        Timeout, WithMessages, RequestVoteRequests, Started

LEMMA VoteRecordInvNext ==
    InductiveInvariant /\ [Next]_vars => VoteRecordInv'
<1> USE MessageFieldsTypeOK, MessageTypesDistinct, NilNotServer
    DEF InductiveInvariant, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, VoteRecordInv, VoteCurrentInv, VoteUniqueInv,
        StartedGrantInv, StartedCurrentInv, Grant, Started
<1>stutter. InductiveInvariant /\ UNCHANGED vars => VoteRecordInv'
    BY DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) => VoteRecordInv'
    BY VoteRecordInvUnchanged, Zenon DEF Restart, InductiveInvariant
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) => VoteRecordInv'
    BY VoteCurrentInvTimeout, VoteUniqueInvTimeout,
        StartedGrantInvTimeout, StartedCurrentInvTimeout
    DEF InductiveInvariant, VoteRecordInv
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => VoteRecordInv'
    BY VoteRecordInvUnchanged, Zenon DEF BecomeLeader, InductiveInvariant
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => VoteRecordInv'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => VoteRecordInv'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) => VoteRecordInv'
    BY DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => VoteRecordInv'
    BY VoteRecordInvUnchanged, Zenon DEF LeaderStepDown, InductiveInvariant
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) => VoteRecordInv'
    <2>update_term. \A m \in messages:
            InductiveInvariant /\ UpdateTerm(m.mdest, m.msource, m) =>
                VoteRecordInv'
        <3> SUFFICES ASSUME NEW m \in messages, InductiveInvariant,
                             UpdateTerm(m.mdest, m.msource, m)
                    PROVE VoteRecordInv'
            OBVIOUS
        <3>messages. UNCHANGED messages
            BY DEF UpdateTerm
        <3>term. currentTerm'[m.mdest] > currentTerm[m.mdest]
            BY DEF UpdateTerm
        <3>others. \A i \in Server: i # m.mdest =>
                /\ currentTerm'[i] = currentTerm[i]
                /\ votedFor'[i] = votedFor[i]
            BY DEF UpdateTerm
        <3>grants. \A voter, candidate \in Server, term \in Nat:
                Grant(voter, candidate, term) => term <= currentTerm[voter]
            BY DEF SendInvariant
        <3>starts. \A voter \in Server, term \in Nat:
                /\ Server # {voter}
                /\ Started(voter, term)
                => term <= currentTerm[voter]
            BY DEF SendInvariant
        <3>current_vote. VoteCurrentInv'
            <4> SUFFICES ASSUME NEW voter \in Server,
                                 NEW candidate \in Server, NEW term \in Nat,
                                 Grant(voter, candidate, term)',
                                 currentTerm'[voter] = term
                        PROVE votedFor'[voter] = candidate
                BY DEF VoteCurrentInv
            <4>grant. Grant(voter, candidate, term)
                BY <3>messages
            <4>bound. term <= currentTerm[voter]
                BY <3>grants, <4>grant
            <4>changed. CASE voter = m.mdest
                BY <4>changed, <3>term, <4>bound, SMT
            <4>other. CASE voter # m.mdest
                BY <4>other, <3>others, <4>grant
            <4> QED BY <4>changed, <4>other
        <3>current_start. StartedCurrentInv'
            <4> SUFFICES ASSUME NEW voter \in Server, NEW term \in Nat,
                                 Server # {voter}, Started(voter, term)',
                                 currentTerm'[voter] = term
                        PROVE votedFor'[voter] = voter
                BY DEF StartedCurrentInv
            <4>start. Started(voter, term)
                BY <3>messages
            <4>bound. term <= currentTerm[voter]
                BY <3>starts, <4>start
            <4>changed. CASE voter = m.mdest
                BY <4>changed, <3>term, <4>bound, SMT
            <4>other. CASE voter # m.mdest
                BY <4>other, <3>others, <4>start
            <4> QED BY <4>changed, <4>other
        <3> QED BY <3>messages, <3>current_vote, <3>current_start
    <2>request_vote_request. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => VoteRecordInv'
        BY SMTT(30)
        DEF HandleRequestVoteRequest, Send, WithMessage, WithMessages
    <2>request_vote_response. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => VoteRecordInv'
        BY VoteRecordInvUnchanged, Zenon
        DEF HandleRequestVoteResponse, InductiveInvariant
    <2>append_entries_request. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => VoteRecordInv'
        BY SMTT(20), MessageTypesDistinct
        DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages
    <2>append_entries_response. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => VoteRecordInv'
        BY VoteRecordInvUnchanged, Zenon
        DEF HandleAppendEntriesResponse, InductiveInvariant
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA ActiveVotesInvNext ==
    InductiveInvariant /\ [Next]_vars => ActiveVotesInv'
<1> USE MessageFieldsTypeOK, MessageTypesDistinct, ServerStatesDistinct
    DEF InductiveInvariant, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, CandidateVarsTypeOK, VoteRecordInv, ActiveVotesInv,
        Started, VoteFor, Grant
<1>stutter. InductiveInvariant /\ UNCHANGED vars => ActiveVotesInv'
    BY DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) => ActiveVotesInv'
    BY DEF Restart
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) => ActiveVotesInv'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant, Timeout(i),
                         NEW candidate \in Server,
                         state'[candidate] \in {Candidate, Leader}
                PROVE
                  /\ \/ Server = {candidate}
                     \/ \E m \in messages':
                          /\ m.mtype = RequestVoteRequest
                          /\ m.mterm = currentTerm'[candidate]
                          /\ m.msource = candidate
                  /\ \A voter \in votesGranted'[candidate]:
                       \/ voter = candidate
                       \/ \E m \in messages':
                            /\ m.mtype = RequestVoteResponse
                            /\ m.mterm = currentTerm'[candidate]
                            /\ m.mvoteGranted
                            /\ m.msource = voter
                            /\ m.mdest = candidate
        BY DEF ActiveVotesInv, Started, VoteFor, Grant
    <2>changed_server. CASE candidate = i
        <3> USE <2>changed_server
        <3>1. \/ Server = {candidate}
                \/ \E m \in messages':
                    /\ m.mtype = RequestVoteRequest
                    /\ m.mterm = currentTerm'[candidate]
                    /\ m.msource = candidate
            BY TimeoutStartsElection DEF InductiveInvariant
        <3>2. \A voter \in votesGranted'[candidate]: voter = candidate
            BY DEF Timeout
        <3> QED BY <3>1, <3>2
    <2>other_server. CASE candidate # i
        <3> USE <2>other_server
        <3>1. messages \subseteq messages'
            BY DEF Timeout, WithMessages
        <3>2. /\ currentTerm'[candidate] = currentTerm[candidate]
              /\ state'[candidate] = state[candidate]
              /\ votesGranted'[candidate] = votesGranted[candidate]
            BY DEF Timeout
        <3> QED BY <3>1, <3>2
            DEF InductiveInvariant, ActiveVotesInv, Started, VoteFor, Grant
    <2> QED BY <2>changed_server, <2>other_server
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => ActiveVotesInv'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => ActiveVotesInv'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => ActiveVotesInv'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) => ActiveVotesInv'
    BY DEF AppendEntries, Send, WithMessage, WithMessages,
        AppendEntriesMessage
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => ActiveVotesInv'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) => ActiveVotesInv'
    BY DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA LeaderQuorumInvNext ==
    InductiveInvariant /\ [Next]_vars => LeaderQuorumInv'
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMTT(30)
    DEF Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive, UpdateTerm,
        HandleMsg, HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse,
        InductiveInvariant, TypeOK, MsgTypeOK, ServerVarsTypeOK,
        CandidateVarsTypeOK, LeaderQuorumInv

LEMMA ActiveLeaderWon ==
    InductiveInvariant =>
        \A i \in Server:
            state[i] = Leader => Won(i, currentTerm[i])
    BY SMT
    DEF InductiveInvariant, TypeOK, ServerVarsTypeOK,
        CandidateVarsTypeOK, ActiveVotesInv, LeaderQuorumInv, Won

LEMMA TermOwnerStable ==
    \A owner \in Server, term \in Nat, index \in Nat:
        /\ TermOwner(owner, term, index)
        /\ Won(owner, term)'
        /\ currentTerm'[owner] = currentTerm[owner]
        /\ state'[owner] = state[owner]
        /\ log'[owner] = log[owner]
        => TermOwner(owner, term, index)'
    BY DEF TermOwner, OwnerActive, LogHasTermAt

LEMMA TermOwnerNext ==
    \A owner \in Server, term \in Nat, index \in Nat:
        /\ InductiveInvariant
        /\ [Next]_vars
        /\ TermOwner(owner, term, index)
        => TermOwner(owner, term, index)'
<1> SUFFICES ASSUME NEW owner \in Server, NEW term \in Nat,
                      NEW index \in Nat, InductiveInvariant, [Next]_vars,
                      TermOwner(owner, term, index)
             PROVE  TermOwner(owner, term, index)'
    OBVIOUS
<1> USE WonMonotonicNext, AppendProperties, LenProperties,
        ServerStatesDistinct
    DEF InductiveInvariant, TypeOK, ServerVarsTypeOK,
        LogVarsTypeOK,
        TermOwner, OwnerActive, LogHasTermAt
<1>stutter. InductiveInvariant /\ UNCHANGED vars /\
        TermOwner(owner, term, index) => TermOwner(owner, term, index)'
    BY DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) /\ TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant, Restart(i),
                         TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>changed_server. CASE owner = i
        <3> USE <2>changed_server
        <3>1. Won(owner, term)' BY WonMonotonicNext
        <3>2. /\ term <= currentTerm'[owner]
              /\ ~OwnerActive(owner, term)'
            BY ServerStatesDistinct DEF Restart, TermOwner, OwnerActive
        <3> QED BY <3>1, <3>2 DEF TermOwner
    <2>other_server. CASE owner # i
        <3> USE <2>other_server
        <3>1. Won(owner, term)' BY WonMonotonicNext
        <3>2. /\ currentTerm'[owner] = currentTerm[owner]
              /\ state'[owner] = state[owner]
              /\ log'[owner] = log[owner]
            BY DEF Restart
        <3> QED BY <3>1, <3>2, TermOwnerStable
    <2> QED BY <2>changed_server, <2>other_server
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) /\ TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant, Timeout(i),
                         TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>changed_server. CASE owner = i
        BY <2>changed_server, WonMonotonicNext
        DEF Timeout, TermOwner, OwnerActive
    <2>other_server. CASE owner # i
        BY <2>other_server, TermOwnerStable, WonMonotonicNext DEF Timeout
    <2> QED BY <2>changed_server, <2>other_server
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) /\
            TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant,
                         BecomeLeader(i), TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>changed_server. CASE owner = i
        BY <2>changed_server, WonMonotonicNext DEF BecomeLeader,
            TermOwner, OwnerActive, LogHasTermAt
    <2>other_server. CASE owner # i
        BY <2>other_server, TermOwnerStable, WonMonotonicNext DEF BecomeLeader
    <2> QED BY <2>changed_server, <2>other_server
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) /\
            TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                         InductiveInvariant, ClientRequest(i, v),
                         TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>changed_server. CASE owner = i
        <3> USE <2>changed_server
        <3>1. Won(owner, term)' BY WonMonotonicNext
        <3>2. /\ currentTerm'[owner] = currentTerm[owner]
              /\ state'[owner] = state[owner]
              /\ log'[owner] = Append(log[owner],
                    [term |-> currentTerm[owner], value |-> v])
            BY DEF ClientRequest
        <3>3. OwnerActive(owner, term)' =>
                LogHasTermAt(owner, term, index)
            BY <3>2 DEF TermOwner, OwnerActive
        <3>4. OwnerActive(owner, term)' =>
                LogHasTermAt(owner, term, index)'
            <4> SUFFICES ASSUME OwnerActive(owner, term)'
                         PROVE  LogHasTermAt(owner, term, index)'
                OBVIOUS
            <4>1. LogHasTermAt(owner, term, index) BY <3>3
            <4>2. /\ log[owner] \in Seq(LogEntry)
                  /\ [term |-> currentTerm[owner], value |-> v] \in LogEntry
                BY DEF InductiveInvariant, TypeOK,
                    ServerVarsTypeOK, LogVarsTypeOK, LogEntry
            <4>3. index \in 1..Len(log[owner])
                BY <4>1, <4>2, LenProperties DEF LogHasTermAt
            <4>4. Append(log[owner],
                        [term |-> currentTerm[owner], value |-> v])[index]
                    = log[owner][index]
                BY <4>2, <4>3, AppendProperties
            <4>5. index \in DOMAIN log'[owner]
                BY <3>2, <4>2, <4>3, AppendProperties, LenProperties
            <4>6. log'[owner][index].term = term
                BY <3>2, <4>1, <4>4 DEF LogHasTermAt
            <4> QED BY <4>5, <4>6 DEF LogHasTermAt
        <3> QED BY <3>1, <3>2, <3>4 DEF TermOwner
    <2>other_server. CASE owner # i
        BY <2>other_server, TermOwnerStable, WonMonotonicNext DEF ClientRequest
    <2> QED BY <2>changed_server, <2>other_server
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) /\
            TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) /\
            TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    BY DEF AppendEntries, Send, WithMessage, WithMessages
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) /\
            TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant,
                         LeaderStepDown(i), TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>changed_server. CASE owner = i
        <3> USE owner = i
        <3> QED BY WonMonotonicNext, ServerStatesDistinct
            DEF LeaderStepDown, TermOwner, OwnerActive
    <2>other_server. CASE owner # i
        <3> USE owner # i
        <3> QED BY TermOwnerStable, WonMonotonicNext DEF LeaderStepDown
    <2> QED BY <2>changed_server, <2>other_server
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) /\ TermOwner(owner, term, index) =>
            TermOwner(owner, term, index)'
    <2> SUFFICES ASSUME NEW m \in messages, InductiveInvariant, Receive(m),
                         TermOwner(owner, term, index)
                PROVE  TermOwner(owner, term, index)'
        OBVIOUS
    <2>recipient. CASE owner = m.mdest
        <3> USE <2>recipient
        <3>1. Won(owner, term)' BY WonMonotonicNext
        <3>2. currentTerm[owner] <= currentTerm'[owner]
            BY MessageFieldsTypeOK, SMTT(30)
            DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest,
                HandleAppendEntriesResponse
        <3>3. /\ term <= currentTerm[owner]
              /\ term \in Nat
              /\ currentTerm[owner] \in Nat
              /\ currentTerm'[owner] \in Nat
            BY <3>2, TypeOKNext
            DEF TermOwner, InductiveInvariant,
                TypeOK, ServerVarsTypeOK
        <3>4. term <= currentTerm'[owner]
            BY <3>2, <3>3, NatLeqTransitive
        <3>5. \/ ~OwnerActive(owner, term)'
              \/ /\ currentTerm'[owner] = currentTerm[owner]
                    /\ state'[owner] = state[owner]
                    /\ log'[owner] = log[owner]
            BY MessageFieldsTypeOK, ServerStatesDistinct, SMTT(30)
            DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest,
                HandleAppendEntriesResponse, OwnerActive
        <3> QED BY <3>1, <3>4, <3>5
            DEF TermOwner, OwnerActive, LogHasTermAt
    <2>other_server. CASE owner # m.mdest
        BY <2>other_server, TermOwnerStable, WonMonotonicNext, MessageFieldsTypeOK
        DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
            HandleRequestVoteResponse, HandleAppendEntriesRequest,
            HandleAppendEntriesResponse
    <2> QED BY <2>recipient, <2>other_server
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA AppendPreservesTermBound ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, term \in Nat:
        /\ \A index \in DOMAIN entries: entries[index].term <= term
        /\ entry.term <= term
        => \A index \in DOMAIN Append(entries, entry):
            Append(entries, entry)[index].term <= term
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                      NEW term \in Nat,
                      \A oldIndex \in DOMAIN entries:
                          entries[oldIndex].term <= term,
                      entry.term <= term,
                      NEW index \in DOMAIN Append(entries, entry)
             PROVE  Append(entries, entry)[index].term <= term
    OBVIOUS
<1>1. /\ DOMAIN entries = 1..Len(entries)
       /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
    BY AppendProperties, LenProperties
<1>old. CASE index \in DOMAIN entries
    BY <1>old, <1>1, AppendProperties
<1>new. CASE index \notin DOMAIN entries
    BY <1>new, <1>1, AppendProperties
<1> QED BY <1>old, <1>new

LEMMA SubSeqPreservesTermBound ==
    \A entries \in Seq(LogEntry), last, term \in Nat:
        /\ last <= Len(entries)
        /\ \A index \in DOMAIN entries: entries[index].term <= term
        => \A index \in DOMAIN SubSeq(entries, 1, last):
            SubSeq(entries, 1, last)[index].term <= term
    BY LenProperties, SubSeqProperties

LEMMA LogTermBoundInvNext ==
    InductiveInvariant /\ [Next]_vars => LogTermBoundInv'
<1> USE MessageFieldsTypeOK, MessageTypesDistinct, ServerStatesDistinct,
        AppendProperties, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, LogVarsTypeOK, LogTermBoundInv,
        MessageTermBoundInv
<1>stutter. InductiveInvariant /\ UNCHANGED vars => LogTermBoundInv'
    BY DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) => LogTermBoundInv'
    BY DEF Restart
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) => LogTermBoundInv'
    <2> SUFFICES ASSUME NEW i \in Server, InductiveInvariant, Timeout(i),
                         NEW k \in Server, NEW index \in DOMAIN log'[k]
                PROVE  log'[k][index].term <= currentTerm'[k]
        BY DEF LogTermBoundInv
    <2>changed_server. CASE k = i
        <3> USE <2>changed_server
        <3>1. log'[k] = log[k] BY DEF Timeout
        <3>2. currentTerm'[k] = currentTerm[k] + 1
            BY DEF Timeout, InductiveInvariant, TypeOK,
                ServerVarsTypeOK
        <3>3. log[k][index].term <= currentTerm[k]
            BY <3>1 DEF InductiveInvariant, LogTermBoundInv
        <3>4. currentTerm[k] \in Nat
            BY DEF InductiveInvariant, TypeOK,
                ServerVarsTypeOK
        <3>5. log'[k][index].term = log[k][index].term
            BY <3>1
        <3>6. log[k][index].term \in Nat
            BY <3>1, ElementOfSeq
            DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LogEntry
        <3>7. currentTerm[k] <= currentTerm'[k]
            BY <3>2, <3>4
        <3>8. currentTerm'[k] \in Nat BY <3>2, <3>4
        <3> QED BY <3>3, <3>5, <3>6, <3>7, <3>8,
            NatLeqTransitive
    <2>other_server. CASE k # i
        BY <2>other_server DEF Timeout
    <2> QED BY <2>changed_server, <2>other_server
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => LogTermBoundInv'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => LogTermBoundInv'
    <2> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                         InductiveInvariant, ClientRequest(i, v),
                         NEW k \in Server, NEW index \in DOMAIN log'[k]
                PROVE  log'[k][index].term <= currentTerm'[k]
        BY DEF LogTermBoundInv
    <2>changed_server. CASE k = i
        <3> USE <2>changed_server
        <3>1. /\ log[i] \in Seq(LogEntry)
              /\ currentTerm[i] \in Nat
              /\ [term |-> currentTerm[i], value |-> v] \in LogEntry
            BY DEF InductiveInvariant, TypeOK,
                ServerVarsTypeOK, LogVarsTypeOK, LogEntry
        <3>2. \A oldIndex \in DOMAIN log[i]:
                log[i][oldIndex].term <= currentTerm[i]
            BY DEF InductiveInvariant, LogTermBoundInv
        <3>3. [term |-> currentTerm[i], value |-> v].term <= currentTerm[i]
            BY <3>1, SMT
        <3>4. \A newIndex \in
                    DOMAIN Append(log[i],
                        [term |-> currentTerm[i], value |-> v]):
                Append(log[i],
                    [term |-> currentTerm[i], value |-> v])[newIndex].term
                    <= currentTerm[i]
            BY <3>1, <3>2, <3>3, AppendPreservesTermBound, Zenon
        <3> QED BY <3>4 DEF ClientRequest
    <2>other_server. CASE k # i
        BY <2>other_server DEF ClientRequest
    <2> QED BY <2>changed_server, <2>other_server
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => LogTermBoundInv'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) => LogTermBoundInv'
    BY DEF AppendEntries
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => LogTermBoundInv'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) => LogTermBoundInv'
    <2>update_term. \A m \in messages:
            InductiveInvariant /\ UpdateTerm(m.mdest, m.msource, m) =>
                LogTermBoundInv'
        <3> SUFFICES ASSUME NEW m \in messages, InductiveInvariant,
                             UpdateTerm(m.mdest, m.msource, m),
                             NEW k \in Server,
                             NEW index \in DOMAIN log'[k]
                    PROVE  log'[k][index].term <= currentTerm'[k]
            BY DEF LogTermBoundInv
        <3>changed_server. CASE k = m.mdest
            <4> USE <3>changed_server
            <4>1. log'[k] = log[k] BY DEF UpdateTerm
            <4>2. currentTerm'[k] = m.mterm
                BY MessageFieldsTypeOK
                DEF UpdateTerm, InductiveInvariant, TypeOK,
                    MsgTypeOK, ServerVarsTypeOK
            <4>3. log[k][index].term <= currentTerm[k]
                BY <4>1 DEF InductiveInvariant, LogTermBoundInv
            <4>4. /\ log'[k][index].term = log[k][index].term
                  /\ m.mterm > currentTerm[k]
                BY <4>1, MessageFieldsTypeOK DEF UpdateTerm
            <4>5. /\ log[k][index].term \in Nat
                  /\ currentTerm[k] \in Nat
                  /\ m.mterm \in Nat
                BY <4>1, MessageFieldsTypeOK, ElementOfSeq
                DEF InductiveInvariant, TypeOK, MsgTypeOK,
                    ServerVarsTypeOK, LogVarsTypeOK, LogEntry
            <4> QED BY <4>2, <4>3, <4>4, <4>5,
                NatLeqTransitive
        <3>other_server. CASE k # m.mdest
            BY <3>other_server DEF UpdateTerm, InductiveInvariant, LogTermBoundInv
        <3> QED BY <3>changed_server, <3>other_server
    <2>request_vote_request. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => LogTermBoundInv'
        BY DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => LogTermBoundInv'
        BY DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => LogTermBoundInv'
        <3> SUFFICES ASSUME NEW m \in messages, InductiveInvariant,
                             m.mtype = AppendEntriesRequest,
                             HandleAppendEntriesRequest(
                                 m.mdest, m.msource, m),
                             NEW k \in Server,
                             NEW index \in DOMAIN log'[k]
                    PROVE  log'[k][index].term <= currentTerm'[k]
            BY DEF LogTermBoundInv
        <3>recipient. CASE k = m.mdest
            <4> USE <3>recipient
            <4>1. /\ log[k] \in Seq(LogEntry)
                  /\ currentTerm[k] \in Nat
                  /\ \A oldIndex \in DOMAIN log[k]:
                        log[k][oldIndex].term <= currentTerm[k]
                BY MessageFieldsTypeOK
                DEF InductiveInvariant, TypeOK, LogVarsTypeOK,
                    ServerVarsTypeOK, LogTermBoundInv
            <4>2. \A entryIndex \in DOMAIN m.mentries:
                    m.mentries[entryIndex].term <= m.mterm
                BY DEF InductiveInvariant, MessageTermBoundInv
            <4>3. /\ currentTerm'[k] = currentTerm[k]
                  /\ \/ log'[k] = log[k]
                     \/ /\ log'[k] =
                                Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1])
                        /\ m.mprevLogIndex \in Nat
                        /\ m.mprevLogIndex <= Len(log[k])
                        /\ m.mentries # << >>
                        /\ m.mterm = currentTerm[k]
                BY MessageFieldsTypeOK, SMTT(30)
                DEF HandleAppendEntriesRequest,
                    InductiveInvariant, TypeOK, MsgTypeOK
            <4>unchanged. CASE log'[k] = log[k]
                BY <4>unchanged, <4>1, <4>3
            <4>changed. CASE log'[k] # log[k]
                <5> USE <4>changed
                <5>1. /\ log'[k] =
                            Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1])
                       /\ m.mentries # << >>
                       /\ m.mterm = currentTerm[k]
                    BY <4>3
                <5>2. \A newIndex \in
                            DOMAIN SubSeq(log[k], 1, m.mprevLogIndex):
                        SubSeq(log[k], 1, m.mprevLogIndex)[newIndex].term
                            <= currentTerm[k]
                    BY <4>1, <4>3, SubSeqPreservesTermBound
                <5>3. SubSeq(log[k], 1, m.mprevLogIndex) \in Seq(LogEntry)
                    BY <4>1, <4>3, SubSeqTypeOK
                <5>entry_sequence. /\ m.mentries \in Seq(LogEntry)
                                    /\ DOMAIN m.mentries = 1..Len(m.mentries)
                                    /\ Len(m.mentries) > 0
                    BY <5>1, MessageFieldsTypeOK, EmptySeq, LenProperties
                    DEF InductiveInvariant, TypeOK, MsgTypeOK
                <5>entry_index. 1 \in DOMAIN m.mentries
                    BY <5>entry_sequence
                <5>4. /\ m.mentries[1] \in LogEntry
                       /\ m.mentries[1].term <= currentTerm[k]
                    BY <4>2, <5>1, <5>entry_sequence, <5>entry_index,
                        ElementOfSeq
                <5>5. \A newIndex \in
                            DOMAIN Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1]):
                        Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1])[newIndex].term
                            <= currentTerm[k]
                    BY <5>2, <5>3, <5>4,
                        AppendPreservesTermBound, Zenon
                <5> QED BY <4>3, <5>1, <5>5
            <4> QED BY <4>unchanged, <4>changed
        <3>other_server. CASE k # m.mdest
            BY <3>other_server
            DEF HandleAppendEntriesRequest, InductiveInvariant,
                LogTermBoundInv
        <3> QED BY <3>recipient, <3>other_server
    <2>append_entries_response. \A m \in messages:
            /\ InductiveInvariant
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => LogTermBoundInv'
        BY DEF HandleAppendEntriesResponse
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
        DEF Next, vars

LEMMA AppendEntriesEntriesTermBound ==
    \A i, j \in Server:
        /\ TypeOK
        /\ LogTermBoundInv
        => \A index \in DOMAIN AppendEntriesEntries(i, j):
            AppendEntriesEntries(i, j)[index].term <= currentTerm[i]
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                      TypeOK, LogTermBoundInv, NEW index \in DOMAIN AppendEntriesEntries(i, j)
             PROVE  AppendEntriesEntries(i, j)[index].term <= currentTerm[i]
    OBVIOUS
<1>1. /\ AppendEntriesEntries(i, j) \in Seq(LogEntry)
       /\ DOMAIN AppendEntriesEntries(i, j) =
            1..Len(AppendEntriesEntries(i, j))
    BY AppendEntriesEntriesTypeOK, LenProperties
<1>2. /\ nextIndex[i][j] \in Nat \ {0}
       /\ AppendEntriesLastEntry(i, j) \in Nat
       /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY AppendEntriesLastEntryTypeOK
    DEF TypeOK, LeaderVarsTypeOK
<1>3. \A position \in
            nextIndex[i][j]..AppendEntriesLastEntry(i, j):
        log[i][position] \in LogEntry
    BY <1>2, ElementOfSeq DEF TypeOK, LogVarsTypeOK
<1>4. Len(AppendEntriesEntries(i, j)) =
        IF nextIndex[i][j] <= AppendEntriesLastEntry(i, j)
        THEN AppendEntriesLastEntry(i, j) - nextIndex[i][j] + 1
        ELSE 0
    BY <1>2, <1>3, SubSeqProperties DEF AppendEntriesEntries
<1>5. nextIndex[i][j] + index - 1 \in DOMAIN log[i]
    BY <1>1, <1>2, <1>4, LenProperties
    DEF TypeOK, LogVarsTypeOK
<1>6. AppendEntriesEntries(i, j)[index] =
        log[i][nextIndex[i][j] + index - 1]
    BY <1>1, <1>2, <1>3, <1>4, SubSeqProperties
    DEF AppendEntriesEntries
<1> QED BY <1>5, <1>6 DEF LogTermBoundInv

LEMMA MessageTermBoundInvNext ==
    InductiveInvariant /\ [Next]_vars => MessageTermBoundInv'
<1> USE MessageFieldsTypeOK, MessageTypesDistinct
    DEF InductiveInvariant, TypeOK, MsgTypeOK,
        MessageTermBoundInv
<1>stutter. InductiveInvariant /\ UNCHANGED vars => MessageTermBoundInv'
    BY DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) => MessageTermBoundInv'
    BY DEF Restart
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) => MessageTermBoundInv'
    BY DEF Timeout, WithMessages, RequestVoteRequests
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => MessageTermBoundInv'
    BY DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => MessageTermBoundInv'
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => MessageTermBoundInv'
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j) => MessageTermBoundInv'
    BY AppendEntriesEntriesTermBound, SMTT(30)
    DEF AppendEntries, Send, WithMessage, WithMessages, AppendEntriesMessage
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => MessageTermBoundInv'
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) => MessageTermBoundInv'
    BY SMTT(30)
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter
    DEF Next, vars

LEMMA OldLogEntryOwnerNext ==
    \A i \in Server:
    \A index \in DOMAIN log[i]:
        InductiveInvariant /\ [Next]_vars =>
            \E owner \in Server:
                TermOwnerPrime(owner, log[i][index].term, index)
<1> SUFFICES ASSUME NEW i \in Server, NEW index \in DOMAIN log[i],
                      InductiveInvariant, [Next]_vars
             PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, log[i][index].term, index)
    OBVIOUS
<1>1. \E owner \in Server:
        TermOwner(owner, log[i][index].term, index)
    BY DEF InductiveInvariant, LogElectionInv
<1> PICK owner \in Server:
        TermOwner(owner, log[i][index].term, index) BY <1>1
<1>2. /\ log[i][index].term \in Nat
       /\ index \in Nat
    BY ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LogEntry
<1> PICK entryTerm \in Nat:
        entryTerm = log[i][index].term BY <1>2
<1>3. TermOwner(owner, entryTerm, index) BY SMT
<1>4. TermOwner(owner, entryTerm, index)'
    BY <1>2, <1>3, TermOwnerNext
<1>5. TermOwnerPrime(owner, entryTerm, index)
    BY <1>4
    DEF TermOwnerPrime, WonPrime, StartedPrime, VoteForPrime, GrantPrime,
        TermOwner, Won, Started, VoteFor, Grant, OwnerActive, LogHasTermAt
<1> QED BY <1>5

LEMMA LogElectionUnchanged ==
    /\ InductiveInvariant
    /\ [Next]_vars
    /\ UNCHANGED log
    => LogElectionInv'
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, UNCHANGED log,
                      NEW i \in Server, NEW index \in DOMAIN log'[i]
             PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, log'[i][index].term, index)
    BY DEF LogElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
        VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor, Grant,
        OwnerActive, LogHasTermAt
<1>1. /\ index \in DOMAIN log[i]
       /\ log'[i][index].term = log[i][index].term
    BY SMT
<1>2. \E owner \in Server:
        TermOwner(owner, log[i][index].term, index)
    BY <1>1 DEF InductiveInvariant, LogElectionInv
<1> PICK owner \in Server:
        TermOwner(owner, log[i][index].term, index) BY <1>2
<1>3. /\ log[i][index].term \in Nat
       /\ index \in Nat
    BY <1>1, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LogEntry
<1>4. TermOwner(owner, log[i][index].term, index)'
    BY <1>3, TermOwnerNext
<1>5. TermOwnerPrime(owner, log[i][index].term, index)
    BY <1>4
    DEF TermOwnerPrime, WonPrime, StartedPrime, VoteForPrime, GrantPrime,
        TermOwner, Won, Started, VoteFor, Grant, OwnerActive, LogHasTermAt
<1> QED BY <1>1, <1>5 DEF TermOwnerPrime

LEMMA MessageElectionUnchanged ==
    /\ InductiveInvariant
    /\ [Next]_vars
    /\ UNCHANGED messages
    => MessageElectionInv'
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, UNCHANGED messages,
                      NEW m \in messages',
                      m.mtype = AppendEntriesRequest,
                      NEW index \in DOMAIN m.mentries
             PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, m.mentries[index].term,
                                       m.mprevLogIndex + index)
    BY DEF MessageElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
        VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor, Grant,
        OwnerActive, LogHasTermAt
<1>1. \E owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index)
    BY DEF InductiveInvariant, MessageElectionInv
<1> PICK owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index) BY <1>1
<1>2. /\ m.mentries[index].term \in Nat
       /\ m.mprevLogIndex + index \in Nat
    BY MessageFieldsTypeOK, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogEntry
<1>3. TermOwner(owner, m.mentries[index].term,
                m.mprevLogIndex + index)'
    BY <1>2, TermOwnerNext
<1>4. TermOwnerPrime(owner, m.mentries[index].term,
                     m.mprevLogIndex + index)
    BY <1>3
    DEF TermOwnerPrime, WonPrime, StartedPrime, VoteForPrime, GrantPrime,
        TermOwner, Won, Started, VoteFor, Grant, OwnerActive, LogHasTermAt
<1> QED BY <1>4

LEMMA MessageElectionNoNewRequests ==
    /\ InductiveInvariant
    /\ [Next]_vars
    /\ messages \subseteq messages'
    /\ \A m \in messages' \ messages:
        m.mtype # AppendEntriesRequest
    => MessageElectionInv'
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                      messages \subseteq messages',
                      \A newMessage \in messages' \ messages:
                          newMessage.mtype # AppendEntriesRequest,
                      NEW m \in messages',
                      m.mtype = AppendEntriesRequest,
                      NEW index \in DOMAIN m.mentries
             PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, m.mentries[index].term,
                            m.mprevLogIndex + index)
    BY DEF MessageElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
        VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor, Grant,
        OwnerActive, LogHasTermAt
<1>1. m \in messages BY SMT
<1>2. \E owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index)
    BY <1>1 DEF InductiveInvariant, MessageElectionInv
<1> PICK owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index) BY <1>2
<1>3. /\ m.mentries[index].term \in Nat
       /\ m.mprevLogIndex + index \in Nat
    BY <1>1, MessageFieldsTypeOK, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogEntry
<1>4. TermOwner(owner, m.mentries[index].term,
                m.mprevLogIndex + index)'
    BY <1>3, TermOwnerNext
<1>5. TermOwnerPrime(owner, m.mentries[index].term,
                     m.mprevLogIndex + index)
    BY <1>4
    DEF TermOwnerPrime, WonPrime, StartedPrime, VoteForPrime, GrantPrime,
        TermOwner, Won, Started, VoteFor, Grant, OwnerActive, LogHasTermAt
<1> QED BY <1>5

LEMMA LogElectionInvNext ==
    InductiveInvariant /\ [Next]_vars => LogElectionInv'
<1> USE TermOwnerNext, ActiveLeaderWon, MessageFieldsTypeOK,
        ServerStatesDistinct, AppendProperties, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK,
        ServerVarsTypeOK, LogVarsTypeOK, LogElectionInv, MessageElectionInv,
        TermOwner, OwnerActive, LogHasTermAt
<1>stutter. InductiveInvariant /\ UNCHANGED vars => LogElectionInv'
    BY LogElectionUnchanged DEF vars
<1>restart. \A i \in Server:
        InductiveInvariant /\ [Next]_vars /\ Restart(i) => LogElectionInv'
    BY LogElectionUnchanged DEF Restart
<1>timeout. \A i \in Server:
        InductiveInvariant /\ [Next]_vars /\ Timeout(i) => LogElectionInv'
    BY LogElectionUnchanged DEF Timeout
<1>leader. \A i \in Server:
        InductiveInvariant /\ [Next]_vars /\ BecomeLeader(i) => LogElectionInv'
    BY LogElectionUnchanged DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ [Next]_vars /\ ClientRequest(i, v) =>
            LogElectionInv'
    <2> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                         InductiveInvariant, [Next]_vars, ClientRequest(i, v),
                         NEW k \in Server, NEW index \in DOMAIN log'[k]
                PROVE  \E owner \in Server:
                    TermOwnerPrime(owner, log'[k][index].term, index)
        BY Zenon DEF LogElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
            VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor, Grant,
            OwnerActive, LogHasTermAt
    <2>other_server. CASE k # i
        <3> USE <2>other_server
        <3>1. /\ index \in DOMAIN log[k]
              /\ log'[k][index].term = log[k][index].term
            BY DEF ClientRequest
        <3>2. \E owner \in Server:
                TermOwnerPrime(owner, log[k][index].term, index)
            BY <3>1, OldLogEntryOwnerNext
        <3> QED BY <3>1, <3>2
    <2>changed_server. CASE k = i
        <3> USE <2>changed_server
        <3>old_entry. CASE index \in DOMAIN log[k]
            <4> USE <3>old_entry
            <4>1. log'[k][index].term = log[k][index].term
                BY AppendProperties DEF ClientRequest,
                    InductiveInvariant, TypeOK, LogVarsTypeOK,
                    LogEntry
            <4>2. \E owner \in Server:
                    TermOwnerPrime(owner, log[k][index].term, index)
                BY OldLogEntryOwnerNext
            <4> QED BY <4>1, <4>2
        <3>new_entry. CASE index \notin DOMAIN log[k]
            <4> USE <3>new_entry
            <4>1. /\ log'[k] = Append(log[k],
                            [term |-> currentTerm[k], value |-> v])
                  /\ currentTerm'[k] = currentTerm[k]
                  /\ state'[k] = Leader
                BY DEF ClientRequest
            <4>2. /\ log[k] \in Seq(LogEntry)
                  /\ [term |-> currentTerm[k], value |-> v] \in LogEntry
                  /\ DOMAIN log[k] = 1..Len(log[k])
                  /\ DOMAIN Append(log[k],
                        [term |-> currentTerm[k], value |-> v]) =
                        1..(Len(log[k]) + 1)
                BY AppendProperties, LenProperties
                DEF InductiveInvariant, TypeOK,
                    ServerVarsTypeOK, LogVarsTypeOK, LogEntry
            <4>3. index = Len(log[k]) + 1 BY <4>1, <4>2
            <4>4. log'[k][index].term = currentTerm[k]
                BY <4>1, <4>2, <4>3, AppendProperties
            <4>5. Won(k, currentTerm[k]) BY ActiveLeaderWon
                DEF ClientRequest
            <4>6. WonPrime(k, currentTerm[k])
                BY <4>5, MessagesMonotonicNext
                DEF WonPrime, StartedPrime, VoteForPrime, GrantPrime,
                    Won, Started, VoteFor, Grant
            <4>7. TermOwnerPrime(k, currentTerm[k], index)
                BY <4>1, <4>3, <4>4, <4>6 DEF TermOwnerPrime
            <4> QED BY <4>4, <4>7
        <3> QED BY <3>old_entry, <3>new_entry
    <2> QED BY <2>other_server, <2>changed_server
<1>commit. \A i \in Server:
        InductiveInvariant /\ [Next]_vars /\ AdvanceCommitIndex(i) =>
            LogElectionInv'
    BY LogElectionUnchanged DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ [Next]_vars /\ AppendEntries(i, j) =>
            LogElectionInv'
    BY LogElectionUnchanged DEF AppendEntries
<1>step_down. \A i \in Server:
        InductiveInvariant /\ [Next]_vars /\ LeaderStepDown(i) =>
            LogElectionInv'
    BY LogElectionUnchanged DEF LeaderStepDown
<1>receive. \A m \in messages:
        InductiveInvariant /\ [Next]_vars /\ Receive(m) => LogElectionInv'
    <2>update_term. \A m \in messages:
            InductiveInvariant /\ [Next]_vars /\
                UpdateTerm(m.mdest, m.msource, m) => LogElectionInv'
    BY LogElectionUnchanged DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ InductiveInvariant
            /\ [Next]_vars
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => LogElectionInv'
    BY LogElectionUnchanged DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ InductiveInvariant
            /\ [Next]_vars
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => LogElectionInv'
    BY LogElectionUnchanged DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ InductiveInvariant
            /\ [Next]_vars
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => LogElectionInv'
        <3> SUFFICES ASSUME NEW m \in messages, InductiveInvariant,
                             [Next]_vars, m.mtype = AppendEntriesRequest,
                             HandleAppendEntriesRequest(
                                 m.mdest, m.msource, m),
                             NEW k \in Server,
                             NEW index \in DOMAIN log'[k]
                    PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, log'[k][index].term, index)
            BY Zenon DEF LogElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
                VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor,
                Grant, OwnerActive, LogHasTermAt
        <3>other_server. CASE k # m.mdest
            <4> USE <3>other_server
            <4>1. /\ index \in DOMAIN log[k]
                  /\ log'[k][index].term = log[k][index].term
                BY DEF HandleAppendEntriesRequest
            <4>2. \E owner \in Server:
                    TermOwnerPrime(owner, log[k][index].term, index)
                BY <4>1, OldLogEntryOwnerNext, Zenon
            <4> QED BY <4>1, <4>2
        <3>recipient. CASE k = m.mdest
            <4> USE <3>recipient
            <4>1. \/ log'[k] = log[k]
                  \/ /\ log'[k] =
                            Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1])
                     /\ m.mentries # << >>
                     /\ m.mprevLogIndex \in Nat
                     /\ m.mprevLogIndex <= Len(log[k])
                     /\ m.mterm = currentTerm[k]
                BY MessageFieldsTypeOK, SMTT(30)
                DEF HandleAppendEntriesRequest,
                    InductiveInvariant, TypeOK, MsgTypeOK
            <4>2. \/ /\ index \in DOMAIN log[k]
                        /\ log'[k][index].term = log[k][index].term
                  \/ /\ m.mentries # << >>
                        /\ index = m.mprevLogIndex + 1
                        /\ log'[k][index].term = m.mentries[1].term
                <5>unchanged. CASE log'[k] = log[k]
                    BY <5>unchanged, <4>1
                <5>changed. CASE log'[k] # log[k]
                    <6> USE <5>changed
                    <6>1. /\ log'[k] =
                                Append(SubSeq(log[k], 1, m.mprevLogIndex), m.mentries[1])
                           /\ m.mentries # << >>
                           /\ m.mprevLogIndex \in Nat
                           /\ m.mprevLogIndex <= Len(log[k])
                        BY  <4>1
                    <6>2. /\ log[k] \in Seq(LogEntry)
                          /\ m.mentries \in Seq(LogEntry)
                          /\ DOMAIN log[k] = 1..Len(log[k])
                          /\ DOMAIN m.mentries = 1..Len(m.mentries)
                          /\ DOMAIN log'[k] = 1..(m.mprevLogIndex + 1)
                        BY <6>1, MessageFieldsTypeOK, EmptySeq,
                            ElementOfSeq, AppendProperties, LenProperties,
                            SubSeqProperties
                        DEF InductiveInvariant, TypeOK, MsgTypeOK, LogVarsTypeOK
                    <6>preserved. CASE index \in 1..m.mprevLogIndex
                        <7> USE <6>preserved
                        <7>1. /\ index \in DOMAIN SubSeq(log[k], 1, m.mprevLogIndex)
                              /\ index \in DOMAIN log[k]
                        BY <6>1, <6>2, SubSeqProperties
                        <7>2. log'[k][index] =
                                SubSeq(log[k], 1, m.mprevLogIndex)[index]
                        BY <6>1, <6>2, <7>1,
                            AppendProperties, SubSeqProperties
                        <7>3. SubSeq(log[k], 1, m.mprevLogIndex)[index]
                                = log[k][index]
                        BY <6>2, <7>1, SubSeqProperties
                        <7> QED BY <6>1, <7>2, <7>3
                    <6>appended. CASE index \notin 1..m.mprevLogIndex
                        <7> USE <6>appended
                        <7>1. index = m.mprevLogIndex + 1
                            BY <6>1, <6>2
                        <7>2. log'[k][index] = m.mentries[1]
                        BY <6>1, <6>2, <7>1, AppendProperties, SubSeqProperties
                        <7>3. /\ m.mentries # << >>
                              /\ log'[k][index].term = m.mentries[1].term
                        BY <6>1, <7>1, <7>2
                        <7> QED BY <7>1, <7>3
                    <6> QED BY <6>preserved, <6>appended
                <5> QED BY <5>unchanged, <5>changed
            <4>preserved. CASE /\ index \in DOMAIN log[k]
                               /\ log'[k][index].term = log[k][index].term
                <5> USE <4>preserved
                <5>1. /\ index \in DOMAIN log[k]
                      /\ log'[k][index].term = log[k][index].term
                    OBVIOUS
                <5>2. \E owner \in Server:
                        TermOwnerPrime(owner, log[k][index].term, index)
                    BY <5>1, OldLogEntryOwnerNext, Zenon
                <5> QED BY <5>1, <5>2
            <4>appended. CASE /\ m.mentries # << >>
                                 /\ index = m.mprevLogIndex + 1
                                 /\ log'[k][index].term = m.mentries[1].term
                <5> USE <4>appended
                <5>1. /\ m.mentries # << >>
                      /\ index = m.mprevLogIndex + 1
                      /\ log'[k][index].term = m.mentries[1].term
                    OBVIOUS
                <5>2. /\ m.mentries \in Seq(LogEntry)
                      /\ DOMAIN m.mentries = 1..Len(m.mentries)
                      /\ Len(m.mentries) > 0
                    BY MessageFieldsTypeOK, EmptySeq, LenProperties
                    DEF InductiveInvariant, TypeOK, MsgTypeOK
                <5>3. 1 \in DOMAIN m.mentries BY <5>2
                <5>4. m.mentries[1] \in LogEntry
                    BY <5>2, <5>3, ElementOfSeq
                <5>5. /\ m.mentries[1].term \in Nat
                      /\ m.mprevLogIndex \in Nat
                      /\ m.mprevLogIndex + 1 \in Nat
                    BY <5>4, MessageFieldsTypeOK
                    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogEntry
                <5> PICK entryTerm \in Nat:
                        entryTerm = m.mentries[1].term BY <5>5
                <5> PICK entryIndex \in Nat:
                        entryIndex = m.mprevLogIndex + 1 BY <5>5
                <5>6. \E owner \in Server:
                        TermOwner(owner, entryTerm, entryIndex)
                    BY <5>3 DEF InductiveInvariant, MessageElectionInv
                <5> PICK owner \in Server:
                        TermOwner(owner, entryTerm, entryIndex) BY <5>6
                <5>7. TermOwner(owner, entryTerm, entryIndex) BY SMT
                <5>8. /\ owner \in Server
                      /\ entryTerm \in Nat
                      /\ entryIndex \in Nat
                      /\ InductiveInvariant
                      /\ [Next]_vars
                      /\ TermOwner(owner, entryTerm, entryIndex)
                    BY <5>7
                <5>9. TermOwner(owner, entryTerm, entryIndex)'
                    <6>recipient_owner. CASE owner = m.mdest
                        BY <6>recipient_owner, <5>8, WonMonotonicNext,
                            MessageFieldsTypeOK, ServerStatesDistinct, SMTT(30)
                        DEF HandleAppendEntriesRequest, TermOwner,
                            OwnerActive, LogHasTermAt
                    <6>other_owner. CASE owner # m.mdest
                        BY <6>other_owner, <5>8, TermOwnerStable,
                            WonMonotonicNext, MessageFieldsTypeOK, SMTT(30)
                        DEF HandleAppendEntriesRequest
                    <6> QED BY <6>recipient_owner, <6>other_owner
                <5>10. TermOwnerPrime(owner, entryTerm, entryIndex)
                    BY <5>9
                    DEF TermOwnerPrime, WonPrime, StartedPrime,
                        VoteForPrime, GrantPrime, TermOwner, Won, Started,
                        VoteFor, Grant, OwnerActive, LogHasTermAt
                <5> QED BY <5>10
            <4> QED BY <4>2, <4>preserved, <4>appended
        <3> QED BY <3>other_server, <3>recipient
    <2>append_entries_response. \A m \in messages:
            /\ InductiveInvariant
            /\ [Next]_vars
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => LogElectionInv'
    BY LogElectionUnchanged DEF HandleAppendEntriesResponse
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response DEF Receive, HandleMsg
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter, SMT
        DEF Next, vars

LEMMA AppendEntriesEntriesSource ==
    \A i, j \in Server:
        TypeOK =>
        \A index \in DOMAIN AppendEntriesEntries(i, j):
            /\ nextIndex[i][j] + index - 1 \in DOMAIN log[i]
            /\ AppendEntriesEntries(i, j)[index] =
                log[i][nextIndex[i][j] + index - 1]
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server, TypeOK,
                      NEW index \in DOMAIN AppendEntriesEntries(i, j)
             PROVE  /\ nextIndex[i][j] + index - 1 \in DOMAIN log[i]
                    /\ AppendEntriesEntries(i, j)[index] =
                        log[i][nextIndex[i][j] + index - 1]
    OBVIOUS
<1>1. /\ AppendEntriesEntries(i, j) \in Seq(LogEntry)
       /\ DOMAIN AppendEntriesEntries(i, j) =
            1..Len(AppendEntriesEntries(i, j))
    BY AppendEntriesEntriesTypeOK, LenProperties
<1>2. /\ nextIndex[i][j] \in Nat \ {0}
       /\ AppendEntriesLastEntry(i, j) \in Nat
       /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY AppendEntriesLastEntryTypeOK
    DEF TypeOK, LeaderVarsTypeOK
<1>3. \A position \in
            nextIndex[i][j]..AppendEntriesLastEntry(i, j):
        log[i][position] \in LogEntry
    BY <1>2, ElementOfSeq DEF TypeOK, LogVarsTypeOK
<1>4. Len(AppendEntriesEntries(i, j)) =
        IF nextIndex[i][j] <= AppendEntriesLastEntry(i, j)
        THEN AppendEntriesLastEntry(i, j) - nextIndex[i][j] + 1
        ELSE 0
    BY <1>2, <1>3, SubSeqProperties DEF AppendEntriesEntries
<1>5. nextIndex[i][j] + index - 1 \in DOMAIN log[i]
    BY <1>1, <1>2, <1>4, LenProperties
    DEF TypeOK, LogVarsTypeOK
<1>6. AppendEntriesEntries(i, j)[index] =
        log[i][nextIndex[i][j] + index - 1]
    BY <1>1, <1>2, <1>3, <1>4, SubSeqProperties
    DEF AppendEntriesEntries
<1> QED BY <1>5, <1>6

LEMMA OldMessageEntryOwnerNext ==
    \A m \in messages:
    \A index \in DOMAIN m.mentries:
        /\ InductiveInvariant
        /\ [Next]_vars
        /\ m.mtype = AppendEntriesRequest
        => \E owner \in Server:
            TermOwnerPrime(owner, m.mentries[index].term,
                           m.mprevLogIndex + index)
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                      NEW m \in messages,
                      m.mtype = AppendEntriesRequest,
                      NEW index \in DOMAIN m.mentries
             PROVE  \E owner \in Server:
                        TermOwnerPrime(owner, m.mentries[index].term,
                                      m.mprevLogIndex + index)
    OBVIOUS
<1>1. \E owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index)
    BY DEF InductiveInvariant, MessageElectionInv
<1> PICK owner \in Server:
        TermOwner(owner, m.mentries[index].term,
                  m.mprevLogIndex + index) BY <1>1
<1>2. /\ m.mentries[index].term \in Nat
       /\ m.mprevLogIndex + index \in Nat
    BY MessageFieldsTypeOK, ElementOfSeq, LenProperties
    DEF InductiveInvariant, TypeOK, MsgTypeOK, LogEntry
<1>3. TermOwner(owner, m.mentries[index].term,
                m.mprevLogIndex + index) BY SMT
<1>4. TermOwner(owner, m.mentries[index].term,
                m.mprevLogIndex + index)'
    BY <1>2, <1>3, TermOwnerNext
<1>5. TermOwnerPrime(owner, m.mentries[index].term,
                     m.mprevLogIndex + index)
    BY <1>4
    DEF TermOwnerPrime, WonPrime, StartedPrime, VoteForPrime, GrantPrime,
        TermOwner, Won, Started, VoteFor, Grant, OwnerActive, LogHasTermAt
<1> QED BY <1>5

LEMMA MessageElectionInvNext ==
    InductiveInvariant /\ [Next]_vars => MessageElectionInv'
<1> USE TermOwnerNext, AppendEntriesEntriesSource, MessageFieldsTypeOK,
        MessageTypesDistinct, LenProperties
    DEF Next, vars, InductiveInvariant, TypeOK, MsgTypeOK,
        LeaderVarsTypeOK, LogElectionInv, MessageElectionInv
<1>stutter. InductiveInvariant /\ UNCHANGED vars => MessageElectionInv'
    BY MessageElectionUnchanged 
<1>restart. \A i \in Server:
        InductiveInvariant /\ Restart(i) => MessageElectionInv'
    BY MessageElectionUnchanged DEF Restart
<1>timeout. \A i \in Server:
        InductiveInvariant /\ Timeout(i) => MessageElectionInv'
    BY MessageElectionNoNewRequests, MessageTypesDistinct
    DEF Timeout, WithMessages, RequestVoteRequests
<1>leader. \A i \in Server:
        InductiveInvariant /\ BecomeLeader(i) => MessageElectionInv'
    BY MessageElectionUnchanged DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v) => MessageElectionInv'
    BY MessageElectionUnchanged DEF ClientRequest
<1>commit. \A i \in Server:
        InductiveInvariant /\ AdvanceCommitIndex(i) => MessageElectionInv'
    BY MessageElectionUnchanged DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        InductiveInvariant /\ [Next]_vars /\ AppendEntries(i, j) =>
            MessageElectionInv'
    <2> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                         InductiveInvariant, [Next]_vars, AppendEntries(i, j),
                         NEW m \in messages',
                         m.mtype = AppendEntriesRequest,
                         NEW index \in DOMAIN m.mentries
                PROVE  \E owner \in Server:
                    TermOwnerPrime(owner, m.mentries[index].term,
                                   m.mprevLogIndex + index)
        BY Zenon DEF MessageElectionInv, TermOwnerPrime, WonPrime, StartedPrime,
            VoteForPrime, GrantPrime, TermOwner, Won, Started, VoteFor, Grant,
            OwnerActive, LogHasTermAt
    <2>old_message. CASE m \in messages
        BY <2>old_message, OldMessageEntryOwnerNext
    <2>new_message. CASE m \notin messages
        <3> USE <2>new_message
        <3>1. m = AppendEntriesMessage(i, j)
            BY DEF AppendEntries, Send, WithMessage, WithMessages
        <3>2. /\ nextIndex[i][j] + index - 1 \in DOMAIN log[i]
              /\ AppendEntriesEntries(i, j)[index] =
                    log[i][nextIndex[i][j] + index - 1]
            BY <3>1, AppendEntriesEntriesSource
            DEF AppendEntriesMessage, InductiveInvariant
        <3>3. \E owner \in Server:
                TermOwnerPrime(owner,
                    log[i][nextIndex[i][j] + index - 1].term,
                    nextIndex[i][j] + index - 1)
            BY <3>2, OldLogEntryOwnerNext
        <3>4. /\ m.mentries = AppendEntriesEntries(i, j)
              /\ m.mprevLogIndex = nextIndex[i][j] - 1
            BY <3>1 DEF AppendEntriesMessage
        <3>5. /\ index \in Nat
              /\ nextIndex[i][j] \in Nat \ {0}
            BY <3>4, AppendEntriesEntriesTypeOK, LenProperties
            DEF InductiveInvariant, TypeOK, LeaderVarsTypeOK
        <3>6. /\ m.mentries[index].term =
                    log[i][nextIndex[i][j] + index - 1].term
              /\ m.mprevLogIndex + index =
                    nextIndex[i][j] + index - 1
            BY <3>2, <3>4, <3>5
        <3> QED BY <3>3, <3>6
    <2> QED BY <2>old_message, <2>new_message
<1>step_down. \A i \in Server:
        InductiveInvariant /\ LeaderStepDown(i) => MessageElectionInv'
    BY MessageElectionUnchanged DEF LeaderStepDown
<1>receive. \A m \in messages:
        InductiveInvariant /\ Receive(m) => MessageElectionInv'
    BY MessageElectionNoNewRequests, MessageTypesDistinct, SMTT(30)
    DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>restart, <1>timeout, <1>leader, <1>client_request,
        <1>commit, <1>append_entries, <1>step_down, <1>receive,
        <1>stutter

LEMMA MatchIndexMonotonicNext ==
    /\ TypeOK
    /\ [Next]_vars
    => MatchIndexMonotonicInv
<1> USE DEF TypeOK, LeaderVarsTypeOK, MatchIndexMonotonicInv, vars
<1>stutter. TypeOK /\ UNCHANGED vars => MatchIndexMonotonicInv
    OBVIOUS
<1>restart. ASSUME
                NEW i \in Server,
                TypeOK,
                Restart(i)
            PROVE MatchIndexMonotonicInv
    <2> USE <1>restart, ServerStatesDistinct DEF Restart, ServerVarsTypeOK
    <2>restarted_node.
            /\ state'[i] = Follower
            /\ state'[i] # Leader
        OBVIOUS
    <2>others. \A j \in Server: j # i => /\ matchIndex'[j] = matchIndex[j]
                                         /\ state'[j] = state[j]
        OBVIOUS
    <2> QED BY <2>restarted_node, <2>others
<1>timeout. \A i \in Server:
        TypeOK /\ Timeout(i) => MatchIndexMonotonicInv
    BY DEF Timeout
<1>leader. \A i \in Server:
        TypeOK /\ BecomeLeader(i) => /\ state[i] = Candidate
                                     /\ MatchIndexMonotonicInv
    BY ServerStatesDistinct DEF BecomeLeader
<1>client_request. \A i \in Server, v \in Value:
        TypeOK /\ ClientRequest(i, v) => MatchIndexMonotonicInv
    BY DEF ClientRequest
<1>commit. \A i \in Server:
        TypeOK /\ AdvanceCommitIndex(i) => MatchIndexMonotonicInv
    BY DEF AdvanceCommitIndex
<1>append_entries. \A i, j \in Server:
        TypeOK /\ AppendEntries(i, j) => MatchIndexMonotonicInv
    BY DEF AppendEntries
<1>step_down. \A i \in Server:
        TypeOK /\ LeaderStepDown(i) => MatchIndexMonotonicInv
    BY DEF LeaderStepDown
<1>receive. \A m \in messages:
        TypeOK /\ Receive(m) => MatchIndexMonotonicInv
    <2>update_term. \A m \in messages:
            TypeOK /\ UpdateTerm(m.mdest, m.msource, m)
            => MatchIndexMonotonicInv
        BY DEF UpdateTerm
    <2>request_vote_request. \A m \in messages:
            /\ TypeOK
            /\ m.mtype = RequestVoteRequest
            /\ HandleRequestVoteRequest(m.mdest, m.msource, m)
            => MatchIndexMonotonicInv
        BY DEF HandleRequestVoteRequest
    <2>request_vote_response. \A m \in messages:
            /\ TypeOK
            /\ m.mtype = RequestVoteResponse
            /\ HandleRequestVoteResponse(m.mdest, m.msource, m)
            => MatchIndexMonotonicInv
        BY DEF HandleRequestVoteResponse
    <2>append_entries_request. \A m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
            => MatchIndexMonotonicInv
        BY DEF HandleAppendEntriesRequest
    <2>append_entries_response. \A m \in messages:
            /\ TypeOK
            /\ m.mtype = AppendEntriesResponse
            /\ HandleAppendEntriesResponse(m.mdest, m.msource, m)
            => MatchIndexMonotonicInv
        BY DEF HandleAppendEntriesResponse
    <2> QED BY <2>update_term, <2>request_vote_request,
        <2>request_vote_response, <2>append_entries_request,
        <2>append_entries_response
        DEF Receive, HandleMsg
<1> QED BY <1>stutter, <1>restart, <1>timeout, <1>leader,
    <1>client_request, <1>commit, <1>append_entries, <1>step_down,
    <1>receive
    DEF Next, vars

LEMMA InductiveInvariantNext ==
    InductiveInvariant /\ [Next]_vars => InductiveInvariant'
    BY TypeOKNext, SendInvariantNext, RequestIndexBoundNext,
        ResponseTermBoundNext, ResponseIndexBoundNext, NextIndexBoundNext,
        MatchIndexBelowNextIndexNext,
        AcknowledgedNextIndexInvNext,
        VoteRecordInvNext, ActiveVotesInvNext, LeaderQuorumInvNext,
        LogElectionInvNext, MessageElectionInvNext, LogTermBoundInvNext,
        MessageTermBoundInvNext, RequestCommitIndexBoundNext
    DEF InductiveInvariant

-----------------------------------------------------------------------

THEOREM InductiveInvariantInvariant == Spec => []InductiveInvariant
    BY InductiveInvariantInit, InductiveInvariantNext, PTL DEF Spec

THEOREM TypeOKInvariant == Spec => []TypeOK
    BY InductiveInvariantInvariant, PTL DEF InductiveInvariant

THEOREM MsgTypeOKInvariant == Spec => []MsgTypeOK
    BY TypeOKInvariant, PTL DEF TypeOK

THEOREM ServerVarsTypeOKInvariant == Spec => []ServerVarsTypeOK
    BY TypeOKInvariant, PTL DEF TypeOK

THEOREM CandidateVarsTypeOKInvariant == Spec => []CandidateVarsTypeOK
    BY TypeOKInvariant, PTL DEF TypeOK

THEOREM LeaderVarsTypeOKInvariant == Spec => []LeaderVarsTypeOK
    BY TypeOKInvariant, PTL DEF TypeOK

THEOREM LogVarsTypeOKInvariant == Spec => []LogVarsTypeOK
    BY TypeOKInvariant, PTL DEF TypeOK


THEOREM MatchIndexMonotonicInvariant == Spec => [][MatchIndexMonotonicInv]_vars
<1>1. Spec => [][Next]_vars /\ []TypeOK
    BY TypeOKInvariant DEF Spec
<1>2. TypeOK /\ [Next]_vars => [MatchIndexMonotonicInv]_vars
  BY MatchIndexMonotonicNext
<1> QED BY <1>1, <1>2, PTL

=========================================================================
