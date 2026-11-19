--------------------- MODULE proof_commitindex ----------------------
\* proof_commitindex.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_inductiveinvariant

CandidateCurrentTermFree ==
    \A i \in Server:
        state[i] = Candidate =>
            \A index \in DOMAIN log[i]: log[i][index].term < currentTerm[i]

OldCommitPhase(i) ==
    \A index \in DOMAIN log[i]:
        log[i][index].term = currentTerm[i] => commitIndex[i] < index

CurrentCommitPhase(i) == commitIndex[i] \in AgreeIndexes(i)

LeaderCommitPhaseInv ==
    \A i \in Server:
        state[i] = Leader => OldCommitPhase(i) \/ CurrentCommitPhase(i)

CommitPhaseInv == CandidateCurrentTermFree /\ LeaderCommitPhaseInv

CommitIndexMonotonicInv ==
    \A i \in Server:
        state[i] = Leader /\ state'[i] = Leader =>
            commitIndex[i] <= commitIndex'[i]

MonotonicCommitIndexInv ==
    \A i \in Server:
        commitIndex[i] <= commitIndex'[i] \/ Restart(i)

------------------------------------------------------------------------

LEMMA CommitPhaseInvInit == Init => CommitPhaseInv
    BY ServerStatesDistinct, SMT
    DEF Init, InitServerVars, CommitPhaseInv,
        CandidateCurrentTermFree, LeaderCommitPhaseInv

LEMMA CandidateCurrentTermFreeNext ==
    /\ TypeOK
    /\ LogTermBoundInv
    /\ CandidateCurrentTermFree
    /\ [Next]_vars
    => CandidateCurrentTermFree'
<1> USE ServerStatesDistinct
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, CandidateCurrentTermFree
<1>timeout. \A i \in Server:
        /\ TypeOK
        /\ LogTermBoundInv
        /\ CandidateCurrentTermFree
        /\ Timeout(i)
        => CandidateCurrentTermFree'
    <2> SUFFICES ASSUME NEW i \in Server, TypeOK, LogTermBoundInv,
                          CandidateCurrentTermFree, Timeout(i),
                          NEW j \in Server, state'[j] = Candidate,
                          NEW index \in DOMAIN log'[j]
                 PROVE log'[j][index].term < currentTerm'[j]
        BY SMT
    <2>timed_out. CASE j = i
        <3>bound. log[j][index].term <= currentTerm[j]
            BY <2>timed_out, SMT DEF LogTermBoundInv, Timeout
        <3>terms. /\ currentTerm'[j] = currentTerm[j] + 1
                  /\ currentTerm[j] \in Nat
                  /\ log'[j] = log[j]
            BY <2>timed_out, SMT DEF Timeout
        <3>entry. log[j][index].term \in Nat
            BY <3>terms, ElementOfSeq, SMT DEF LogEntry
        <3> QED BY <3>bound, <3>terms, <3>entry, SMT
    <2>other. CASE j # i
        BY <2>other, SMT DEF Timeout
    <2> QED BY <2>timed_out, <2>other, SMT
<1>others.
        /\ TypeOK
        /\ CandidateCurrentTermFree
        /\ \/ UNCHANGED vars
           \/ \E i \in Server: Restart(i)
           \/ \E i \in Server: BecomeLeader(i)
           \/ \E i \in Server, v \in Value: ClientRequest(i, v)
           \/ \E i \in Server: AdvanceCommitIndex(i)
           \/ \E i, j \in Server: AppendEntries(i, j)
           \/ \E i \in Server: LeaderStepDown(i)
           \/ \E m \in messages: Receive(m)
        => CandidateCurrentTermFree'
    BY MessageFieldsTypeOK, SMT
    DEF vars, Restart, BecomeLeader, ClientRequest, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse, MsgTypeOK
<1> QED BY <1>timeout, <1>others, SMT DEF Next

LEMMA GrowingAgreement ==
    \A i \in Server:
        /\ TypeOK
        /\ TypeOK'
        /\ Len(log[i]) <= Len(log'[i])
        /\ \A j \in Server: matchIndex[i][j] <= matchIndex'[i][j]
        => AgreeIndexes(i) \subseteq AgreeIndexes(i)'
<1> SUFFICES ASSUME NEW i \in Server, TypeOK, TypeOK',
                      Len(log[i]) <= Len(log'[i]),
                      \A j \in Server: matchIndex[i][j] <= matchIndex'[i][j],
                      NEW index \in AgreeIndexes(i)
             PROVE index \in AgreeIndexes(i)'
    BY SMT
<1>types. /\ Len(log[i]) \in Nat
          /\ Len(log'[i]) \in Nat
          /\ index \in Nat
          /\ \A j \in Server:
                 /\ matchIndex[i][j] \in Nat
                 /\ matchIndex'[i][j] \in Nat
    BY LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK, LeaderVarsTypeOK, AgreeIndexes
<1>1. /\ Agree(i, index) \in Quorum
       /\ index \in 1..Len(log'[i])
       /\ Agree(i, index) \subseteq Agree(i, index)'
       /\ Agree(i, index)' \subseteq Server
    <2>bounds. /\ index \in 1..Len(log[i])
               /\ Agree(i, index) \in Quorum
        BY SMT DEF AgreeIndexes
    <2>growth. /\ Agree(i, index) \subseteq Agree(i, index)'
               /\ Agree(i, index)' \subseteq Server
        BY <1>types, SMT DEF Agree
    <2> QED BY <1>types, <2>bounds, <2>growth, SMT
<1>2. Agree(i, index)' \in Quorum
    BY <1>1, QuorumSuperset, SMT
<1> QED BY <1>1, <1>2, SMT DEF AgreeIndexes

LEMMA ContinuingLeaderLog ==
    \A i \in Server:
        /\ TypeOK
        /\ [Next]_vars
        /\ state[i] = Leader
        /\ state'[i] = Leader
        => /\ currentTerm'[i] = currentTerm[i]
           /\ \/ log'[i] = log[i]
              \/ \E v \in Value:
                     log'[i] = Append(log[i], [term |-> currentTerm[i], value |-> v])
    BY MessageFieldsTypeOK, ServerStatesDistinct, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, MsgTypeOK, Next, vars,
        Restart, Timeout, BecomeLeader, ClientRequest, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesRequest, HandleAppendEntriesResponse

LEMMA ContinuingLeaderAgreement ==
    \A i \in Server:
        /\ TypeOK
        /\ TypeOK'
        /\ [Next]_vars
        /\ state[i] = Leader
        /\ state'[i] = Leader
        => AgreeIndexes(i) \subseteq AgreeIndexes(i)'
<1> SUFFICES ASSUME NEW i \in Server, TypeOK, TypeOK', [Next]_vars,
                      state[i] = Leader, state'[i] = Leader
             PROVE AgreeIndexes(i) \subseteq AgreeIndexes(i)'
    OBVIOUS
<1>log. Len(log[i]) <= Len(log'[i])
    BY ContinuingLeaderLog, AppendProperties, LenProperties, SMT
    DEF TypeOK, LogVarsTypeOK
<1>match. \A j \in Server: matchIndex[i][j] <= matchIndex'[i][j]
    BY MatchIndexMonotonicNext, SMT DEF MatchIndexMonotonicInv
<1> QED BY <1>log, <1>match, GrowingAgreement, SMT

LEMMA LeaderNewCommitIndexBound ==
    \A i \in Server:
        /\ TypeOK
        /\ OldCommitPhase(i) \/ CurrentCommitPhase(i)
        => commitIndex[i] <= NewCommitIndex(i)
<1> SUFFICES ASSUME NEW i \in Server, TypeOK,
                      OldCommitPhase(i) \/ CurrentCommitPhase(i)
             PROVE commitIndex[i] <= NewCommitIndex(i)
    OBVIOUS
<1>unchanged. CASE NewCommitIndex(i) = commitIndex[i]
    BY <1>unchanged, SMT DEF TypeOK, LogVarsTypeOK
<1>changed. CASE NewCommitIndex(i) # commitIndex[i]
    <2>max. /\ AgreeIndexes(i) # {}
             /\ NewCommitIndex(i) = Max(AgreeIndexes(i))
             /\ Max(AgreeIndexes(i)) \in AgreeIndexes(i)
             /\ log[i][Max(AgreeIndexes(i))].term = currentTerm[i]
        BY <1>changed, MaxAgreeIndexesTypeOK, SMT DEF NewCommitIndex
    <2>types. /\ log[i] \in Seq(LogEntry)
               /\ commitIndex[i] \in Nat
               /\ Max(AgreeIndexes(i)) \in Nat
        BY <2>max, MaxAgreeIndexesTypeOK, SMT DEF TypeOK, LogVarsTypeOK
    <2>old. OldCommitPhase(i) => commitIndex[i] < Max(AgreeIndexes(i))
        BY <2>max, <2>types, LenProperties, SMT DEF OldCommitPhase, AgreeIndexes
    <2>current. CurrentCommitPhase(i) => commitIndex[i] <= Max(AgreeIndexes(i))
        BY <2>max, BoundedNatSetHasMaximum, AgreeIndexesTypeOK, SMT
        DEF CurrentCommitPhase, Max
    <2> QED BY <2>max, <2>old, <2>current, SMT
<1> QED BY <1>unchanged, <1>changed, SMT

LEMMA LeaderCommitPhaseNext ==
    /\ TypeOK
    /\ TypeOK'
    /\ CommitIndexBound
    /\ CommitPhaseInv
    /\ [Next]_vars
    => LeaderCommitPhaseInv'
<1> SUFFICES ASSUME TypeOK, TypeOK', CommitIndexBound, CommitPhaseInv,
                      [Next]_vars, NEW i \in Server, state'[i] = Leader
             PROVE OldCommitPhase(i)' \/ CurrentCommitPhase(i)'
    BY SMT DEF LeaderCommitPhaseInv
<1>new_leader. CASE state[i] # Leader
    <2>election. /\ state[i] = Candidate
                  /\ log'[i] = log[i]
                  /\ currentTerm'[i] = currentTerm[i]
        BY <1>new_leader, MessageFieldsTypeOK, ServerStatesDistinct, SMT
        DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, MsgTypeOK,
            Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
            AdvanceCommitIndex, AppendEntries, LeaderStepDown, Receive,
            UpdateTerm, HandleMsg, HandleRequestVoteRequest,
            HandleRequestVoteResponse, HandleAppendEntriesRequest,
            HandleAppendEntriesResponse
    <2> QED BY <2>election, SMT
        DEF CommitPhaseInv, CandidateCurrentTermFree, OldCommitPhase
<1>continuing. CASE state[i] = Leader
    <2>agreement. AgreeIndexes(i) \subseteq AgreeIndexes(i)'
        BY <1>continuing, ContinuingLeaderAgreement
    <2>commit. \/ commitIndex'[i] = commitIndex[i]
               \/ /\ AgreeIndexes(i) # {}
                  /\ commitIndex'[i] = Max(AgreeIndexes(i))
        BY <1>continuing, MessageFieldsTypeOK, ServerStatesDistinct, SMT
        DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, MsgTypeOK,
            Next, vars, Restart, Timeout, BecomeLeader, ClientRequest,
            AdvanceCommitIndex, NewCommitIndex, AppendEntries,
            LeaderStepDown, Receive, UpdateTerm, HandleMsg,
            HandleRequestVoteRequest, HandleRequestVoteResponse,
            HandleAppendEntriesRequest, HandleAppendEntriesResponse
    <2>changed. CASE commitIndex'[i] # commitIndex[i]
        BY <2>commit, <2>agreement, <2>changed, MaxAgreeIndexesTypeOK, SMT
        DEF CurrentCommitPhase
    <2>unchanged. CASE commitIndex'[i] = commitIndex[i]
        <3>old. OldCommitPhase(i) => OldCommitPhase(i)'
            BY <1>continuing, <2>unchanged, ContinuingLeaderLog,
                AppendProperties, LenProperties, SMT
            DEF OldCommitPhase, CommitIndexBound, TypeOK, LogVarsTypeOK
        <3>current. CurrentCommitPhase(i) => CurrentCommitPhase(i)'
            BY <2>unchanged, <2>agreement, SMT DEF CurrentCommitPhase
        <3> QED BY <3>old, <3>current, <1>continuing, SMT
            DEF CommitPhaseInv, LeaderCommitPhaseInv
    <2> QED BY <2>changed, <2>unchanged, SMT
<1> QED BY <1>new_leader, <1>continuing, SMT

LEMMA CommitPhaseInvNext ==
    /\ InductiveInvariant
    /\ CommitIndexBound
    /\ CommitPhaseInv
    /\ [Next]_vars
    => CommitPhaseInv'
    BY CandidateCurrentTermFreeNext, LeaderCommitPhaseNext, TypeOKNext, SMT
    DEF InductiveInvariant, CommitPhaseInv


LEMMA MonotonicCommitIndexNext ==
    /\ TypeOK
    /\ LeaderCommitPhaseInv
    /\ [Next]_vars
    => MonotonicCommitIndexInv
<1>restart. \A i \in Server:
        /\ TypeOK
        /\ Restart(i)
        => MonotonicCommitIndexInv
    BY SMT DEF TypeOK, LogVarsTypeOK, Restart, MonotonicCommitIndexInv
<1>advance. \A i \in Server:
        /\ TypeOK
        /\ LeaderCommitPhaseInv
        /\ AdvanceCommitIndex(i)
        => MonotonicCommitIndexInv
    BY LeaderNewCommitIndexBound, SMT
    DEF TypeOK, LogVarsTypeOK, LeaderCommitPhaseInv,
        AdvanceCommitIndex, MonotonicCommitIndexInv
<1>receive. \A m \in messages:
        /\ TypeOK
        /\ Receive(m)
        => MonotonicCommitIndexInv
    BY MessageFieldsTypeOK, SMT
    DEF TypeOK, ServerVarsTypeOK, LogVarsTypeOK, MsgTypeOK,
        Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
        HandleRequestVoteResponse, HandleAppendEntriesRequest,
        HandleAppendEntriesResponse, MonotonicCommitIndexInv
<1>others.
        /\ TypeOK
        /\ \/ UNCHANGED vars
           \/ \E i \in Server: Timeout(i)
           \/ \E i \in Server: BecomeLeader(i)
           \/ \E i \in Server, v \in Value: ClientRequest(i, v)
           \/ \E i, j \in Server: AppendEntries(i, j)
           \/ \E i \in Server: LeaderStepDown(i)
        => MonotonicCommitIndexInv
    BY SMT
    DEF TypeOK, LogVarsTypeOK, vars, Timeout, BecomeLeader,
        ClientRequest, AppendEntries, LeaderStepDown, MonotonicCommitIndexInv
<1> QED BY <1>restart, <1>advance, <1>receive, <1>others, SMT DEF Next

LEMMA CommitIndexMonotonicNext ==
    /\ TypeOK
    /\ LeaderCommitPhaseInv
    /\ [Next]_vars
    => CommitIndexMonotonicInv
    BY MonotonicCommitIndexNext, ServerStatesDistinct, SMT
    DEF CommitIndexMonotonicInv, MonotonicCommitIndexInv,
        Restart, TypeOK, ServerVarsTypeOK

------------------------------------------------------------------------

THEOREM CandidateCurrentTermFreeInvariant == Spec => []CandidateCurrentTermFree
<1>init. Init => CandidateCurrentTermFree
    BY CommitPhaseInvInit DEF CommitPhaseInv
<1>next. InductiveInvariant /\ CandidateCurrentTermFree /\ [Next]_vars
         => CandidateCurrentTermFree'
    BY CandidateCurrentTermFreeNext DEF InductiveInvariant
<1> QED BY <1>init, <1>next, InductiveInvariantInvariant, PTL DEF Spec


=====================================================================
