------------------------------ MODULE raft -------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* raft.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.
\*
\* This derivative work incorporates material from the following sources, which remain governed by their respective original licenses:
\*
\* 1. raft.tla (https://github.com/ongardie/raft.tla)
\* Copyright 2014 Diego Ongaro.
\* Licensed under the Creative Commons Attribution-4.0 International License (https://creativecommons.org/licenses/by/4.0/).
\* Modifications: Significantly rewritten and adapted to work with dqlite while preserving the core algorithmic logic.
\*
\* 2. etcdraft.tla (https://github.com/etcd-io/raft)
\* Copyright 2024 The etcd Authors.
\* Licensed under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0).
\* Modifications: Incorporated system invariants from the original specification and subsequently modified them for dqlite.

EXTENDS Naturals, FiniteSets, Sequences, SequenceTheorems, TLC, TLAPS,
        FiniteSetTheorems

\* The set of server IDs
CONSTANTS Server
ASSUME ServerOK == IsFiniteSet(Server) /\ Server # {}

\* A reserved value.
CONSTANTS Nil
ASSUME NilNotServer == Nil \notin Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader
ASSUME ServerStatesDistinct ==
  /\ Follower # Candidate
  /\ Follower # Leader
  /\ Candidate # Leader

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse
ASSUME MessageTypesDistinct ==
  /\ RequestVoteRequest # RequestVoteResponse
  /\ RequestVoteRequest # AppendEntriesRequest
  /\ RequestVoteRequest # AppendEntriesResponse
  /\ RequestVoteResponse # AppendEntriesRequest
  /\ RequestVoteResponse # AppendEntriesResponse
  /\ AppendEntriesRequest # AppendEntriesResponse

----
\* Global variables

\* A set of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, currentTerm, state, votedFor, votesResponded, votesGranted, nextIndex, matchIndex, log, commitIndex>>
----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for sending many messages at once.
WithMessages(msgs, newMsgs) == msgs \cup newMsgs

\* Given a message m and set of messages, add m to the set.
WithMessage(m, msgs) == WithMessages(msgs, {m})

\* Add a message to the set of messages.
Send(m) ==
    /\ messages' = WithMessage(m, messages)

\* Local definitions of Min/Max (see SequencesExt).
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Local definition of IsPrefix (see SequencesExt).
IsPrefix(prefix, fullLog) ==
    /\ Len(prefix) <= Len(fullLog)
    /\ prefix = SubSeq(fullLog, 1, Len(prefix))

----
\* Define initial values for all variables

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = {}
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log>>

RequestVoteRequests(i, requestTerm) ==
    { [mtype |-> RequestVoteRequest,
       mterm |-> requestTerm,
       mlastLogTerm |-> LastTerm(log[i]),
       mlastLogIndex |-> Len(log[i]),
       msource |-> i,
       mdest |-> j] : j \in Server \ { i } }

\* Server i times out and starts a new election, sending a request vote
\* to all its peers.
Timeout(i) ==
    /\ state[i] \in { Follower, Candidate }
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    \* Vote for self atomically when starting an election.
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = { i }]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = { i }]
    /\ messages' = WithMessages(
        messages, RequestVoteRequests(i, currentTerm[i] + 1))
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.

AppendEntriesPrevLogTerm(i, j) ==
    LET prevLogIndex == nextIndex[i][j] - 1
    IN IF prevLogIndex > 0 THEN
           log[i][prevLogIndex].term
       ELSE
           0

AppendEntriesLastEntry(i, j) == Min({Len(log[i]), nextIndex[i][j]})

AppendEntriesEntries(i, j) ==
    SubSeq(log[i], nextIndex[i][j], AppendEntriesLastEntry(i, j))

AppendEntriesMessage(i, j) ==
    [mtype          |-> AppendEntriesRequest,
     mterm          |-> currentTerm[i],
     mprevLogIndex  |-> nextIndex[i][j] - 1,
     mprevLogTerm   |-> AppendEntriesPrevLogTerm(i, j),
     mentries       |-> AppendEntriesEntries(i, j),
     mcommitIndex   |-> Min({commitIndex[i], AppendEntriesLastEntry(i, j)}),
     msource        |-> i,
     mdest          |-> j]

AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Send(AppendEntriesMessage(i, j))
    /\ UNCHANGED (* serverVars *) <<currentTerm, state, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, currentTerm, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, commitIndex>>
    /\ UNCHANGED (* serverVars *) <<currentTerm, state, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
Agree(i, index) == { i } \cup {k \in Server: matchIndex[i][k] >= index}

AgreeIndexes(i) ==
    {index \in 1 .. Len(log[i]): Agree(i, index) \in Quorum}

NewCommitIndex(i) ==
  IF /\ AgreeIndexes(i) /= {}
     /\ log[i][Max(AgreeIndexes(i))].term = currentTerm[i]
  THEN Max(AgreeIndexes(i))
  ELSE commitIndex[i]

AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ commitIndex' = [commitIndex EXCEPT ![i] = NewCommitIndex(i)]
    /\ UNCHANGED <<messages, log>>
    /\ UNCHANGED (* serverVars *) <<currentTerm, state, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>

\* From dissertation, section 6.2:
\*     > Thus, a leader in Raft steps down if an election timeout elapses
\*       without a successful round of heartbeats to a majority of its cluster;
\*       this allows clients to retry their requests with another server.
LeaderStepDown(i) ==
    /\ state[i] = Leader
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<messages, currentTerm, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    \* TODO: it would be nice to reset `leaderVars` (`nextIndex` and `matchIndex`)
    \* when losing leadership as that would collapse lots of equal states in 
    \* the state space.
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Send([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 msource      |-> i,
                 mdest        |-> j])
       /\ UNCHANGED <<state, currentTerm>>
       /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
       /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
       /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ UNCHANGED messages
    /\ UNCHANGED (* serverVars *) <<currentTerm, state, votedFor>>
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
          \* Update state to Follower if necessary.
       /\ IF m.mterm = currentTerm[i] /\ state[i] = Candidate
          THEN state' = [state EXCEPT ![i] = Follower]
          ELSE UNCHANGED state
       /\ IF \/ m.mterm < currentTerm[i]
             \/ /\ state[i] # Leader
                /\ ~logOk
          \* reject request
          THEN /\ Send([ mtype           |-> AppendEntriesResponse,
                         mterm           |-> currentTerm[i],
                         msuccess        |-> FALSE,
                         mmatchIndex     |-> 0,
                         msource         |-> i,
                         mdest           |-> j])
               /\ UNCHANGED (* logVars *) <<log, commitIndex>>
          \* accept request
          ELSE /\ state[i] # Leader
               \* Delayed or duplicated requests must not undo known commits.
               /\ IF m.mcommitIndex > commitIndex[i]
                  THEN commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                  ELSE UNCHANGED commitIndex
               /\ IF /\ m.mentries /= << >>
                     /\ \/ Len(log[i]) = m.mprevLogIndex
                        \/ log[i][m.mprevLogIndex + 1].term /= m.mentries[1].term
                  THEN log' = [log EXCEPT ![i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])]
                  ELSE UNCHANGED log
               /\ Send([mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        msuccess        |-> TRUE,
                        mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                        msource         |-> i,
                        mdest           |-> j])
       /\ UNCHANGED <<currentTerm, votedFor>>
       /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
       /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Leader
    /\ IF m.msuccess
       THEN IF m.mmatchIndex > matchIndex[i][j]
            THEN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
            ELSE UNCHANGED <<nextIndex, matchIndex>>
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                                Max({nextIndex[i][j] - 1, matchIndex[i][j] + 1})]
            /\ UNCHANGED matchIndex
    /\ UNCHANGED messages
    /\ UNCHANGED (* serverVars *) <<currentTerm, state, votedFor>>
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
    \* messages is unchanged so m can be processed further.
    /\ UNCHANGED messages
    /\ UNCHANGED (* candidateVars *) <<votesResponded, votesGranted>>
    /\ UNCHANGED (* leaderVars *) <<nextIndex, matchIndex>>
    /\ UNCHANGED (* logVars *) <<log, commitIndex>>

HandleMsg(i, j, m) ==
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ HandleAppendEntriesResponse(i, j, m)

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ HandleMsg(i, j, m)

\* End of message handlers.
----
\* Defines how the variables may transition.
Next ==
  \/ \E i \in Server : Restart(i)
  \/ \E i \in Server : Timeout(i)
  \/ \E i \in Server : BecomeLeader(i)
  \/ \E i \in Server, v \in Value : ClientRequest(i, v)
  \/ \E i \in Server : AdvanceCommitIndex(i)
  \/ \E i,j \in Server : AppendEntries(i, j)
  \/ \E i \in Server : LeaderStepDown(i)
  \/ \E m \in messages : Receive(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* Correctness invariants.

\* Exact record types for log entries and in-flight messages.
LogEntry ==
    [term : Nat, value : Value]

RequestVoteRequestMessage ==
    [mtype         : {RequestVoteRequest},
     mterm         : Nat,
     mlastLogTerm  : Nat,
     mlastLogIndex : Nat,
     msource       : Server,
     mdest         : Server]

RequestVoteResponseMessage ==
    [mtype        : {RequestVoteResponse},
     mterm        : Nat,
     mvoteGranted : BOOLEAN,
     msource      : Server,
     mdest        : Server]

AppendEntriesRequestMessage ==
    [mtype         : {AppendEntriesRequest},
     mterm         : Nat,
     mprevLogIndex : Nat,
     mprevLogTerm  : Nat,
     mentries      : Seq(LogEntry),
     mcommitIndex  : Nat,
     msource       : Server,
     mdest         : Server]

AppendEntriesResponseMessage ==
    [mtype       : {AppendEntriesResponse},
     mterm       : Nat,
     msuccess    : BOOLEAN,
     mmatchIndex : Nat,
     msource     : Server,
     mdest       : Server]

Message ==
    UNION {RequestVoteRequestMessage, RequestVoteResponseMessage,
           AppendEntriesRequestMessage, AppendEntriesResponseMessage}


MsgTypeOK == messages \subseteq Message

ServerVarsTypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ state \in [Server -> {Follower, Candidate, Leader}]
    /\ votedFor \in [Server -> Server \cup {Nil}]

CandidateVarsTypeOK ==
    /\ votesResponded \in [Server -> SUBSET Server]
    /\ votesGranted \in [Server -> SUBSET Server]

LeaderVarsTypeOK ==
    /\ nextIndex \in [Server -> [Server -> Nat \ {0}]]
    /\ matchIndex \in [Server -> [Server -> Nat]]

LogVarsTypeOK ==
    /\ log \in [Server -> Seq(LogEntry)]
    /\ commitIndex \in [Server -> Nat]


\* Every variable holds a value of its declared type. Numeric fields are Nat
\* since all terms and indices are non-negative; votedFor may also be Nil,
\* which is distinct from every Server at runtime.
TypeOK ==
    /\ MsgTypeOK
    /\ ServerVarsTypeOK
    /\ CandidateVarsTypeOK
    /\ LeaderVarsTypeOK
    /\ LogVarsTypeOK

SendInvariant ==
    \A m \in messages: m.mterm <= currentTerm[m.msource] /\ m.msource # m.mdest

\* Helper functions:
\* The prefix of the log of server i that has been committed.
Committed(i) == SubSeq(log[i],1,commitIndex[i])
MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)
CurrentLeaders == {i \in Server : state[i] = Leader}

\* Committed log entries should never conflict between servers.
\* See https://github.com/etcd-io/raft/blob/195edd62dbd6d9c9c2d11342b0476ecd64e7ca6f/tla/etcdraft.tla#L781.
LogInv ==
    \A i, j \in Server :
        \/ IsPrefix(Committed(i),Committed(j))
        \/ IsPrefix(Committed(j),Committed(i))

\* There should not be more than one leader per term at the same time.
\* Note that this does not rule out multiple leaders in the same term at
\* different times.
\* See https://github.com/etcd-io/raft/blob/195edd62dbd6d9c9c2d11342b0476ecd64e7ca6f/tla/etcdraft.tla#L792.
MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* A leader always has the greatest index for its current term.
\* See https://github.com/etcd-io/raft/blob/195edd62dbd6d9c9c2d11342b0476ecd64e7ca6f/tla/etcdraft.tla#L800.
ElectionSafetyInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})

\* Every (index, term) pair determines a log prefix.
\* See https://github.com/etcd-io/raft/blob/195edd62dbd6d9c9c2d11342b0476ecd64e7ca6f/tla/etcdraft.tla#L808.
LogMatchingInv ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* All committed entries are contained in the log of at least one server in
\* every quorum.
\* See https://github.com/etcd-io/raft/blob/195edd62dbd6d9c9c2d11342b0476ecd64e7ca6f/tla/etcdraft.tla#L838.
QuorumLogInv ==
    \A i \in Server:
    \A S \in Quorum:
        \E j \in S :
            IsPrefix(Committed(i), log[j])

\* Leaders at or above a server's current term contain its committed prefix.
\* Older entries may have become committed only in a later term.
LeaderCompletenessInv ==
    \A server \in Server: \A leader \in CurrentLeaders:
        currentTerm[server] <= currentTerm[leader] =>
            IsPrefix(Committed(server), log[leader])

===============================================================================
