------------------ MODULE proof_log_matching_inv --------------------
\* proof_log_matching_inv.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_electionsafety
LOCAL INSTANCE NaturalsInduction

\* Independent log matching over the original Raft transitions.
\* Historical entry edges use existing messages; no additional state.

AppendRequests == {m \in messages: m.mtype = AppendEntriesRequest}

LogEntryEdge(entries, index) ==
    [index |-> index, term |-> entries[index].term,
     previous |-> IF index = 1 THEN 0 ELSE entries[index - 1].term,
     entry |-> entries[index]]

RequestEntryEdge(request, offset) ==
    [index |-> request.mprevLogIndex + offset,
     term |-> request.mentries[offset].term,
     previous |-> IF offset = 1 THEN request.mprevLogTerm
                  ELSE request.mentries[offset - 1].term,
     entry |-> request.mentries[offset]]

HistoricalEntryEdges ==
    (UNION { {LogEntryEdge(log[server], index): index \in DOMAIN log[server]}:
              server \in Server })
    \cup (UNION { {RequestEntryEdge(request, offset): offset \in DOMAIN request.mentries}:
                  request \in AppendRequests })

EntryEdgeConsistency ==
    \A left, right \in HistoricalEntryEdges:
        left.index = right.index /\ left.term = right.term
        => /\ left.entry = right.entry /\ left.previous = right.previous

AppendRequestRootTerm ==
    \A m \in AppendRequests: m.mprevLogIndex = 0 => m.mprevLogTerm = 0

-----------------------------------------------------------------------------

LEMMA NewAppendRequestOrigin ==
    InductiveInvariant /\ [Next]_vars =>
        \A m \in messages' \ messages:
            m.mtype = AppendEntriesRequest =>
                \E i, j \in Server:
                    /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    NEW m \in messages' \ messages,
                    m.mtype = AppendEntriesRequest
             PROVE \E i, j \in Server:
                 /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
    OBVIOUS
<1>1. CASE \E i, j \in Server: AppendEntries(i, j)
    BY <1>1 DEF AppendEntries, Send, WithMessage, WithMessages
<1>2. CASE \E i \in Server: Timeout(i)
    BY <1>2, MessageTypesDistinct DEF Timeout, RequestVoteRequests, WithMessages
<1>3. CASE \E request \in messages: Receive(request)
    BY <1>3, MessageTypesDistinct
       DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
           HandleRequestVoteResponse, HandleAppendEntriesRequest,
           HandleAppendEntriesResponse, Send, WithMessage, WithMessages
<1> QED BY <1>1, <1>2, <1>3
    DEF Next, vars, Restart, BecomeLeader, ClientRequest,
        AdvanceCommitIndex, LeaderStepDown

LEMMA AppendRequestFirstEntrySnapshot ==
    \A sender, recipient \in Server:
        /\ TypeOK /\ AppendEntriesEntries(sender, recipient) # << >>
        => /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
           /\ AppendEntriesEntries(sender, recipient)[1] = log[sender][nextIndex[sender][recipient]]
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    TypeOK, AppendEntriesEntries(sender, recipient) # << >>
             PROVE /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
                   /\ AppendEntriesEntries(sender, recipient)[1]
                        = log[sender][nextIndex[sender][recipient]]
    OBVIOUS
<1>1. nextIndex[sender][recipient] \in Nat \ {0} /\
       log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) <= Len(log[sender])
    BY AppendEntriesLastEntryTypeOK, LenProperties
       DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>2. \A index \in nextIndex[sender][recipient]..AppendEntriesLastEntry(sender, recipient):
        log[sender][index] \in LogEntry
    BY <1>1, ElementOfSeq
<1>3. Len(AppendEntriesEntries(sender, recipient)) =
        IF nextIndex[sender][recipient] <= AppendEntriesLastEntry(sender, recipient)
        THEN AppendEntriesLastEntry(sender, recipient) - nextIndex[sender][recipient] + 1
        ELSE 0
    BY <1>1, <1>2, SubSeqProperties DEF AppendEntriesEntries
<1>4. AppendEntriesEntries(sender, recipient) \in Seq(LogEntry) /\
       Len(AppendEntriesEntries(sender, recipient)) \in Nat \ {0}
    BY AppendEntriesEntriesTypeOK, EmptySeq
<1>5. nextIndex[sender][recipient] \in DOMAIN log[sender]
    BY <1>1, <1>3, <1>4, LenProperties
<1>6. AppendEntriesEntries(sender, recipient)[1] = log[sender][nextIndex[sender][recipient]]
    BY <1>1, <1>2, <1>3, <1>4, SubSeqProperties DEF AppendEntriesEntries
<1> QED BY <1>5, <1>6

LEMMA EqualLogPrefixesEntryEqual ==
    \A left, right \in Seq(LogEntry), endpoint, index \in Nat:
        /\ endpoint <= Len(left) /\ endpoint <= Len(right)
        /\ index \in 1..endpoint
        /\ SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
        => left[index] = right[index]
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    NEW endpoint \in Nat, NEW index \in Nat,
                    endpoint <= Len(left), endpoint <= Len(right),
                    index \in 1..endpoint,
                    SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
             PROVE left[index] = right[index]
    OBVIOUS
<1>1. Len(left) \in Nat /\ Len(right) \in Nat
    BY LenProperties
<1>2. SubSeq(left, 1, endpoint)[index] = left[index]
    BY <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>3. SubSeq(right, 1, endpoint)[index] = right[index]
    BY <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1> QED BY <1>2, <1>3

LEMMA AppendRetainsLogPrefix ==
    \A entries \in Seq(LogEntry), entry \in LogEntry: \A endpoint \in 1..Len(entries):
        SubSeq(Append(entries, entry), 1, endpoint) = SubSeq(entries, 1, endpoint)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW endpoint \in 1..Len(entries)
             PROVE SubSeq(Append(entries, entry), 1, endpoint) = SubSeq(entries, 1, endpoint)
    OBVIOUS
<1>1. <<entry>> \in Seq(LogEntry)
    OBVIOUS
<1> QED BY <1>1, AppendIsConcat, SubSeqOfConcat1

LEMMA TruncateAppendRetainsPrefix ==
    \A entries \in Seq(LogEntry), entry \in LogEntry, cut \in Nat:
        \A endpoint \in 1..cut:
            cut <= Len(entries)
            => /\ Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
               /\ SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
                    = SubSeq(entries, 1, endpoint)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW cut \in Nat, NEW endpoint \in 1..cut, cut <= Len(entries)
             PROVE /\ Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
                   /\ SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
                        = SubSeq(entries, 1, endpoint)
    OBVIOUS
<1>1. Len(entries) \in Nat /\ cut \in 1..Len(entries)
    BY LenProperties
<1>2. SubSeq(entries, 1, cut) \in Seq(LogEntry) /\ Len(SubSeq(entries, 1, cut)) = cut
    BY <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>3. SubSeq(entries, 1, cut)[endpoint] = entries[endpoint]
    BY <1>1, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>4. Append(SubSeq(entries, 1, cut), entry)[endpoint] = entries[endpoint]
    BY <1>2, <1>3, AppendProperties
<1>5. SubSeq(Append(SubSeq(entries, 1, cut), entry), 1, endpoint)
         = SubSeq(SubSeq(entries, 1, cut), 1, endpoint)
    BY <1>2, AppendRetainsLogPrefix
<1>6. SubSeq(SubSeq(entries, 1, cut), 1, endpoint) = SubSeq(entries, 1, endpoint)
    BY <1>1, <1>2, SubSeqOfSubSeq
<1> QED BY <1>4, <1>5, <1>6

LEMMA AppendRequestRetainsMatchedPrefix ==
    \A recipient, sender \in Server, m \in messages:
        \A endpoint \in 1..m.mprevLogIndex:
            /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
            /\ HandleAppendEntriesRequest(recipient, sender, m)
            /\ m.mprevLogIndex <= Len(log[recipient])
            => /\ log'[recipient][endpoint] = log[recipient][endpoint]
               /\ SubSeq(log'[recipient], 1, endpoint)
                    = SubSeq(log[recipient], 1, endpoint)
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, NEW endpoint \in 1..m.mprevLogIndex,
                    InductiveInvariant, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m),
                    m.mprevLogIndex <= Len(log[recipient])
             PROVE /\ log'[recipient][endpoint] = log[recipient][endpoint]
                   /\ SubSeq(log'[recipient], 1, endpoint) = SubSeq(log[recipient], 1, endpoint)
    OBVIOUS
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry)
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, LogVarsTypeOK, MsgTypeOK
<1>2. CASE log' = log
    BY <1>2
<1>3. CASE log' # log
    <2>1. m.mentries # << >> /\
           log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
        BY <1>1, <1>3 DEF HandleAppendEntriesRequest
    <2>2. m.mentries[1] \in LogEntry
        BY <1>1, <2>1, LenProperties, EmptySeq, ElementOfSeq
    <2> QED BY <1>1, <2>1, <2>2, TruncateAppendRetainsPrefix
<1> QED BY <1>2, <1>3

LEMMA AppendRequestChangedLogShape ==
    \A recipient, sender \in Server, m \in messages:
        /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, m) /\ log' # log
        => /\ m.mprevLogIndex \in 0..Len(log[recipient])
           /\ m.mentries # << >> /\ m.mentries[1] \in LogEntry
           /\ Len(log'[recipient]) = m.mprevLogIndex + 1
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, InductiveInvariant,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m), log' # log
             PROVE /\ m.mprevLogIndex \in 0..Len(log[recipient])
                   /\ m.mentries # << >> /\ m.mentries[1] \in LogEntry
                   /\ Len(log'[recipient]) = m.mprevLogIndex + 1
    OBVIOUS
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry) /\ currentTerm \in [Server -> Nat]
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, LogVarsTypeOK,
                               ServerVarsTypeOK, MsgTypeOK
<1>2. m.mprevLogIndex \in 0..Len(log[recipient]) /\ m.mentries # << >> /\
       log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
    BY <1>1 DEF HandleAppendEntriesRequest
<1>3. m.mentries[1] \in LogEntry
    BY <1>1, <1>2, EmptySeq, ElementOfSeq
<1>4. SubSeq(log[recipient], 1, m.mprevLogIndex) \in Seq(LogEntry) /\
       Len(SubSeq(log[recipient], 1, m.mprevLogIndex)) = m.mprevLogIndex
    BY <1>1, <1>2, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1>5. Len(log'[recipient]) = m.mprevLogIndex + 1
    BY <1>2, <1>3, <1>4, AppendProperties
<1> QED BY <1>2, <1>3, <1>5

LEMMA AppendRequestCopiesEndpointEntry ==
    \A recipient, sender \in Server, m \in messages:
        /\ InductiveInvariant /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, m) /\ log' # log
        => log'[recipient][m.mprevLogIndex + 1] = m.mentries[1]
<1> SUFFICES ASSUME NEW recipient \in Server, NEW sender \in Server,
                    NEW m \in messages, InductiveInvariant,
                    m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(recipient, sender, m), log' # log
             PROVE log'[recipient][m.mprevLogIndex + 1] = m.mentries[1]
    OBVIOUS
<1>1. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, LogVarsTypeOK, MsgTypeOK
<1>2. m.mprevLogIndex \in 0..Len(log[recipient]) /\ m.mentries[1] \in LogEntry
    BY AppendRequestChangedLogShape
<1>3. log'[recipient] = Append(SubSeq(log[recipient], 1, m.mprevLogIndex), m.mentries[1])
    BY <1>1 DEF HandleAppendEntriesRequest
<1>4. SubSeq(log[recipient], 1, m.mprevLogIndex) \in Seq(LogEntry) /\
       Len(SubSeq(log[recipient], 1, m.mprevLogIndex)) = m.mprevLogIndex
    BY <1>1, <1>2, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
<1> QED BY <1>2, <1>3, <1>4, AppendProperties


LEMMA ConsistentLogEdgesPrefixEqual ==
    \A left, right \in Seq(LogEntry):
        /\ \A index \in (DOMAIN left) \cap (DOMAIN right):
            left[index].term = right[index].term =>
                /\ left[index] = right[index]
                /\ index > 1 => left[index - 1].term = right[index - 1].term
        => \A endpoint \in (DOMAIN left) \cap (DOMAIN right):
            left[endpoint].term = right[endpoint].term =>
                SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
<1> SUFFICES ASSUME NEW left \in Seq(LogEntry), NEW right \in Seq(LogEntry),
                    \A index \in (DOMAIN left) \cap (DOMAIN right):
                        left[index].term = right[index].term =>
                            /\ left[index] = right[index]
                            /\ index > 1 => left[index - 1].term = right[index - 1].term
             PROVE \A endpoint \in (DOMAIN left) \cap (DOMAIN right):
                        left[endpoint].term = right[endpoint].term =>
                            SubSeq(left, 1, endpoint) = SubSeq(right, 1, endpoint)
    OBVIOUS
<1> DEFINE P(n) == n \in (DOMAIN left) \cap (DOMAIN right) /\ left[n].term = right[n].term
                   => SubSeq(left, 1, n) = SubSeq(right, 1, n)
<1>0. Len(left) \in Nat /\ Len(right) \in Nat /\
       DOMAIN left = 1..Len(left) /\ DOMAIN right = 1..Len(right)
    BY LenProperties
<1>1. P(0)
    BY <1>0 DEF P
<1>2. \A n \in Nat: P(n) => P(n + 1)
    <2> SUFFICES ASSUME NEW n \in Nat, P(n),
                        n + 1 \in (DOMAIN left) \cap (DOMAIN right),
                        left[n + 1].term = right[n + 1].term
                 PROVE SubSeq(left, 1, n + 1) = SubSeq(right, 1, n + 1)
        BY DEF P
    <2>1. left[n + 1] = right[n + 1]
        OBVIOUS
    <2>2. SubSeq(left, 1, n) = SubSeq(right, 1, n)
        <3>1. CASE n = 0
            BY <1>0, <3>1, SubSeqProperties, EmptySeq
        <3>2. CASE n > 0
            BY <1>0, <3>2 DEF P
        <3> QED BY <3>1, <3>2
    <2>3. \A index \in 1..(n + 1): left[index] = right[index]
        <3> SUFFICES ASSUME NEW index \in 1..(n + 1)
                     PROVE left[index] = right[index]
            OBVIOUS
        <3>1. CASE index = n + 1
            BY <2>1, <3>1
        <3>2. CASE index # n + 1
            <4>1. index \in Nat /\ index \in 1..n /\ n <= Len(left) /\ n <= Len(right)
                BY <1>0, <3>2
            <4> QED BY <2>2, <4>1, EqualLogPrefixesEntryEqual
        <3> QED BY <3>1, <3>2
    <2>4. SubSeq(left, 1, n + 1) \in Seq(LogEntry) /\
           SubSeq(right, 1, n + 1) \in Seq(LogEntry) /\
           Len(SubSeq(left, 1, n + 1)) = n + 1 /\ Len(SubSeq(right, 1, n + 1)) = n + 1
        BY <1>0, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
    <2>5. \A index \in 1..(n + 1):
            SubSeq(left, 1, n + 1)[index] = SubSeq(right, 1, n + 1)[index]
        BY <1>0, <2>3, SubSeqProperties, ElementOfSeq, 1 \in Int, Nat \subseteq Int
    <2> QED BY <2>4, <2>5, SeqEqual
<1> HIDE DEF P
<1>3. \A n \in Nat: P(n)
    BY <1>1, <1>2, NatInduction, Isa
<1> QED BY <1>0, <1>3 DEF P

LEMMA EntryEdgeConsistencyLogBoundary ==
    InductiveInvariant /\ EntryEdgeConsistency =>
        \A left, right \in Server:
            \A index \in (DOMAIN log[left]) \cap (DOMAIN log[right]):
                log[left][index].term = log[right][index].term =>
                    /\ log[left][index] = log[right][index]
                    /\ index > 1 => log[left][index - 1].term = log[right][index - 1].term
<1> SUFFICES ASSUME InductiveInvariant, EntryEdgeConsistency,
                    NEW left \in Server, NEW right \in Server,
                    NEW index \in (DOMAIN log[left]) \cap (DOMAIN log[right]),
                    log[left][index].term = log[right][index].term
             PROVE /\ log[left][index] = log[right][index]
                   /\ index > 1 => log[left][index - 1].term = log[right][index - 1].term
    OBVIOUS
<1>1. LogEntryEdge(log[left], index) \in HistoricalEntryEdges /\
       LogEntryEdge(log[right], index) \in HistoricalEntryEdges
    BY DEF HistoricalEntryEdges
<1> QED BY <1>1 DEF EntryEdgeConsistency, LogEntryEdge

LEMMA EntryEdgeConsistencyImpliesLogMatching ==
    InductiveInvariant /\ EntryEdgeConsistency => LogMatchingInv
    BY EntryEdgeConsistencyLogBoundary, ConsistentLogEdgesPrefixEqual, LenProperties
       DEF InductiveInvariant, TypeOK, LogVarsTypeOK, LogMatchingInv

LEMMA AppendRequestAcceptedPreviousAnchor ==
    \A recipient, sender \in Server, request \in messages:
        /\ InductiveInvariant /\ request.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(recipient, sender, request) /\ log' # log
        /\ request.mprevLogIndex > 0
        => log[recipient][request.mprevLogIndex].term = request.mprevLogTerm
    BY DEF HandleAppendEntriesRequest

LEMMA EntryEdgeConsistencyInit == Init => EntryEdgeConsistency
    BY DEF Init, InitLogVars, EntryEdgeConsistency, HistoricalEntryEdges, AppendRequests

LEMMA EntryEdgeConsistencySubset ==
    EntryEdgeConsistency /\ HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    => EntryEdgeConsistency'
    BY DEF EntryEdgeConsistency

LEMMA ActiveLeaderFreshTermOwnerImpossible ==
    \A leader, owner \in Server:
        InductiveInvariant /\ state[leader] = Leader
        => ~TermOwner(owner, currentTerm[leader], Len(log[leader]) + 1)
<1> SUFFICES ASSUME NEW leader \in Server, NEW owner \in Server,
                    InductiveInvariant, state[leader] = Leader,
                    TermOwner(owner, currentTerm[leader], Len(log[leader]) + 1)
             PROVE FALSE
    OBVIOUS
<1>1. VoteRecordInv /\ currentTerm[leader] \in Nat /\
       log[leader] \in Seq(LogEntry)
    BY DEF InductiveInvariant, TypeOK, ServerVarsTypeOK, LogVarsTypeOK
<1>2. Won(leader, currentTerm[leader])
    BY ActiveLeaderWon
<1>3. owner = leader
    BY <1>1, <1>2, WonUnique DEF TermOwner
<1>4. Len(log[leader]) + 1 \in DOMAIN log[leader]
    BY <1>3 DEF TermOwner, OwnerActive, LogHasTermAt
<1> QED BY <1>1, <1>4, LenProperties

LEMMA ActiveLeaderFreshLogKey ==
    \A leader, server \in Server: \A index \in DOMAIN log[server]:
        InductiveInvariant /\ state[leader] = Leader
        => ~(index = Len(log[leader]) + 1 /\
             log[server][index].term = currentTerm[leader])
<1> SUFFICES ASSUME NEW leader \in Server, NEW server \in Server,
                    NEW index \in DOMAIN log[server], InductiveInvariant,
                    state[leader] = Leader,
                    index = Len(log[leader]) + 1,
                    log[server][index].term = currentTerm[leader]
             PROVE FALSE
    OBVIOUS
<1>1. PICK owner \in Server:
          TermOwner(owner, currentTerm[leader], Len(log[leader]) + 1)
    BY DEF InductiveInvariant, LogElectionInv
<1> QED BY <1>1, ActiveLeaderFreshTermOwnerImpossible

LEMMA ActiveLeaderFreshRequestKey ==
    \A leader \in Server, request \in AppendRequests:
        \A offset \in DOMAIN request.mentries:
            InductiveInvariant /\ state[leader] = Leader
            => ~(request.mprevLogIndex + offset = Len(log[leader]) + 1 /\
                 request.mentries[offset].term = currentTerm[leader])
<1> SUFFICES ASSUME NEW leader \in Server, NEW request \in AppendRequests,
                    NEW offset \in DOMAIN request.mentries,
                    InductiveInvariant, state[leader] = Leader,
                    request.mprevLogIndex + offset = Len(log[leader]) + 1,
                    request.mentries[offset].term = currentTerm[leader]
             PROVE FALSE
    OBVIOUS
<1>1. request \in messages /\ request.mtype = AppendEntriesRequest
    BY DEF AppendRequests
<1>2. PICK owner \in Server:
          TermOwner(owner, currentTerm[leader], Len(log[leader]) + 1)
    BY <1>1 DEF InductiveInvariant, MessageElectionInv
<1> QED BY <1>2, ActiveLeaderFreshTermOwnerImpossible

LEMMA ActiveLeaderFreshHistoricalKey ==
    \A leader \in Server: \A edge \in HistoricalEntryEdges:
        InductiveInvariant /\ state[leader] = Leader
        => ~(edge.index = Len(log[leader]) + 1 /\
             edge.term = currentTerm[leader])
<1> SUFFICES ASSUME NEW leader \in Server,
                    NEW edge \in HistoricalEntryEdges,
                    InductiveInvariant, state[leader] = Leader,
                    edge.index = Len(log[leader]) + 1,
                    edge.term = currentTerm[leader]
             PROVE FALSE
    OBVIOUS
<1>1. CASE \E server \in Server: \E index \in DOMAIN log[server]:
              edge = LogEntryEdge(log[server], index)
    <2>1. PICK server, index:
              server \in Server /\ index \in DOMAIN log[server] /\ edge = LogEntryEdge(log[server], index)
        BY <1>1
    <2> QED BY <2>1, ActiveLeaderFreshLogKey DEF LogEntryEdge
<1>2. CASE \E request \in AppendRequests:
              \E offset \in DOMAIN request.mentries:
                  edge = RequestEntryEdge(request, offset)
    <2>1. PICK request, offset:
              request \in AppendRequests /\ offset \in DOMAIN request.mentries /\ edge = RequestEntryEdge(request, offset)
        BY <1>2
    <2> QED BY <2>1, ActiveLeaderFreshRequestKey DEF RequestEntryEdge
<1> QED BY <1>1, <1>2 DEF HistoricalEntryEdges

LEMMA AppendRetainsLogEntryEdge ==
    \A entries \in Seq(LogEntry), entry \in LogEntry:
        \A index \in DOMAIN entries:
            LogEntryEdge(Append(entries, entry), index) = LogEntryEdge(entries, index)
<1> SUFFICES ASSUME NEW entries \in Seq(LogEntry), NEW entry \in LogEntry,
                    NEW index \in DOMAIN entries
             PROVE LogEntryEdge(Append(entries, entry), index)
                     = LogEntryEdge(entries, index)
    OBVIOUS
<1>1. index \in 1..Len(entries) /\ Len(entries) \in Nat
    BY LenProperties
<1>2. Append(entries, entry)[index] = entries[index]
    BY <1>1, AppendProperties
<1>3. CASE index = 1
    BY <1>2, <1>3 DEF LogEntryEdge
<1>4. CASE index # 1
    <2>1. index - 1 \in 1..Len(entries)
        BY <1>1, <1>4
    <2>2. Append(entries, entry)[index - 1] = entries[index - 1]
        BY <2>1, AppendProperties
    <2> QED BY <1>2, <2>2 DEF LogEntryEdge
<1> QED BY <1>3, <1>4

LEMMA ClientHistoricalEntryEdges ==
    \A i \in Server, v \in Value:
        InductiveInvariant /\ ClientRequest(i, v)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup
             {LogEntryEdge(log'[i], Len(log[i]) + 1)}
<1> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                    InductiveInvariant, ClientRequest(i, v)
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup
                     {LogEntryEdge(log'[i], Len(log[i]) + 1)}
    OBVIOUS
<1> DEFINE fresh == LogEntryEdge(log'[i], Len(log[i]) + 1)
<1>0. log \in [Server -> Seq(LogEntry)] /\ currentTerm \in [Server -> Nat] /\
       [term |-> currentTerm[i], value |-> v] \in LogEntry
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK, LogEntry
<1>1. log'[i] = Append(log[i], [term |-> currentTerm[i], value |-> v]) /\
       (\A server \in Server: server # i => log'[server] = log[server]) /\
       AppendRequests' = AppendRequests
    BY <1>0 DEF ClientRequest, AppendRequests
<1>2. DOMAIN log'[i] = 1..(Len(log[i]) + 1) /\
       DOMAIN log[i] = 1..Len(log[i]) /\ Len(log[i]) \in Nat
    BY <1>0, <1>1, AppendProperties, LenProperties
<1>3. \A index \in DOMAIN log[i]:
          LogEntryEdge(log'[i], index) = LogEntryEdge(log[i], index)
    BY <1>0, <1>1, AppendRetainsLogEntryEdge
<1>4. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh}
    <2> SUFFICES ASSUME NEW edge \in HistoricalEntryEdges'
                 PROVE edge \in HistoricalEntryEdges \cup {fresh}
        OBVIOUS
    <2>1. CASE \E server \in Server: \E index \in DOMAIN log'[server]:
                  edge = LogEntryEdge(log'[server], index)
        <3>1. PICK server, index:
                  server \in Server /\ index \in DOMAIN log'[server] /\ edge = LogEntryEdge(log'[server], index)
            BY <2>1
        <3>2. CASE server # i
            BY <1>1, <3>1, <3>2 DEF HistoricalEntryEdges
        <3>3. CASE server = i /\ index \in DOMAIN log[i]
            BY <1>3, <3>1, <3>3 DEF HistoricalEntryEdges
        <3>4. CASE server = i /\ index \notin DOMAIN log[i]
            <4>1. index = Len(log[i]) + 1
                BY <1>2, <3>1, <3>4
            <4> QED BY <3>1, <3>4, <4>1 DEF fresh
        <3> QED BY <3>2, <3>3, <3>4
    <2>2. CASE \E request \in AppendRequests':
                  \E offset \in DOMAIN request.mentries:
                      edge = RequestEntryEdge(request, offset)
        BY <1>1, <2>2 DEF HistoricalEntryEdges
    <2> QED BY <2>1, <2>2 DEF HistoricalEntryEdges
<1> QED BY <1>4 DEF fresh

LEMMA EntryEdgeConsistencyClient ==
    \A i \in Server, v \in Value:
        InductiveInvariant /\ EntryEdgeConsistency /\ ClientRequest(i, v)
        => EntryEdgeConsistency'
<1> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                    InductiveInvariant, EntryEdgeConsistency, ClientRequest(i, v),
                    NEW left \in HistoricalEntryEdges',
                    NEW right \in HistoricalEntryEdges',
                    left.index = right.index, left.term = right.term
             PROVE left.entry = right.entry /\ left.previous = right.previous
    BY DEF EntryEdgeConsistency
<1> DEFINE fresh == LogEntryEdge(log'[i], Len(log[i]) + 1)
<1>0. log[i] \in Seq(LogEntry) /\ currentTerm[i] \in Nat /\
       [term |-> currentTerm[i], value |-> v] \in LogEntry /\
       state[i] = Leader /\
       log'[i] = Append(log[i], [term |-> currentTerm[i], value |-> v])
    BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK, ServerVarsTypeOK,
           LogEntry, ClientRequest
<1>1. HistoricalEntryEdges' \subseteq HistoricalEntryEdges \cup {fresh}
    BY ClientHistoricalEntryEdges DEF fresh
<1>2. fresh.index = Len(log[i]) + 1 /\ fresh.term = currentTerm[i] /\
       fresh.entry = [term |-> currentTerm[i], value |-> v]
    BY <1>0, AppendProperties DEF fresh, LogEntryEdge
<1>3. CASE left \in HistoricalEntryEdges /\ right \in HistoricalEntryEdges
    BY <1>3 DEF EntryEdgeConsistency
<1>4. CASE left \in HistoricalEntryEdges /\ right = fresh
    <2>1. left.index = Len(log[i]) + 1 /\ left.term = currentTerm[i]
        BY <1>2, <1>4
    <2> QED BY <1>0, <1>4, <2>1, ActiveLeaderFreshHistoricalKey
<1>5. CASE left = fresh /\ right \in HistoricalEntryEdges
    <2>1. right.index = Len(log[i]) + 1 /\ right.term = currentTerm[i]
        BY <1>2, <1>5
    <2> QED BY <1>0, <1>5, <2>1, ActiveLeaderFreshHistoricalKey
<1>6. CASE left = fresh /\ right = fresh
    BY <1>6
<1> QED BY <1>1, <1>3, <1>4, <1>5, <1>6

LEMMA AppendSendEntryOffsetSnapshot ==
    \A sender, recipient \in Server:
        InductiveInvariant =>
            \A offset \in DOMAIN AppendEntriesEntries(sender, recipient):
                /\ offset = 1
                /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
                /\ AppendEntriesEntries(sender, recipient)[offset]
                    = log[sender][nextIndex[sender][recipient]]
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    InductiveInvariant,
                    NEW offset \in DOMAIN AppendEntriesEntries(sender, recipient)
             PROVE /\ offset = 1
                   /\ nextIndex[sender][recipient] \in DOMAIN log[sender]
                   /\ AppendEntriesEntries(sender, recipient)[offset]
                        = log[sender][nextIndex[sender][recipient]]
    OBVIOUS
<1>1. TypeOK /\ nextIndex[sender][recipient] \in Nat \ {0} /\
       log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) \in Nat /\
       AppendEntriesLastEntry(sender, recipient) <= Len(log[sender]) /\
       AppendEntriesLastEntry(sender, recipient) <= nextIndex[sender][recipient]
    BY AppendEntriesLastEntryTypeOK, MinTypeOK, LenProperties
       DEF InductiveInvariant, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK,
           AppendEntriesLastEntry
<1>2. \A index \in nextIndex[sender][recipient]..AppendEntriesLastEntry(sender, recipient):
        log[sender][index] \in LogEntry
    BY <1>1, ElementOfSeq
<1>3. AppendEntriesEntries(sender, recipient) \in Seq(LogEntry) /\
       Len(AppendEntriesEntries(sender, recipient)) =
           IF nextIndex[sender][recipient] <= AppendEntriesLastEntry(sender, recipient)
           THEN AppendEntriesLastEntry(sender, recipient) - nextIndex[sender][recipient] + 1
           ELSE 0
    BY <1>1, <1>2, AppendEntriesEntriesTypeOK, SubSeqProperties
       DEF AppendEntriesEntries
<1>4. Len(AppendEntriesEntries(sender, recipient)) <= 1
    BY <1>1, <1>3, SMT
<1>5. Len(AppendEntriesEntries(sender, recipient)) \in Nat /\
       DOMAIN AppendEntriesEntries(sender, recipient)
           = 1..Len(AppendEntriesEntries(sender, recipient))
    BY <1>3, LenProperties
<1>6. offset = 1 /\ Len(AppendEntriesEntries(sender, recipient)) = 1
    BY <1>4, <1>5, SMT
<1>7. AppendEntriesEntries(sender, recipient) # << >>
    BY <1>3, <1>6, EmptySeq
<1>8. nextIndex[sender][recipient] \in DOMAIN log[sender] /\
       AppendEntriesEntries(sender, recipient)[1]
           = log[sender][nextIndex[sender][recipient]]
    BY <1>1, <1>7, AppendRequestFirstEntrySnapshot
<1> QED BY <1>6, <1>8

LEMMA AppendSendPreviousSnapshot ==
    \A sender, recipient \in Server:
        InductiveInvariant /\ state[sender] = Leader =>
            /\ nextIndex[sender][recipient] - 1 \in Nat
            /\ (nextIndex[sender][recipient] = 1 =>
                AppendEntriesPrevLogTerm(sender, recipient) = 0)
            /\ (nextIndex[sender][recipient] > 1 =>
                /\ nextIndex[sender][recipient] - 1 \in DOMAIN log[sender]
                /\ AppendEntriesPrevLogTerm(sender, recipient)
                    = log[sender][nextIndex[sender][recipient] - 1].term)
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    InductiveInvariant, state[sender] = Leader
             PROVE /\ nextIndex[sender][recipient] - 1 \in Nat
                   /\ (nextIndex[sender][recipient] = 1 =>
                       AppendEntriesPrevLogTerm(sender, recipient) = 0)
                   /\ (nextIndex[sender][recipient] > 1 =>
                       /\ nextIndex[sender][recipient] - 1 \in DOMAIN log[sender]
                       /\ AppendEntriesPrevLogTerm(sender, recipient)
                           = log[sender][nextIndex[sender][recipient] - 1].term)
    OBVIOUS
<1>1. nextIndex[sender][recipient] \in Nat \ {0} /\
       nextIndex[sender][recipient] <= Len(log[sender]) + 1 /\
       log[sender] \in Seq(LogEntry) /\ Len(log[sender]) \in Nat /\
       DOMAIN log[sender] = 1..Len(log[sender])
    BY LenProperties
       DEF InductiveInvariant, NextIndexBound, TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>2. nextIndex[sender][recipient] - 1 \in Nat /\
       (nextIndex[sender][recipient] > 1 =>
           nextIndex[sender][recipient] - 1 \in DOMAIN log[sender])
    BY <1>1, SMT
<1> QED BY <1>1, <1>2 DEF AppendEntriesPrevLogTerm

LEMMA AppendSendRequestEdgeSnapshot ==
    \A sender, recipient \in Server:
        InductiveInvariant /\ state[sender] = Leader =>
            \A offset \in DOMAIN AppendEntriesMessage(sender, recipient).mentries:
                /\ AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
                    \in DOMAIN log[sender]
                /\ RequestEntryEdge(AppendEntriesMessage(sender, recipient), offset)
                    = LogEntryEdge(log[sender],
                        AppendEntriesMessage(sender, recipient).mprevLogIndex + offset)
<1> SUFFICES ASSUME NEW sender \in Server, NEW recipient \in Server,
                    InductiveInvariant, state[sender] = Leader,
                    NEW offset \in DOMAIN AppendEntriesMessage(sender, recipient).mentries
             PROVE /\ AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
                        \in DOMAIN log[sender]
                   /\ RequestEntryEdge(AppendEntriesMessage(sender, recipient), offset)
                        = LogEntryEdge(log[sender],
                            AppendEntriesMessage(sender, recipient).mprevLogIndex + offset)
    OBVIOUS
<1>1. offset \in DOMAIN AppendEntriesEntries(sender, recipient)
    BY DEF AppendEntriesMessage
<1>2. offset = 1 /\ nextIndex[sender][recipient] \in DOMAIN log[sender] /\
       AppendEntriesEntries(sender, recipient)[offset]
           = log[sender][nextIndex[sender][recipient]]
    BY <1>1, AppendSendEntryOffsetSnapshot
<1>3. nextIndex[sender][recipient] \in Nat \ {0} /\
       AppendEntriesMessage(sender, recipient).mprevLogIndex
           = nextIndex[sender][recipient] - 1 /\
       AppendEntriesMessage(sender, recipient).mentries
           = AppendEntriesEntries(sender, recipient) /\
       AppendEntriesMessage(sender, recipient).mprevLogTerm
           = AppendEntriesPrevLogTerm(sender, recipient)
    BY DEF InductiveInvariant, TypeOK, LeaderVarsTypeOK, AppendEntriesMessage
<1>4. AppendEntriesMessage(sender, recipient).mprevLogIndex + offset
           = nextIndex[sender][recipient]
    BY <1>2, <1>3, SMT
<1>5. CASE nextIndex[sender][recipient] = 1
    BY <1>2, <1>3, <1>4, <1>5, AppendSendPreviousSnapshot
       DEF RequestEntryEdge, LogEntryEdge
<1>6. CASE nextIndex[sender][recipient] > 1
    BY <1>2, <1>3, <1>4, <1>6, AppendSendPreviousSnapshot
       DEF RequestEntryEdge, LogEntryEdge
<1> QED BY <1>3, <1>5, <1>6

LEMMA EntryEdgeAppendSendSubset ==
    \A i, j \in Server:
        InductiveInvariant /\ AppendEntries(i, j)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    InductiveInvariant, AppendEntries(i, j)
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    OBVIOUS
<1>1. log' = log /\ state[i] = Leader /\
       messages' = messages \cup {AppendEntriesMessage(i, j)} /\
       AppendRequests' = AppendRequests \cup {AppendEntriesMessage(i, j)}
    BY DEF AppendEntries, Send, WithMessage, WithMessages,
           AppendRequests, AppendEntriesMessage
<1>2. \A server \in Server: \A index \in DOMAIN log'[server]:
        LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
    BY <1>1 DEF HistoricalEntryEdges
<1>3. \A request \in AppendRequests':
        \A offset \in DOMAIN request.mentries:
            RequestEntryEdge(request, offset) \in HistoricalEntryEdges
    <2> SUFFICES ASSUME NEW request \in AppendRequests',
                        NEW offset \in DOMAIN request.mentries
                 PROVE RequestEntryEdge(request, offset) \in HistoricalEntryEdges
        OBVIOUS
    <2>1. CASE request \in AppendRequests
        BY <2>1 DEF HistoricalEntryEdges
    <2>2. CASE request = AppendEntriesMessage(i, j)
        <3>1. request.mprevLogIndex + offset \in DOMAIN log[i] /\
               RequestEntryEdge(request, offset)
                   = LogEntryEdge(log[i], request.mprevLogIndex + offset)
            BY <1>1, <2>2, AppendSendRequestEdgeSnapshot
        <3> QED BY <3>1 DEF HistoricalEntryEdges
    <2> QED BY <1>1, <2>1, <2>2
<1> QED BY <1>2, <1>3 DEF HistoricalEntryEdges

LEMMA AppendRequestRootTermInit == Init => AppendRequestRootTerm
    BY DEF Init, AppendRequests, AppendRequestRootTerm

LEMMA AppendRequestRootTermNext ==
    InductiveInvariant /\ AppendRequestRootTerm /\ [Next]_vars => AppendRequestRootTerm'
<1> SUFFICES ASSUME InductiveInvariant, AppendRequestRootTerm, [Next]_vars,
                    NEW m \in AppendRequests', m.mprevLogIndex = 0
             PROVE m.mprevLogTerm = 0
    BY DEF AppendRequestRootTerm
<1>1. CASE m \in messages
    BY <1>1 DEF AppendRequests, AppendRequestRootTerm
<1>2. CASE m \notin messages
    <2>1. PICK i, j \in Server: AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
        BY <1>2, NewAppendRequestOrigin DEF AppendRequests
    <2> QED BY <2>1 DEF AppendEntriesMessage, AppendEntriesPrevLogTerm,
                            InductiveInvariant, TypeOK, LeaderVarsTypeOK
<1> QED BY <1>1, <1>2

LEMMA AppendReceiveLogEdgeWitness ==
    \A i, j \in Server, m \in messages:
        InductiveInvariant /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => \A server \in Server: \A index \in DOMAIN log'[server]:
            \E edge \in HistoricalEntryEdges:
                /\ edge.index = index
                /\ edge.term = log'[server][index].term
                /\ edge.entry = log'[server][index]
                /\ (index > 1 => edge.previous = log'[server][index - 1].term)
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server, NEW m \in messages,
                    InductiveInvariant, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(i, j, m), NEW server \in Server,
                    NEW index \in DOMAIN log'[server]
             PROVE \E edge \in HistoricalEntryEdges:
                 /\ edge.index = index
                 /\ edge.term = log'[server][index].term
                 /\ edge.entry = log'[server][index]
                 /\ (index > 1 => edge.previous = log'[server][index - 1].term)
    OBVIOUS
<1>types. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
           m.mentries \in Seq(LogEntry) /\ m \in AppendRequests
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, LogVarsTypeOK, MsgTypeOK, AppendRequests
<1>1. CASE log' = log
    BY <1>1 DEF HistoricalEntryEdges, LogEntryEdge
<1>2. CASE server # i
    <2>1. log'[server] = log[server]
        BY <1>types, <1>2 DEF HandleAppendEntriesRequest
    <2> QED BY <2>1 DEF HistoricalEntryEdges, LogEntryEdge
<1>3. CASE log' # log /\ server = i
    <2>shape. m.mprevLogIndex \in 0..Len(log[i]) /\ m.mentries # << >> /\
              m.mentries[1] \in LogEntry /\ Len(log'[i]) = m.mprevLogIndex + 1
        BY <1>3, AppendRequestChangedLogShape
    <2>seq. SubSeq(log[i], 1, m.mprevLogIndex) \in Seq(LogEntry)
        BY <1>types, <2>shape, SubSeqProperties, ElementOfSeq, LenProperties,
           1 \in Int, Nat \subseteq Int
    <2>post. log'[i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])
        BY <1>types, <1>3 DEF HandleAppendEntriesRequest
    <2>typed. log'[i] \in Seq(LogEntry) /\ Len(log'[i]) \in Nat /\
              DOMAIN log'[i] = 1..Len(log'[i]) /\ DOMAIN m.mentries = 1..Len(m.mentries) /\
              Len(m.mentries) \in Nat
        BY <1>types, <2>shape, <2>seq, <2>post, AppendProperties, LenProperties
    <2>first. 1 \in DOMAIN m.mentries
        BY ONLY <1>types, <2>shape, EmptySeq, LenProperties
    <2>domain. DOMAIN log'[i] = 1..(m.mprevLogIndex + 1) /\
               1 \in DOMAIN m.mentries /\ index \in Nat
        BY ONLY <1>3, <2>shape, <2>typed, <2>first,
            index \in DOMAIN log'[server], SMT
    <2>1. CASE index <= m.mprevLogIndex
        <3>1. index \in DOMAIN log[i] /\ log'[i][index] = log[i][index]
            BY <1>types, <1>3, <2>shape, <2>domain, <2>1,
               AppendRequestRetainsMatchedPrefix, LenProperties
        <3>2. index > 1 => log'[i][index - 1] = log[i][index - 1]
            BY <1>types, <1>3, <2>shape, <2>domain, <2>1,
               AppendRequestRetainsMatchedPrefix
        <3>3. LogEntryEdge(log[i], index) \in HistoricalEntryEdges /\
               LogEntryEdge(log[i], index).index = index /\
               LogEntryEdge(log[i], index).term = log'[server][index].term /\
               LogEntryEdge(log[i], index).entry = log'[server][index] /\
               (index > 1 =>
                   LogEntryEdge(log[i], index).previous = log'[server][index - 1].term)
            BY <1>3, <3>1, <3>2 DEF HistoricalEntryEdges, LogEntryEdge
        <3> QED BY <3>3
    <2>2. CASE index > m.mprevLogIndex
        <3>1. index = m.mprevLogIndex + 1 /\ log'[i][index] = m.mentries[1]
            BY <1>3, <2>shape, <2>domain, <2>2, AppendRequestCopiesEndpointEntry
        <3>2. index > 1 => log'[i][index - 1].term = m.mprevLogTerm
            BY <1>types, <1>3, <2>shape, <3>1, AppendRequestAcceptedPreviousAnchor,
               AppendRequestRetainsMatchedPrefix
        <3>3. RequestEntryEdge(m, 1) \in HistoricalEntryEdges /\
               RequestEntryEdge(m, 1).index = index /\
               RequestEntryEdge(m, 1).term = log'[server][index].term /\
               RequestEntryEdge(m, 1).entry = log'[server][index] /\
               (index > 1 =>
                   RequestEntryEdge(m, 1).previous = log'[server][index - 1].term)
            BY <1>types, <1>3, <2>domain, <3>1, <3>2
               DEF HistoricalEntryEdges, RequestEntryEdge
        <3> QED BY <3>3
    <2>split. index <= m.mprevLogIndex \/ index > m.mprevLogIndex
        BY ONLY <1>types, <2>domain, SMT
    <2> QED BY ONLY <2>split, <2>1, <2>2
<1> QED BY <1>1, <1>2, <1>3

LEMMA AppendReceiveLogEdgeOrigin ==
    \A i, j \in Server, m \in messages:
        InductiveInvariant /\ AppendRequestRootTerm /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => \A server \in Server: \A index \in DOMAIN log'[server]:
            LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server, NEW m \in messages,
                    InductiveInvariant, AppendRequestRootTerm, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(i, j, m), NEW server \in Server,
                    NEW index \in DOMAIN log'[server]
             PROVE LogEntryEdge(log'[server], index) \in HistoricalEntryEdges
    OBVIOUS
<1>0. log \in [Server -> Seq(LogEntry)] /\ m.mprevLogIndex \in Nat /\
       m.mentries \in Seq(LogEntry) /\ m \in AppendRequests
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, LogVarsTypeOK, MsgTypeOK, AppendRequests
<1>1. CASE log' = log
    BY <1>1 DEF HistoricalEntryEdges
<1>2. CASE server # i
    <2>1. log'[server] = log[server]
        BY <1>0, <1>2 DEF HandleAppendEntriesRequest
    <2> QED BY <2>1 DEF HistoricalEntryEdges
<1>3. CASE log' # log /\ server = i
    <2>shape. m.mprevLogIndex \in 0..Len(log[i]) /\ m.mentries # << >> /\
              m.mentries[1] \in LogEntry /\ Len(log'[i]) = m.mprevLogIndex + 1
        BY <1>3, AppendRequestChangedLogShape
    <2>seq. SubSeq(log[i], 1, m.mprevLogIndex) \in Seq(LogEntry)
        BY <1>0, <2>shape, SubSeqProperties, ElementOfSeq, LenProperties,
           1 \in Int, Nat \subseteq Int
    <2>post. log'[i] = Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])
        BY <1>0, <1>3 DEF HandleAppendEntriesRequest
    <2>typed. log'[i] \in Seq(LogEntry) /\ Len(log'[i]) \in Nat /\
              DOMAIN log'[i] = 1..Len(log'[i]) /\ DOMAIN m.mentries = 1..Len(m.mentries) /\
              Len(m.mentries) \in Nat
        BY <1>0, <2>shape, <2>seq, <2>post, AppendProperties, LenProperties
    <2>0. m.mprevLogIndex \in 0..Len(log[i]) /\ m.mentries # << >> /\
           Len(log'[i]) = m.mprevLogIndex + 1 /\
           DOMAIN log'[i] = 1..(m.mprevLogIndex + 1) /\ 1 \in DOMAIN m.mentries /\ index \in Nat
        BY <1>0, <1>3, <2>shape, <2>typed, EmptySeq
    <2>1. CASE index <= m.mprevLogIndex
        <3>1. index \in DOMAIN log[i] /\ log'[i][index] = log[i][index]
            BY <1>0, <1>3, <2>0, <2>1, AppendRequestRetainsMatchedPrefix, LenProperties
        <3>2. index > 1 => log'[i][index - 1] = log[i][index - 1]
            BY <1>0, <1>3, <2>0, <2>1, AppendRequestRetainsMatchedPrefix
        <3>3. LogEntryEdge(log'[server], index) = LogEntryEdge(log[i], index)
            BY <1>3, <2>0, <3>1, <3>2 DEF LogEntryEdge
        <3> QED BY <3>1, <3>3 DEF HistoricalEntryEdges
    <2>2. CASE index > m.mprevLogIndex
        <3>1. index = m.mprevLogIndex + 1 /\ log'[i][index] = m.mentries[1]
            BY <1>3, <2>0, <2>2, AppendRequestCopiesEndpointEntry
        <3>2. m.mprevLogIndex > 0 =>
                log'[i][index - 1].term = m.mprevLogTerm
            BY <1>0, <1>3, <2>0, <3>1, AppendRequestAcceptedPreviousAnchor,
               AppendRequestRetainsMatchedPrefix
        <3>3. m.mprevLogIndex = 0 => m.mprevLogTerm = 0
            BY <1>0 DEF AppendRequestRootTerm
        <3>4. LogEntryEdge(log'[server], index) = RequestEntryEdge(m, 1)
            BY <1>0, <1>3, <3>1, <3>2, <3>3 DEF LogEntryEdge, RequestEntryEdge
        <3> QED BY <1>0, <2>0, <3>4 DEF HistoricalEntryEdges
    <2> QED BY <2>0, <2>1, <2>2
<1> QED BY <1>1, <1>2, <1>3

LEMMA AppendReceiveRequestEdgesUnchanged ==
    \A i, j \in Server, m \in messages:
        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => AppendRequests' = AppendRequests
    BY MessageTypesDistinct DEF HandleAppendEntriesRequest, Send, WithMessage, WithMessages, AppendRequests

LEMMA EntryEdgeAppendReceiveSubset ==
    \A i, j \in Server, m \in messages:
        InductiveInvariant /\ AppendRequestRootTerm /\ m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
        => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    BY AppendReceiveLogEdgeOrigin, AppendReceiveRequestEdgesUnchanged DEF HistoricalEntryEdges

LEMMA LogChangingActionNext ==
    InductiveInvariant /\ [Next]_vars =>
        \/ (\E leader \in Server, value \in Value: ClientRequest(leader, value))
        \/ (\E m \in messages:
                m.mtype = AppendEntriesRequest /\
                HandleAppendEntriesRequest(m.mdest, m.msource, m))
        \/ log' = log
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars, log' # log,
                    ~(\E leader \in Server, value \in Value: ClientRequest(leader, value))
             PROVE \E m \in messages:
                 m.mtype = AppendEntriesRequest /\
                 HandleAppendEntriesRequest(m.mdest, m.msource, m)
    OBVIOUS
<1>receive. \E m \in messages: Receive(m)
    BY DEF Next, vars, Restart, Timeout, BecomeLeader,
           AdvanceCommitIndex, AppendEntries, LeaderStepDown
<1> PICK m \in messages: Receive(m) BY <1>receive
<1>types. /\ m.mterm \in Nat /\ m.mdest \in Server /\ m.msource \in Server
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK, MsgTypeOK
<1>append. m.mtype = AppendEntriesRequest /\
           HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>types
       DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
           HandleRequestVoteResponse, HandleAppendEntriesResponse
<1> QED BY <1>append

LEMMA EntryEdgeOtherSubset ==
    InductiveInvariant /\ [Next]_vars
    /\ ~(\E i \in Server, v \in Value: ClientRequest(i, v))
    /\ ~(\E i, j \in Server: AppendEntries(i, j))
    /\ ~(\E i, j \in Server, m \in messages:
            m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m))
    => HistoricalEntryEdges' \subseteq HistoricalEntryEdges
<1> SUFFICES ASSUME InductiveInvariant, [Next]_vars,
                    ~(\E i \in Server, v \in Value: ClientRequest(i, v)),
                    ~(\E i, j \in Server: AppendEntries(i, j)),
                    ~(\E i, j \in Server, m \in messages:
                        m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m))
             PROVE HistoricalEntryEdges' \subseteq HistoricalEntryEdges
    OBVIOUS
<1>types. \A m \in messages: m.mdest \in Server /\ m.msource \in Server
    BY StoredMessageFieldsTypeOK DEF InductiveInvariant
<1>1. log' = log
    BY LogChangingActionNext, <1>types
<1>2. AppendRequests' \subseteq AppendRequests
    BY NewAppendRequestOrigin DEF AppendRequests
<1> QED BY <1>1, <1>2 DEF HistoricalEntryEdges

LEMMA EntryEdgeConsistencyNext ==
    InductiveInvariant /\ AppendRequestRootTerm /\ EntryEdgeConsistency /\ [Next]_vars => EntryEdgeConsistency'
<1>1. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    BY <1>1, EntryEdgeConsistencyClient
<1>2. CASE \E i, j \in Server: AppendEntries(i, j)
    BY <1>2, EntryEdgeAppendSendSubset, EntryEdgeConsistencySubset
<1>3. CASE \E i, j \in Server, m \in messages:
            m.mtype = AppendEntriesRequest /\ HandleAppendEntriesRequest(i, j, m)
    BY <1>3, EntryEdgeAppendReceiveSubset, EntryEdgeConsistencySubset
<1> QED BY <1>1, <1>2, <1>3, EntryEdgeOtherSubset, EntryEdgeConsistencySubset

LEMMA LogMatchingInvNext ==
    InductiveInvariant /\ EntryEdgeConsistency /\ [Next]_vars => LogMatchingInv'
<1> SUFFICES ASSUME InductiveInvariant, EntryEdgeConsistency, [Next]_vars
             PROVE LogMatchingInv'
    OBVIOUS
<1>inductive. InductiveInvariant' BY InductiveInvariantNext
<1>types. log' \in [Server -> Seq(LogEntry)] /\
           \A m \in messages: m.mdest \in Server /\ m.msource \in Server
    BY <1>inductive, StoredMessageFieldsTypeOK
       DEF InductiveInvariant, TypeOK, LogVarsTypeOK
<1>1. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    <2>edges. EntryEdgeConsistency' BY <1>1, EntryEdgeConsistencyClient
    <2> QED BY <1>inductive, <2>edges, EntryEdgeConsistencyImpliesLogMatching, PTL
<1>2. CASE \E m \in messages:
              m.mtype = AppendEntriesRequest /\
              HandleAppendEntriesRequest(m.mdest, m.msource, m)
    <2> PICK m \in messages:
              m.mtype = AppendEntriesRequest /\
              HandleAppendEntriesRequest(m.mdest, m.msource, m)
        BY <1>2
    <2>boundary. \A left, right \in Server:
                    \A index \in (DOMAIN log'[left]) \cap (DOMAIN log'[right]):
                        log'[left][index].term = log'[right][index].term =>
                            /\ log'[left][index] = log'[right][index]
                            /\ (index > 1 =>
                                log'[left][index - 1].term = log'[right][index - 1].term)
        <3> SUFFICES ASSUME NEW left \in Server, NEW right \in Server,
                            NEW index \in (DOMAIN log'[left]) \cap (DOMAIN log'[right]),
                            log'[left][index].term = log'[right][index].term
                     PROVE /\ log'[left][index] = log'[right][index]
                           /\ (index > 1 =>
                               log'[left][index - 1].term = log'[right][index - 1].term)
            OBVIOUS
        <3>1. PICK leftEdge \in HistoricalEntryEdges:
                  /\ leftEdge.index = index
                  /\ leftEdge.term = log'[left][index].term
                  /\ leftEdge.entry = log'[left][index]
                  /\ (index > 1 => leftEdge.previous = log'[left][index - 1].term)
            BY <1>types, AppendReceiveLogEdgeWitness
        <3>2. PICK rightEdge \in HistoricalEntryEdges:
                  /\ rightEdge.index = index
                  /\ rightEdge.term = log'[right][index].term
                  /\ rightEdge.entry = log'[right][index]
                  /\ (index > 1 => rightEdge.previous = log'[right][index - 1].term)
            BY <1>types, AppendReceiveLogEdgeWitness
        <3> QED BY <3>1, <3>2 DEF EntryEdgeConsistency
    <2> QED BY <1>types, <2>boundary, ConsistentLogEdgesPrefixEqual, LenProperties
               DEF LogMatchingInv
<1>3. CASE log' = log
    BY <1>3, EntryEdgeConsistencyImpliesLogMatching DEF LogMatchingInv
<1> QED BY <1>1, <1>2, <1>3, LogChangingActionNext

-----------------------------------------------------------------------------

THEOREM AppendRequestRootTermInvariant == Spec => []AppendRequestRootTerm
    BY AppendRequestRootTermInit, AppendRequestRootTermNext, InductiveInvariantInvariant, PTL DEF Spec

THEOREM EntryEdgeConsistencyInvariant == Spec => []EntryEdgeConsistency
    BY EntryEdgeConsistencyInit, EntryEdgeConsistencyNext, InductiveInvariantInvariant,
       AppendRequestRootTermInvariant, PTL DEF Spec

THEOREM ClusterLogMatchingInvariant == Spec => []LogMatchingInv
    BY EntryEdgeConsistencyInvariant, InductiveInvariantInvariant,
       EntryEdgeConsistencyImpliesLogMatching, PTL

=============================================================================
