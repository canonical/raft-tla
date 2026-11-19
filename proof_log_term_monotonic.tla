------------------------- MODULE proof_log_term_monotonic -------------------------
\* proof_log_term_monotonic.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_inductiveinvariant

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

---------------------------------------------------------------------

LEMMA TermOrderingInvInit == Init => TermOrderingInv
    BY DEF Init, InitLogVars, TermOrderingInv,
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
    OBVIOUS
<1>domain. /\ DOMAIN entries = 1..Len(entries)
             /\ DOMAIN Append(entries, entry) = 1..(Len(entries) + 1)
    BY AppendProperties, LenProperties
<1>old_last. CASE last \in DOMAIN entries
    <2>old_first. first \in DOMAIN entries
        BY <1>old_last, <1>domain
    <2>unchanged. /\ Append(entries, entry)[first] = entries[first]
                    /\ Append(entries, entry)[last] = entries[last]
        BY <1>old_last, <2>old_first, AppendProperties
    <2> QED BY <1>old_last, <2>old_first, <2>unchanged
<1>new_last. CASE last \notin DOMAIN entries
    <2>last_index. last = Len(entries) + 1
        BY <1>new_last, <1>domain
    <2>last_entry. Append(entries, entry)[last] = entry
        BY <2>last_index, AppendProperties
    <2>old_first. CASE first \in DOMAIN entries
        BY <2>old_first, <2>last_entry, AppendProperties
    <2>new_first. CASE first \notin DOMAIN entries
        <3>first_index. first = Len(entries) + 1
            BY <2>new_first, <1>domain
        <3>entry_type. entry.term \in Nat BY DEF LogEntry
        <3> QED BY <2>last_index, <3>first_index, <3>entry_type
    <2> QED BY <2>old_first, <2>new_first
<1> QED BY <1>old_last, <1>new_last

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
    OBVIOUS
<1>prefix. /\ SubSeq(entries, 1, cut) \in Seq(LogEntry)
             /\ DOMAIN SubSeq(entries, 1, cut) = 1..cut
             /\ \A index \in 1..cut:
                    SubSeq(entries, 1, cut)[index] = entries[index]
    BY SubSeqProperties, LenProperties, ElementOfSeq
<1>ordered. \A first, last \in DOMAIN SubSeq(entries, 1, cut):
                first <= last =>
                    SubSeq(entries, 1, cut)[first].term <=
                        SubSeq(entries, 1, cut)[last].term
    BY <1>prefix, LenProperties
<1>bound. \A index \in DOMAIN SubSeq(entries, 1, cut):
              SubSeq(entries, 1, cut)[index].term <= entry.term
    <2> SUFFICES ASSUME NEW index \in DOMAIN SubSeq(entries, 1, cut)
                 PROVE SubSeq(entries, 1, cut)[index].term <= entry.term
        OBVIOUS
    <2>indexes. /\ index \in DOMAIN entries
                  /\ cut \in DOMAIN entries
                  /\ index <= cut
                  /\ cut > 0
        BY <1>prefix, LenProperties
    <2>terms. /\ entries[index].term \in Nat
                /\ entries[cut].term \in Nat
                /\ entry.term \in Nat
        BY <2>indexes, ElementOfSeq DEF LogEntry
    <2>ordered. entries[index].term <= entries[cut].term
        BY <2>indexes
    <2> QED BY <1>prefix, <2>indexes, <2>terms, <2>ordered, NatLeqTransitive
<1> QED BY <1>prefix, <1>ordered, <1>bound, AppendPreservesLogTermsMonotonic

LEMMA ClientRequestPreservesLogTermsMonotonic ==
    \A i \in Server, v \in Value:
        /\ InductiveInvariant /\ LogTermsMonotonic /\ ClientRequest(i, v)
        => LogTermsMonotonic'
<1> SUFFICES ASSUME NEW i \in Server, NEW v \in Value,
                    InductiveInvariant, LogTermsMonotonic, ClientRequest(i, v),
                    NEW server \in Server
             PROVE \A first, last \in DOMAIN log'[server]:
                       first <= last =>
                           log'[server][first].term <= log'[server][last].term
    BY DEF LogTermsMonotonic
<1>other. CASE server # i
    BY <1>other DEF ClientRequest, LogTermsMonotonic,
        InductiveInvariant, TypeOK, LogVarsTypeOK
<1>same. CASE server = i
    <2>types. /\ log[i] \in Seq(LogEntry)
                /\ [term |-> currentTerm[i], value |-> v] \in LogEntry
        BY DEF InductiveInvariant, TypeOK, LogVarsTypeOK,
            ServerVarsTypeOK, LogEntry
    <2>ordered. \A first, last \in DOMAIN log[i]:
                    first <= last => log[i][first].term <= log[i][last].term
        BY DEF LogTermsMonotonic
    <2>bound. \A index \in DOMAIN log[i]:
                  log[i][index].term <= currentTerm[i]
        BY DEF InductiveInvariant, LogTermBoundInv
    <2>append. log'[server] = Append(log[i],
                  [term |-> currentTerm[i], value |-> v])
        BY <1>same DEF ClientRequest, InductiveInvariant, TypeOK, LogVarsTypeOK
    <2> QED BY <2>types, <2>ordered, <2>bound, <2>append,
        AppendPreservesLogTermsMonotonic
<1> QED BY <1>other, <1>same

LEMMA HandleAppendEntriesRequestPreservesLogTermsMonotonic ==
    \A m \in messages:
        /\ InductiveInvariant /\ TermOrderingInv
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
        => LogTermsMonotonic'
<1> SUFFICES ASSUME NEW m \in messages, InductiveInvariant,
                    TermOrderingInv, m.mtype = AppendEntriesRequest,
                    HandleAppendEntriesRequest(m.mdest, m.msource, m),
                    NEW server \in Server
             PROVE \A first, last \in DOMAIN log'[server]:
                       first <= last =>
                           log'[server][first].term <= log'[server][last].term
    BY DEF LogTermsMonotonic
<1>types. /\ log \in [Server -> Seq(LogEntry)]
            /\ m.mdest \in Server
            /\ m.mprevLogIndex \in Nat
            /\ m.mentries \in Seq(LogEntry)
    BY MessageFieldsTypeOK DEF InductiveInvariant, TypeOK,
        LogVarsTypeOK, MsgTypeOK
<1>other. CASE server # m.mdest
    BY <1>other, <1>types
    DEF HandleAppendEntriesRequest, TermOrderingInv, LogTermsMonotonic
<1>same. CASE server = m.mdest
    <2>unchanged. CASE log'[server] = log[server]
        BY <2>unchanged DEF TermOrderingInv, LogTermsMonotonic
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
            BY <1>types, <3>shape, EmptySeq, LenProperties, ElementOfSeq
        <3>ordered. \A first, last \in DOMAIN log[server]:
                        first <= last =>
                            log[server][first].term <= log[server][last].term
            BY DEF TermOrderingInv, LogTermsMonotonic
        <3>boundary. m.mprevLogIndex > 0 =>
                        log[server][m.mprevLogIndex].term <= m.mentries[1].term
            BY <3>shape DEF TermOrderingInv, MessageTermsMonotonic
        <3> QED BY <1>types, <3>shape, <3>entry, <3>ordered, <3>boundary,
            PrefixAppendPreservesLogTermsMonotonic
    <2> QED BY <2>unchanged, <2>changed
<1> QED BY <1>other, <1>same

LEMMA AppendEntriesFirstEntrySnapshot ==
    \A i, j \in Server:
        /\ TypeOK /\ AppendEntriesEntries(i, j) # << >>
        => /\ nextIndex[i][j] \in DOMAIN log[i]
           /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    TypeOK, AppendEntriesEntries(i, j) # << >>
             PROVE /\ nextIndex[i][j] \in DOMAIN log[i]
                   /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    OBVIOUS
<1>types. /\ nextIndex[i][j] \in Nat \ {0}
            /\ log[i] \in Seq(LogEntry)
            /\ Len(log[i]) \in Nat
            /\ AppendEntriesLastEntry(i, j) \in Nat
            /\ AppendEntriesLastEntry(i, j) <= Len(log[i])
    BY AppendEntriesLastEntryTypeOK, LenProperties
    DEF TypeOK, LeaderVarsTypeOK, LogVarsTypeOK
<1>elements. \A index \in nextIndex[i][j]..AppendEntriesLastEntry(i, j):
                 log[i][index] \in LogEntry
    BY <1>types, ElementOfSeq
<1>length. Len(AppendEntriesEntries(i, j)) =
               IF nextIndex[i][j] <= AppendEntriesLastEntry(i, j)
               THEN AppendEntriesLastEntry(i, j) - nextIndex[i][j] + 1
               ELSE 0
    BY <1>types, <1>elements, SubSeqProperties DEF AppendEntriesEntries
<1>nonempty. /\ AppendEntriesEntries(i, j) \in Seq(LogEntry)
               /\ Len(AppendEntriesEntries(i, j)) \in Nat \ {0}
    BY AppendEntriesEntriesTypeOK, EmptySeq
<1>index. nextIndex[i][j] \in DOMAIN log[i]
    BY <1>types, <1>length, <1>nonempty, LenProperties
<1>entry. AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    BY <1>types, <1>elements, <1>length, <1>nonempty, SubSeqProperties
    DEF AppendEntriesEntries
<1> QED BY <1>index, <1>entry

LEMMA AppendEntriesMessageTermsMonotonic ==
    \A i, j \in Server:
        /\ InductiveInvariant /\ LogTermsMonotonic
        /\ AppendEntriesMessage(i, j).mprevLogIndex > 0
        /\ AppendEntriesMessage(i, j).mentries # << >>
        => AppendEntriesMessage(i, j).mprevLogTerm <=
               AppendEntriesMessage(i, j).mentries[1].term
<1> SUFFICES ASSUME NEW i \in Server, NEW j \in Server,
                    InductiveInvariant, LogTermsMonotonic,
                    AppendEntriesMessage(i, j).mprevLogIndex > 0,
                    AppendEntriesMessage(i, j).mentries # << >>
             PROVE AppendEntriesMessage(i, j).mprevLogTerm <=
                       AppendEntriesMessage(i, j).mentries[1].term
    OBVIOUS
<1>snapshot. /\ nextIndex[i][j] \in DOMAIN log[i]
               /\ AppendEntriesEntries(i, j)[1] = log[i][nextIndex[i][j]]
    BY AppendEntriesFirstEntrySnapshot
    DEF InductiveInvariant, AppendEntriesMessage
<1>indexes. /\ nextIndex[i][j] - 1 \in DOMAIN log[i]
              /\ nextIndex[i][j] - 1 <= nextIndex[i][j]
              /\ nextIndex[i][j] - 1 > 0
    BY <1>snapshot, LenProperties
    DEF AppendEntriesMessage, InductiveInvariant, TypeOK,
        LogVarsTypeOK, LeaderVarsTypeOK
<1>ordered. log[i][nextIndex[i][j] - 1].term <= log[i][nextIndex[i][j]].term
    BY <1>snapshot, <1>indexes DEF LogTermsMonotonic
<1> QED BY <1>snapshot, <1>indexes, <1>ordered
    DEF AppendEntriesMessage, AppendEntriesPrevLogTerm

LEMMA LogTermsMonotonicNext ==
    InductiveInvariant /\ TermOrderingInv /\ [Next]_vars => LogTermsMonotonic'
<1>client. CASE \E i \in Server, v \in Value: ClientRequest(i, v)
    BY <1>client, ClientRequestPreservesLogTermsMonotonic DEF TermOrderingInv
<1>append. CASE \E m \in messages:
        /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(m.mdest, m.msource, m)
    BY <1>append, HandleAppendEntriesRequestPreservesLogTermsMonotonic
<1>unchanged. CASE UNCHANGED log
    BY <1>unchanged DEF TermOrderingInv, LogTermsMonotonic
<1> QED BY <1>client, <1>append, <1>unchanged
    DEF Next, vars, Restart, Timeout, BecomeLeader, AdvanceCommitIndex,
        AppendEntries, LeaderStepDown, Receive, UpdateTerm, HandleMsg,
        HandleRequestVoteRequest, HandleRequestVoteResponse,
        HandleAppendEntriesResponse

LEMMA MessageTermsMonotonicNext ==
    InductiveInvariant /\ TermOrderingInv /\ [Next]_vars => MessageTermsMonotonic'
<1> SUFFICES ASSUME InductiveInvariant, TermOrderingInv, [Next]_vars,
                    NEW m \in messages', m.mtype = AppendEntriesRequest,
                    m.mprevLogIndex > 0, m.mentries # << >>
             PROVE m.mprevLogTerm <= m.mentries[1].term
    BY DEF MessageTermsMonotonic
<1>old. CASE m \in messages
    BY <1>old DEF TermOrderingInv, MessageTermsMonotonic
<1>new. CASE m \notin messages
    <2>origin. \E i, j \in Server:
                  /\ AppendEntries(i, j) /\ m = AppendEntriesMessage(i, j)
        <3>append. CASE \E i, j \in Server: AppendEntries(i, j)
            BY <3>append, <1>new
            DEF AppendEntries, Send, WithMessage, WithMessages
        <3>timeout. CASE \E i \in Server: Timeout(i)
            BY <3>timeout, <1>new, MessageTypesDistinct
            DEF Timeout, WithMessages, RequestVoteRequests
        <3>receive. CASE \E request \in messages: Receive(request)
            BY <3>receive, <1>new, MessageTypesDistinct, SMT
            DEF Receive, UpdateTerm, HandleMsg, HandleRequestVoteRequest,
                HandleRequestVoteResponse, HandleAppendEntriesRequest,
                HandleAppendEntriesResponse, Send, WithMessage, WithMessages
        <3> QED BY <3>append, <3>timeout, <3>receive, <1>new
            DEF Next, vars, Restart, BecomeLeader, ClientRequest,
                AdvanceCommitIndex, LeaderStepDown
    <2> QED BY <2>origin, AppendEntriesMessageTermsMonotonic DEF TermOrderingInv
<1> QED BY <1>old, <1>new

LEMMA TermOrderingInvNext ==
    InductiveInvariant /\ TermOrderingInv /\ [Next]_vars => TermOrderingInv'
    BY LogTermsMonotonicNext, MessageTermsMonotonicNext DEF TermOrderingInv

---------------------------------------------------------------------

THEOREM TermOrderingInvariant == Spec => []TermOrderingInv
    BY TermOrderingInvInit, TermOrderingInvNext, InductiveInvariantInvariant,
       PTL DEF Spec

THEOREM LogTermsMonotonicInvariant == Spec => []LogTermsMonotonic
    BY TermOrderingInvariant, PTL DEF TermOrderingInv

THEOREM MessageTermsMonotonicInvariant == Spec => []MessageTermsMonotonic
    BY TermOrderingInvariant, PTL DEF TermOrderingInv

THEOREM LogTermBoundInvariant == Spec => []LogTermBoundInv
    BY InductiveInvariantInvariant, PTL DEF InductiveInvariant

=====================================================================
