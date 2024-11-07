--------------- MODULE VectorClocks ---------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT
    P \* the set of processes

N == Cardinality(P)

VectorClock == [P -> Int]

Msg == P \times VectorClock

Event == (P \times {"send", "deliver"} \times Msg) \cup (P \times {"init"})
EventOrdering == SUBSET (Event \times Event)

VARIABLES
    happensBefore \* a ghost variable tracking the happens-before relation
,   clock \* the vector clock
,   sent \* the set of messages sent
,   localEvents

locallyPrecedes(p) == {pair \in happensBefore :
    /\  pair[1] = p
    /\  pair[2] = p}

TypeOK ==
    /\  happensBefore \in EventOrdering
    /\  clock \in [P -> VectorClock]
    /\  sent \in SUBSET Msg
    /\  localEvents \in [P -> SUBSET Event]

zero == [p \in P |-> 0]

Init ==
    /\ happensBefore = {}
    /\ clock = [p \in P |-> zero]
    /\ sent = {}
    /\ localEvents = [p \in P |-> {<<p, "init">>}]

Domain(R) == {r[1] : r \in R}
Image(R) == {r[2] : r \in R}
TransitiveClosure(R) ==
    {r \in Domain(R) \times Image(R) :
        LET x == r[1]
            y == r[2]
        IN  \E z \in Domain(R) : <<x, z>> \in R /\ <<z, y>> \in R}
    \cup R

Max(n1, n2) == IF n1 > n2 THEN n1 ELSE n2
MergeClocks(c1, c2) == [p \in P |-> Max(c1[p], c2[p])]

UpdateLamport(p, newEvent) ==
    /\  localEvents' = [localEvents EXCEPT ![p] = localEvents[p] \cup {newEvent}]
    /\  happensBefore' = TransitiveClosure(happensBefore \cup {<<e, newEvent>> : e \in localEvents[p]})

Deliver(p, m) ==
    /\  m \in sent
    /\  sent' = sent \ {m}
    /\  LET newEvent == <<p, "deliver", m>> IN
        /\  localEvents' = [localEvents EXCEPT ![p] = localEvents[p] \cup {newEvent}]
        /\  happensBefore' = TransitiveClosure(happensBefore
                \cup {<<e, newEvent>> : e \in localEvents[p]}
                \cup {<<<<m[1], "send", m>>, newEvent>>})
    /\  clock' = [clock EXCEPT ![p] = MergeClocks(clock[p], m[2])]

Send(p) ==
    /\  clock' = [clock EXCEPT ![p] = [@ EXCEPT ![p] = @ + 1]]
    /\  LET m == <<p, clock'[p]>> IN
        /\  sent' = sent \cup {m}
        /\  LET newEvent == <<p, "send", m>> IN
            /\  localEvents' = [localEvents EXCEPT ![p] = localEvents[p] \cup {newEvent}]
            /\  happensBefore' = TransitiveClosure(happensBefore \cup {<<e, newEvent>> : e \in localEvents[p]})

Next == \E p \in P : 
    \/  Send(p) 
    \/  \E m \in Msg : Deliver(p, m)

vars == <<happensBefore, clock, sent, localEvents>>
Spec == Init /\ [][Next]_vars

Canary == \neg (
    \E p \in P, q \in P : p # q /\ clock[p][q] > 0
)
    





















=============================================================================