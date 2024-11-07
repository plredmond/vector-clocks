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
StepClock(p, vc) == [vc EXCEPT ![p] = @ + 1]
DeliverableAt(m, p) ==
    \A k \in P :
        /\ k = m[1] => m[2][k] = clock[p][k] + 1
        /\ k # m[1] => m[2][k] = clock[p][k]
\*        IF k = m[1] THEN m[2][k] = clock[p][k] + 1
\*                    ELSE m[2][k] = clock[p][k]

SendEvent(m) == <<m[1], "send", m>>
DeliveryEvent(p, m) == <<p, "deliver", m>>

Deliver(p, m) ==
    /\  m \in sent
    /\ DeliverableAt(m, p)
    /\  LET d == DeliveryEvent(p, m)
           s == SendEvent(m)
        IN
        /\  d \notin localEvents[p]
        /\  localEvents' = [localEvents EXCEPT ![p] = @ \cup {d}]
        /\  happensBefore' = TransitiveClosure({<<s, d>>} \cup {<<e, d>> : e \in localEvents[p]} \cup happensBefore)
    /\  clock' = [clock EXCEPT ![p] = MergeClocks(@, m[2])]
    /\ UNCHANGED <<sent>>

Send(p) ==
    /\  clock' = [clock EXCEPT ![p] = StepClock(p, @)]
    /\  LET m == <<p, clock'[p]>>
           s == SendEvent(m)
        IN
        /\  sent' = sent \cup {m}
        /\  localEvents' = [localEvents EXCEPT ![p] = @ \cup {s}]
        /\  happensBefore' = TransitiveClosure({<<e, s>> : e \in localEvents[p]} \cup happensBefore)

Next == \E p \in P :
    \/  Send(p) 
    \/  \E m \in Msg : Deliver(p, m)

vars == <<happensBefore, clock, sent, localEvents>>
Spec == Init /\ [][Next]_vars

CausalDelivery ==
    \A p \in P, m1 \in Msg, m2 \in Msg:
        /\ DeliveryEvent(p, m1) \in localEvents[p]
        /\ DeliveryEvent(p, m2) \in localEvents[p]
        => (
            <<SendEvent(m1), SendEvent(m2)>> \in happensBefore
            =>
            <<DeliveryEvent(p, m1), DeliveryEvent(p, m2)>> \in happensBefore
        )

Canary == \neg (
    \E p \in P, q \in P : p # q /\ clock[p][q] > 0
)
    





















=============================================================================
