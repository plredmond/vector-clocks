---------- MODULE Utils ----------

EXTENDS Integers

Max(n1, n2) == IF n1 > n2 THEN n1 ELSE n2

(*************************)
(* Stuff about relations *)
(*************************)

Domain(R) == {r[1] : r \in R}

Image(R) == {r[2] : r \in R}

TransitiveClosure(R) == R \cup
    {r \in Domain(R) \times Image(R) :
        \E z \in Domain(R) : <<r[1], z>> \in R /\ <<z, r[2]>> \in R}

============================