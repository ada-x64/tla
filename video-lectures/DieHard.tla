---- MODULE DieHard ----

EXTENDS     TLC, Integers

VARIABLES   small, big
vars        == <<small, big>>

\* invariants *\
TypeOK      ==  /\ small \in 0..3
                /\ big \in 0..5

Condition   ==  big /= 4

\* initialize *\
Init        ==  /\ small = 0
                /\ big = 0

\* main formulae *\
FillSmall   ==  /\ small' = 3
                /\ big' = big

FillBig     ==  /\ big' = 5
                /\ small' = small

EmptySmall  ==  /\ small' = 0
                /\ big' = big

EmptyBig    ==  /\ big' = 0
                /\ small' = small

SmallToBig  ==  IF big + small <= 5
                THEN    /\ big' = big + small
                        /\ small' = 0
                ELSE    /\ big' = small
                        /\ small' = small - (5 - big)

BigToSmall  ==  IF big + small <= 3
                THEN    /\ big' = 0
                        /\ small' = big + small
                ELSE    /\ big' = small - ( 3 - big )
                        /\ small' = 3


\* NEXT *\
Next        ==  \/ FillSmall
                \/ FillBig
                \/ EmptySmall
                \/ EmptyBig
                \/ SmallToBig
                \/ BigToSmall

Spec        == Init /\ [][Next]_vars

====

\* Modification History
\* Last modified Wed Aug 20 23:36:51 CDT 2025 by ada
\* Created Wed Aug 20 22:43:22 CDT 2025 by ada
