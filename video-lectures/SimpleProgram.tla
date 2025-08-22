--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == /\ pc = "start"
        /\ i' \in 0..1000
        /\ pc' = "middle"

Add1 == /\ pc = "middle"
        /\ i' = i + 1
        /\ pc' = "done"

Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Wed Aug 20 23:36:51 CDT 2025 by ada
\* Created Wed Aug 20 22:43:22 CDT 2025 by ada
