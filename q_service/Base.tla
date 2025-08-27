---- MODULE Base ----

EXTENDS TLC, Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Services
symmetry == Permutations(Services)

VARIABLES
    \* @type: Str -> Str;
    State,
    \* @type: Str -> { service: Str, owners: Set(Str) };
    Owners,
    \* @type: Str -> { service: Str, deps: Set(Str) };
    Deps
vars == <<State, Owners, Deps>>

DependsOn(a,b) == b \in Deps[a].deps
Owns(a,b) == b \in Owners[a].owners

-------------------------------------------------------------------------------
\* Invariants *\

TypeOK ==
    \A s \in Services :
        /\ State[s] \in {"register", "init", "up", "down"}
        /\ Owners[s].service = s /\ Owners[s].owners \subseteq Services
        /\ Deps[s].service = s /\ Deps[s].deps \subseteq Services

\* while it would be good to add a recursive definition here this will suffice
\* IF we are sure to add _all_ recursive Deps of a to deps[a]
NonCyclicDeps ==
    \A a \in Services, b \in Services :
        /\ b \in Deps[a].deps => a \notin Deps[b].deps

-------------------------------------------------------------------------------
\* Main cycles

Init == /\ State = [ s \in Services |-> "register" ]
        /\ Owners = [ s \in Services |-> [service |-> s, owners |-> {}]]
        /\ Deps = [ s \in Services |-> [service |-> s, deps |-> {}]]

AllReady == \A s \in Services : State[s] /= "register"

------------------------
\* Actions

SpinUp(a) ==
    /\ State[a] = "down"
    /\ State' = [ s \in Services  |->
        IF s = a THEN "init"
        ELSE IF s \in Deps[a].deps THEN
            IF State[s] = "down"
            THEN "init"
            ELSE State[s]
        ELSE State[s]
        ]
    /\ UNCHANGED <<Owners, Deps>>

SpinDown(a) ==
    /\ State[a] = "up"
    /\ State' = [ State EXCEPT ![a] = "down" ]
    /\ UNCHANGED <<Owners, Deps>>

-------------------
\* Conditions

Ownership(a) ==
    /\ State[a] = "up"
    /\  \/  /\ \A b \in Owners[a].owners : State[b] = "down"
            /\ State' = [State EXCEPT ![a] = "down"]
        \/ UNCHANGED State
    /\ UNCHANGED << Owners, Deps >>

FinishInit(a) ==
    /\  State[a] = "init"
    /\  \/  /\ \E b \in Deps[a].deps : State[b] = "down"
            \* NB: Ownership semantics will determine spin-down behavior of owned items
            /\ State' = [State EXCEPT ![a] = "down"]
        \/  /\ \A b \in Deps[a].deps : State[b] = "up"
            /\ State' = [State EXCEPT ![a] = "up"]
        \/ UNCHANGED State
    /\ UNCHANGED << Owners, Deps >>

-------------------------------------------------------------------------------
\* Registration

\* Sim to AddDep
AddOwner(a,b) ==
    /\ Owners' = [
            c \in Services |->
                IF a = c THEN
                    [Owners[c] EXCEPT !.owners = Owners[c].owners \cup {b} ]
                ELSE IF a \in Owners[c].owners THEN
                    [Owners[c] EXCEPT !.owners = Owners[c].owners \cup {b}]
                ELSE
                    Owners[c]
        ]
    /\ UNCHANGED <<Deps, State>>

\* Add dependency t to s and all of its dependent services
\* This ensures that our definiton of NonCyclicDeps holds
AddDep(a, b) ==
    /\ a /= b \* no loops
    /\ ~DependsOn(b,a) \* no cycles
    /\ \A c \in Services : DependsOn(c,a) => ~DependsOn(b,c)
    /\ AddOwner(a,b)
    /\ Deps' = [
            c \in Services |->
                IF a = c THEN
                    [Deps[c] EXCEPT !.deps = Deps[c].deps \cup {b} ]
                ELSE IF a \in Deps[c].deps THEN
                    [Deps[c] EXCEPT !.deps = Deps[c].deps \cup {b}]
                ELSE
                    Deps[c]
        ]
    /\ UNCHANGED State

FinishRegistration(a) ==
    \/  /\  State' = [ State EXCEPT ![a] = "down" ]
        /\  UNCHANGED <<Deps, Owners>>
    \/  /\  State' = [ State EXCEPT ![a] = "init" ]
        /\  Owners' = [ c \in Services |->
                \* Add a to its own owners
                IF a = c THEN
                    [Owners[c] EXCEPT !.owners = Owners[c].owners \cup {a}]
                ELSE
                    Owners[c]
            ]
        /\  UNCHANGED Deps

-------------------------------------------------------------------------------

Next ==
    \* register
    \/ \E a \in Services :
        /\  State[a] = "register"
        /\  \/ \E b \in Services : AddDep(a,b)
            \/ \E b \in Services : AddOwner(a,b)
            \/ FinishRegistration(a)
    \* run
    \/  \/ \E s \in Services :
            /\  \/ SpinUp(s)
                \/ SpinDown(s)
                \/ TRUE \* noop
            /\  \/ Ownership(s)
                \/ FinishInit(s)
    \* terminated - all down
    \/  /\ \A s \in Services : State[s] = "down"
        /\ UNCHANGED <<State, Owners, Deps>>

Spec == Init /\ [][Next]_vars

====
