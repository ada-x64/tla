---- MODULE Base ----

EXTENDS TLC, Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Services 
symmetry == Permutations(Services)

(*
    Deps and Owners have the following structure:
    Owners[i] = [service: i, owners: {o_1, o_2, ... o_j}] where o_k are owning services of i.
    Deps[i] = [service: i, owners: {d_1, d_2, ..., d_j}] where d_k are deps of i.
*)
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
        /\ State[s] \in {"register", "init", "up", "deinit", "down"}
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

InitService(a) ==
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

DeinitService(s) ==
    /\ State[s] \in {"up", "init"}
    /\ State' = [State EXCEPT ![s] = "deinit"]
    /\ UNCHANGED <<Owners, Deps>>

-------------------
\* Conditions

Ownership(a) ==
    /\  \/  /\ \A b \in Owners[a].owners : State[b] = "down"
            /\ State' = [State EXCEPT ![a] = "down"]
        \/  /\ \A b \in Owners[a].owners : (State[b] = "down" \/ State[b] = "deinit")
            /\ State' = [State EXCEPT ![a] = "deinit"]
        \/ UNCHANGED State
    /\ UNCHANGED << Owners, Deps >>

FinishInit(a) ==
    /\  State[a] = "init"
        \* case 1: fail to init
    /\  \/  /\ \E b \in Deps[a].deps : (State[b] = "down" \/ State[b] = "deinit")
            /\ State' = [State EXCEPT ![a] = "down"] \* NB: Ownership semantics will determine spin-down behavior.
        \* case 2: successful init
        \/  /\ \A b \in Deps[a].deps : State[b] = "up"
            /\ State' = [State EXCEPT ![a] = "up"] 
        \* case 3: still initializing
        \/  UNCHANGED State
    /\ UNCHANGED << Owners, Deps >>

FinishDeinit(a) ==
    /\  State[a] = "init"
        \/  /\ \A b \in Deps[a].deps : State[b] = "down"
            /\ State' = [State EXCEPT ![a] = "down"] 
        \/  UNCHANGED State
    /\ UNCHANGED << Owners, Deps >>

-------------------------------------------------------------------------------
\* Registration

\* Add dependency t to s and all of its dependent services
\* This ensures that our definiton of NonCyclicDeps holds
\* NOTE: Subformula so do not add UNCHANGED
AddDep(a, b) ==
    /\ a /= b \* no loops
    /\ ~DependsOn(b,a) \* no cycles
    /\ \A c \in Services : DependsOn(c,a) => ~DependsOn(b,c)
    /\ Deps' = [
            c \in Services |-> 
                IF a = c THEN 
                    [Deps[c] EXCEPT !.deps = Deps[c].deps \cup {b} ]
                ELSE IF a \in Deps[c].deps THEN 
                    [Deps[c] EXCEPT !.deps = Deps[c].deps \cup {b}]
                ELSE
                    Deps[c]
        ]

\* Sim to AddDep
AddOwner(a,b) ==
    Owners' = [
            c \in Services |-> 
                IF a = c THEN 
                    [Owners[c] EXCEPT !.owners = Owners[c].owners \cup {b} ]
                ELSE IF a \in Owners[c].owners THEN 
                    [Owners[c] EXCEPT !.owners = Owners[c].owners \cup {b}]
                ELSE
                    Owners[c]
        ]


RegisterService(s) == 
    /\ State[s] = "register"
    /\  \/ State' = [ State EXCEPT ![s] = "down" ]
        \/ State' = [ State EXCEPT ![s] = "init" ]
        \/ UNCHANGED State \* add more owners and deps on next step
    /\  \/ UNCHANGED Deps
        \/ \E t \in Services : AddDep( s,t )
    /\  \/ UNCHANGED Owners
        \/ \E t \in Services : AddOwner( s,t )
-------------------------------------------------------------------------------

Next ==
    \* perform actions
    \/  /\ ~AllReady
        /\ \A s \in Services : RegisterService(s)
    \/  /\ AllReady
        /\ \E s \in Services :
            \/ InitService(s)
            \/ DeinitService(s)
        /\ \A s \in Services :
            /\ Ownership(s)
            /\ FinishInit(s)
            /\ FinishDeinit(s)

Spec == Init /\ [][Next]_vars

====