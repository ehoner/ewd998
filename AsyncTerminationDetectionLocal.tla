TODO: add counters, token, color
---------------------- MODULE AsyncTerminationDetection ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals

\* * A constant is a parameter of a specification. In other words, it is a
 \* * "variable" that cannot change throughout a behavior, i.e., a sequence
 \* * of states. Below, we declares N to be a constant of this spec.
 \* * We don't know what value N has or even what its type is; TLA+ is untyped and
 \* * everything is a set. In fact, even 23 and "frob" are sets and 23="frob" is 
 \* * syntactically correct.  However, we don't know what elements are in the sets 
 \* * 23 and "frob" (nor do we care). The value of 23="frob" is undefined, and TLA+
 \* * users call this a "silly expression".
CONSTANT N

\* * We should declare what we assume about the parameters of a spec--the constants.
 \* * In this spec, we assume constant N to be a (positive) natural number, by
 \* * stating that N is in the set of Nat (defined in Naturals.tla) without 0 (zero).
 \* * Note that the TLC model-checker, which we will meet later, checks assumptions
 \* * upon startup.
ASSUME NIsPosNat == N \in Nat \ {0}

\* TODO Fire up the TLA+ repl (`tlcrepl` in the Terminal > New Terminal) and 
 \* TODO find out what TLC returns for the following expressions:
 \* TODO 23 = "frob"
 \* TODO 23 # "frob"                       \* # is pretty-printed as ≠
 \* TODO {1,2,2,3,3} = {3,1,1,2,3,1}
 \* TODO 1 \div 4
 \* TODO 1 \div 0
 \* TODO {1,2,3} \cap {2,3,4}              \* \cap pp'ed as ∩
 \* TODO {1,2,3} \cup {2,3,4}              \* \cap pp'ed as ∪
 \* TODO {1,2,3} \ {2,3,4}
 \* TODO 23 \in {0}                        \* \in pp'ed as ∈
 \* TODO 23 \in {23, "frob"}
 \* TODO 23 \in {"frob", 23}
 \* TODO 23 \in {23} \ 23
 \* TODO 23 \in {23} \ {23}
 \* TODO 23 \notin {23} \ {23}
 \* TODO 10 \in 1..10
 \* TODO 1 \in 1..0

Node == 0 .. N - 1

VARIABLE active, network, terminatationDetected
vars == <<active, network, terminatationDetected>>

TypeOK ==
    \* shorthand to express the two stmts below
    /\ network \in [ Node -> Nat ]
    \* /\ \A n \in Node: network[n] > 0
    \* /\ DOMAIN network = Node
    /\ active \in [ Node -> BOOLEAN ]
    /\ terminatationDetected \in BOOLEAN


\* repl: [0 .. 2 -> {"a", "b"}]
\* repl: Cardinality([ 0..2 -> {"a", "b"} ])


terminated ==
    \A n \in Node: active[n] = FALSE /\ network[n] = 0

\* Intialization 
Init == 
    \* /\ active = [ n \in Node |-> TRUE ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ n \in Node |-> 0..3 ]
    /\ terminatationDetected \in {FALSE, terminated}

\* Idles
Terminates(n) == 
   /\ active[n] = TRUE 
   \* syntax sugar (shortcut for below)
   /\ active' = [ active EXCEPT ![n] = FALSE ]
   \* /\ active' = [ m \in Node |-> IF m = n THEN FALSE ELSE active[m] ]
   /\ network' = network
   /\ \* \/ terminatationDetected' = TRUE \* violation
      \* \/ terminatationDetected' = terminated'
      \/ terminatationDetected' \in {terminatationDetected, terminated'}

\* increment counter
SendMsg(snd, rcv) == 
    /\ UNCHANGED active
    /\ active[snd] = TRUE
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ UNCHANGED terminatationDetected

\* decrement counter
RecvMsg(rcv) == 
    /\ network[rcv] > 0
    \* non-sugar equivalents below
    /\ active' = [ active EXCEPT ![rcv] = TRUE ]
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    \* /\ active' = [ m \in Node |-> IF m = rcv THEN TRUE ELSE active[m] ]
    \* /\ network' = [ m \in Node |-> IF m = rcv THEN network[rcv] - 1 ELSE network[m] ]
    /\ UNCHANGED terminatationDetected

Next == 
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)

Spec == Init /\ [][Next]_vars

-----------------

\* [A]_v  <=>  A \/ UNCHANGED v
\* []<=> "always"
NeverUndetected == 
    [][terminatationDetected => terminatationDetected']_vars

\* something bad never happens
Safe == 
    \* IF terminatationDetected THEN terminated ELSE TRUE 
    \* without [] + () will only check initial state
    [](terminatationDetected => terminated)

\* something good will eventually occur
Live == 
    \* requires fairness constraint
    [](terminated => <>terminatationDetected)  

THEOREM Spec => Safe /\ NeverUndetected /\ Live

Constraint ==
    \A n \in Node: network[n] < 2

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl