------- MODULE EWD998 -----
\*
 \*
 \*
 \*
 \* complete waste of time.... 
 \* disregard everything here, the assignment was not understand
 \*
 \*
 \*
 \*
 \* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF

EXTENDS Naturals

\*  A constant is a parameter of a specification. In other words, it is a
 \* "variable" that cannot change throughout a behavior, i.e., a sequence
 \* of states. Below, we declares N to be a constant of this spec.
 \* We don't know what value N has or even what its type is; TLA+ is untyped and
 \* everything is a set. In fact, even 23 and "frob" are sets and 23="frob" is 
 \* syntactically correct.  However, we don't know what elements are in the sets 
 \* 23 and "frob" (nor do we care). The value of 23="frob" is undefined, and TLA+
 \* users call this a "silly expression".
CONSTANT N 

\* We should declare what we assume about the parameters of a spec--the constants.
 \* In this spec, we assume constant N to be a (positive) natural number, by
 \* stating that N is in the set of Nat (defined in Naturals.tla) without 0 (zero).
 \* Note that the TLC model-checker, which we will meet later, checks assumptions
 \* upon startup.
NIsPosNat == N \in Nat \ {0}

ASSUME NIsPosNat

\*   ************* RECORD SYNTAX
 \* 
 \*  syntax uses string literals for records
 \* (tla+) [q |-> 42, color |-> "white", pos |-> 0 ]
 \* [q |-> 42, color |-> "white", pos |-> 0]
 \* 
 \* domain is all keys
 \* (tla+) DOMAIN [q |-> 42, color |-> "white", pos |-> 0 ]
 \* {"q", "color", "pos"}
 \* 
 \* access shorthand uses dot notation
 \* (tla+) DOMAIN [q |-> 42, color |-> "white", pos |-> 0 ].pos


\*  0) Sending a message by node i increments a counter at i, the receipt of a
 \*    message decrements i's counter
 \* 3) Receiving a *message* (not token) blackens the (receiver) node
 \* 2) An active node j -owning the token- keeps the token.  When j becomes inactive,
 \*    it passes the token to its neighbor with  q = q + counter[j] 
 \* 4) A black node taints the token
 \* 7) Passing the token whitens the sender node
 \* 1) The initiator sends the token with a counter q initialized to 0 and color
 \*    white
 \* 5) The initiator starts a new round iff the current round is inconclusive
 \* 6) The initiator whitens itself and the token when initiating a new round

Node == 0 .. N - 1 

Colors == { "white", "black" }

VARIABLE 
    active, color, counter,  \* NODES --- all are arrays
    token,                   \* record 
    network                  \* infrastructure

vars == <<active, color, counter, token, network>>

Init ==
    \* network size
    /\ network = [ n \in Node |-> 0..3 ]
    \* initialize token ???
    /\ token.q = 0 
    /\ token.color = "white"
    /\ token.pos = 0
    \* active - T or F
    /\ active \in [ Node -> BOOLEAN ]
    \* color - white or black ??? (what color should nodes have at start)
    /\ color \in [ n \in Node |-> Colors ]
    \* all counters init to 0
    /\ counter = [ n \in Node |-> 0 ] 

\* start the token passing
InitiateToken ==
    \* initialize token ???
    /\ token.pos = 0
    /\ active' = [ active EXCEPT ![0] = FALSE ]    \* active at pos 0 b
    /\ token' = [ token EXCEPT !.q = 0,            \* init q to 0
                               !.color = "white",  \* init to white
                               !.pos = N - 1]      \* position (rotate counterclockwise)

    \* what is wrong with this?
    \* /\ token = [ q |-> 0, color |-> "white", pos |-> 0 ]

SetColor(c) == IF c = "white" THEN "white" ELSE "black"

\* start a new token --- iff last round was inconclusive
PassToken == 
    /\ token.pos # 0
    /\ token' = [ token EXCEPT !.q = token.q + counter[token.pos],   \* add value of counter for Node
                               !.color = SetColor(color[token.pos]), \* color is dependent on color of node
                               !.pos = N - 1]                        \* position (rotate counterclockwise)
    /\ color' = [ color EXCEPT ![token.pos] = "white" ]
    /\ UNCHANGED <<network, active, counter>>

\* TODO
TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]

Terminates(n) ==
    \* /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<network>>

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1 ]
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ token' = [ token EXCEPT !.pos = N - 1 ]

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1 ]
    /\ color' = [ color EXCEPT ![rcv] = "black" ]
    /\ active' = [active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = network[rcv] - 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)

Spec ==
    Init /\ [] [Next]_vars

-------------------

Constraint ==
    \A n \in Node: network[n] < 2

=============================================================================