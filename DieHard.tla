------------------------------- MODULE DieHard ------------------------------
\*  action       | small | large
 \* -------------|-------|--------
 \* fill 3       | 3 = 3 | 5 = 0
 \* pour 3 to 5  | 3 = 0 | 5 = 3
 \* fill 3       | 3 = 3 | 5 = 3
 \* pour 3 to 5  | 3 = 1 | 5 = 5
 \* empty 5      | 3 = 1 | 5 = 0 
 \* pour 3 to 5  | 3 = 0 | 5 = 1
 \* fill 3       | 3 = 3 | 5 = 1
 \* pour 3 to 5  | 3 = 0 | 5 = 4

EXTENDS Naturals

VARIABLES jug3, jug5

Not4 == jug5 # 4

Fill3 == 
    /\ jug3 < 3
    /\ jug3' = 3
    /\ UNCHANGED jug5

Fill5 ==
    /\ jug5 < 5
    /\ jug5' = 5
    /\ UNCHANGED jug3

Empty3 == 
    /\ jug3 > 0
    /\ jug3' = 0
    /\ UNCHANGED jug5

Empty5 ==
    /\ jug5 > 5
    /\ jug5' = 0
    /\ UNCHANGED jug3

PourFrom3 ==
    /\ jug3 = 0
    /\ jug5 < 5
    /\ jug5' = IF jug5 + jug3 <= 5 THEN jug5 + jug3 ELSE 5
    /\ jug3' = IF jug5 + jug3 <= 5 THEN 0 ELSE jug3 - (5 - jug5)

PourFrom5 == 
    /\ jug5 > 0
    /\ jug3 < 3
    /\ jug3' = IF (jug5 + jug3) >= 3 THEN 3 ELSE jug5 + jug3
    /\ jug5' = jug5 - jug3

Init == 
    /\ jug3 = 0
    /\ jug5 = 0

Next ==
    \/ Fill3
    \/ Fill5
    \/ Empty3
    \/ Empty5
    \/ PourFrom3
    \/ PourFrom5

Spec == Init /\ [][Next]_<<jug5, jug3>> 

=============================================================================