------------------------------- MODULE CascadingDropDownSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS DDL, Available, None

VARIABLES Enabled, Selected

ASSUME \A a \in 1..Len(Available) : None \notin Available[a]

Init == /\ Enabled = { 1 }
        /\ Selected = [ k \in 1..Len(DDL) |-> None ]

Select(a) == /\ a \in Enabled
             /\ Enabled' = { k \in 1..Len(DDL) : k <= (a + 1) /\ k <= Len(DDL) }
             /\ Selected' = [k \in 1..Len(DDL) |-> IF k < a 
                                                    THEN Selected[k] 
                                                    ELSE 
                                                        IF k = a
                                                        THEN CHOOSE x \in Available[a] : x \notin {Selected[i] : i \in 1..(a-1)}
                                                        ELSE None]

Unselect(a) == /\ a \in Enabled
               /\ Enabled' = { k \in Enabled : k <= a }
               /\ Selected' = [k \in 1..Len(DDL) |-> IF k < a THEN Selected[k] ELSE None]

Next == \E a \in 1..Len(DDL) : Select(a) \/ Unselect(a)

Consistent == 
          /\ 1 \in Enabled \* first one always enabled
          \* only the last enabled can be not selected
          /\ LET EnabledMinusSelected == Enabled \ {x \in 1..Len(DDL) : Selected[x] # None}
                 LastEnabled == { CHOOSE y \in Enabled : (\A z \in Enabled : y >= z) }
             IN EnabledMinusSelected = LastEnabled \/ EnabledMinusSelected = {}
          /\ {x \in 1..Len(DDL) : Selected[x] # None} \ Enabled = {} \* Everyone selected is enabled
          /\ Cardinality({x \in 1..Len(DDL) : Selected[x] # None}) = Cardinality({Selected[x] : x \in 1..Len(DDL)} \ {None}) \* unique values
          

=============================================================================
\* Modification History
\* Last modified Wed Jan 02 22:23:11 PST 2019 by david
\* Last modified Wed Jan 02 16:28:49 PST 2019 by algorist
\* Created Fri Dec 21 21:49:25 PST 2018 by algorist
