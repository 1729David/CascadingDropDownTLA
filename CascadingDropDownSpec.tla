------------------------------- MODULE CascadingDropDownSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS DDL,                  \* The tuple of all the drop downs
          Available,            \* The tuple with the set of values available for each drop down
          None                  \* The value assigned to an unselected drop down

VARIABLES Enabled,              \* The set of enabled drop downs
          Selected              \* The tuple of selected values 

ASSUME \A a \in 1..Len(Available) : None \notin Available[a]
    (***********************************************************************)
    (* The None value is assumed to not be any of the available values     *)
    (* for any of the drop downs.                                          *)
    (***********************************************************************)

--------------------------------------------------------------------------------------------

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
CDDTypeOK == /\ Enabled \in SUBSET { k : k \in 1..Len(DDL) }

(***************************************************************************)
(* The intial predicate                                                    *)
(***************************************************************************)
CDDInit == /\ Enabled = { 1 }
           /\ Selected = [ k \in 1..Len(DDL) |-> None ]

(***************************************************************************)
(* Define the actions that may be perfomed with the cascading drop down.   *)
(* Then define the next state as the disjuction of these actions.          *)
(***************************************************************************)
Select(a) == 
  /\ a \in Enabled
  /\ Enabled' = { k \in 1..Len(DDL) : k <= (a + 1) /\ k <= Len(DDL) }
  /\ Selected' = [k \in 1..Len(DDL) |-> 
        IF k < a 
        THEN Selected[k] 
        ELSE 
            IF k = a
            THEN CHOOSE x \in Available[a] : x \notin {Selected[i] : i \in 1..(a-1)}
            ELSE None]

Unselect(a) == 
  /\ a \in Enabled
  /\ Enabled' = { k \in Enabled : k <= a }
  /\ Selected' = [k \in 1..Len(DDL) |-> IF k < a THEN Selected[k] ELSE None]

CDDNext == \E a \in 1..Len(DDL) : Select(a) \/ Unselect(a)

(***************************************************************************)
(* Invariance properties of the specification:                             *)
(*  - The first drop down is always enabled AND                            *)
(*  - Only the last enabled drop down can be not selected AND              *)
(*  - Every drop down that is selected is also enabled AND                 *)
(*  - There are no repeated selected values                                *)
(***************************************************************************)
CDDConsistent == 
  /\ 1 \in Enabled 
  /\ LET EnabledMinusSelected == Enabled \ {x \in 1..Len(DDL) : Selected[x] # None}
         LastEnabled == { CHOOSE y \in Enabled : (\A z \in Enabled : y >= z) }
     IN EnabledMinusSelected = LastEnabled \/ EnabledMinusSelected = {}
  /\ {x \in 1..Len(DDL) : Selected[x] # None} \ Enabled = {}
  /\ Cardinality({x \in 1..Len(DDL) : Selected[x] # None}) = 
        Cardinality({Selected[x] : x \in 1..Len(DDL)} \ {None})
  
(***************************************************************************)
(* Complete cascading drop down spec                                       *)
(***************************************************************************)
CDDSpec == CDDInit /\ [][CDDNext]_<<Enabled, Selected>>

=============================================================================
\* Modification History
\* Last modified Thu Jan 03 16:59:01 PST 2019 by david
\* Last modified Wed Jan 02 16:28:49 PST 2019 by algorist
\* Created Fri Dec 21 21:49:25 PST 2018 by algorist
