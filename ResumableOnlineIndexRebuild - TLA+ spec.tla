------------------------------ MODULE ResumableOIBSpec ------------------------------

EXTENDS Integers, Sequences

(* The spec models an online index build operation in the presence
   of concurrent DML. It verifies that the old and new rowsets are
   maintained correctly, and that they contain the same data after
   the build completes.
   The old and new index are represented by sequences.
   The model limits the number of concurrent DML operations,
   to ensure that the number of state transitions is finite,
   and the model eventually finishes and performs the verification.
   The deadlock check should be disabled during the execution. *)

CONSTANT Data, InitialRows, TotalDmlCount

(* IndOld - sequence representing the old index
   IndNew - sequence representing the new index
   BuildPos - current position of the builder in the old index
   BuilderCurrentRow - buffer used by the builder to store a row
                       read from the old index, to be inserted
                       into the new index
   NextKey - next key value to be used for rows inserted by
             concurrent DML
   DmlCount - number of concurrent DML perations executed so far *)
VARIABLES IndOld, IndNew, BuildPos, BuilderCurrentRow, NextKey, DmlCount

(* Helper functions to simplify operations on sequences *)
InsertSeq(pos, val, seq) == [i \in 1..(Len(seq)+1) |-> IF i<pos THEN seq[i] ELSE (IF i = pos THEN val ELSE seq[i-1])]
RemoveSeq(j, seq) == [i \in 1..(Len(seq)-1) |-> IF i<j THEN seq[i] ELSE seq[i+1]]

RECURSIVE RemoveKey(_,_)
RemoveKey(key, seq) == IF Len(seq) = 0 THEN <<>> ELSE IF Head(seq)[1]=key THEN Tail(seq) ELSE (<<Head(seq)>> \o RemoveKey(key, Tail(seq)))

(* Model initialization. The old indes is created with the requested
   number of initial rows. *)
Init == BuildPos = 1 
    /\ IndNew = <<>> 
    /\ IndOld= [row \in 1..InitialRows |-> <<row, 1, 0>>] 
    /\ BuilderCurrentRow = <<>>
    /\ NextKey = InitialRows + 1
    /\ DmlCount = 0

(* This action represents the index builder reading a row
   from the old index into its buffer. *)
BuilderReadRow == 
    BuildPos <= Len(IndOld)
    /\ Len(BuilderCurrentRow) = 0
    /\ BuildPos' = BuildPos + 1
    /\ BuilderCurrentRow' = <<IndOld[BuildPos]>>
    /\ UNCHANGED <<IndOld, IndNew, NextKey, DmlCount>>

(* This action represents the index builder inserting a row
   from its buffer into the target index. It is decoupled
   from BuilderReadRow, to allow concurrent actions between
   the read and the write.
   If the row already exists in the new index, the builder
   takes no action. *)
BuilderInsertRow == 
    Len(BuilderCurrentRow) > 0
    /\ (IndNew' = IF (\E r \in 1..Len(IndNew) : IndNew[r][1]=BuilderCurrentRow[1][1]) THEN  IndNew ELSE (IndNew \o BuilderCurrentRow))
    /\ BuilderCurrentRow' = <<>>
    /\ UNCHANGED <<IndOld, NextKey, DmlCount, BuildPos>>

(* This action represents concurrent DML inserting a row
   into the old and new index. If the row is inserted
   before the current position of the index builder,
   the builder's position needs to be adjusted. *)
InsertRow == DmlCount <= TotalDmlCount
    /\ (\E r \in 1..(Len(IndOld)+1) : 
        /\ IndOld' = InsertSeq(r, <<NextKey, 42, 0>>, IndOld) 
        /\ IndNew' = IndNew \o <<<<NextKey, 42,0 >>>>
        /\ IF r <= BuildPos THEN BuildPos' = BuildPos + 1 ELSE BuildPos' = BuildPos) 
    /\ NextKey'= NextKey + 1
    /\ DmlCount' = DmlCount + 1
    /\ UNCHANGED <<BuilderCurrentRow>>
    
(* This action represents concurrent DML deleting a row
   from the old and new index. When maintaining the new index,
   the delete must insert an antimatter row regardless of whether
   the deleted row was found or not. *)
DeleteRow == DmlCount <= TotalDmlCount
    /\ (\E r \in 1..Len(IndOld) : 
        /\ IndOld' = RemoveSeq(r, IndOld)
        /\ IndNew' = IF (\E rNew \in 1..Len(IndNew) : IndNew[rNew][1]=IndOld[r][1]) THEN RemoveKey(IndOld[r][1], IndNew) \o <<<<IndOld[r][1], IndOld[r][2], 1>>>> ELSE IndNew \o <<<<IndOld[r][1], IndOld[r][2], 1>>>> 
        /\ IF r < BuildPos THEN BuildPos' = BuildPos - 1 ELSE BuildPos' = BuildPos)
    /\ DmlCount' = DmlCount + 1
    /\ UNCHANGED <<BuilderCurrentRow, NextKey>>
    
Next == BuilderReadRow \/ BuilderInsertRow \/ InsertRow \/ DeleteRow

(* The end check validates that the contents of the old and new index
   are the same, minus any remaining antimatter in the new index. *)
EndCheck == 
    BuildPos <= Len(IndOld) \/ Len(BuilderCurrentRow) # 0 \/ (\*Len(IndNew) = Len(IndOld) 
    /\ (\A rOld \in 1..Len(IndOld) : \E rNew \in 1..Len(IndNew) : IndOld[rOld]=IndNew[rNew])
    /\ (\A rNew \in 1..Len(IndNew) : IndNew[rNew][3]=1 \/ \E rOld \in 1..Len(IndOld) : IndOld[rOld]=IndNew[rNew])
    /\ ~(\E r1 \in 1..Len(IndOld), r2 \in 1..Len(IndOld) : r1 # r2 /\ IndOld[r1][1] = IndOld[r2][1])
    /\ ~(\E r1 \in 1..Len(IndNew), r2 \in 1..Len(IndNew) : r1 # r2 /\ IndNew[r1][1] = IndNew[r2][1]))
    
Check == Len(IndNew) < Len(IndOld) 
    \/ \E r \in 1..InitialRows : IndOld[r][1] # IndNew[r][1] \/ IndOld[r][2] # IndNew[r][2]
    
=============================================================================
\* Modification History
\* Last modified Mon Apr 11 12:19:43 PDT 2016 by krmularc
\* Last modified Thu Apr 07 14:04:31 PDT 2016 by panant
\* Created Thu Apr 07 10:07:19 PDT 2016 by panant
