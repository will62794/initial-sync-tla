--------------------------------------- MODULE InitSyncDocs ---------------------------------------
\*
\* Initial syncing a single MongoDB collection.
\*

EXTENDS Sequences, Naturals, Integers, FiniteSets

\* The set of all possible documents and all possible keys (i.e. fields).
CONSTANT Document, Key

\* An empty value.
CONSTANT Nil

\* Value representing an exhausted cursor.
CONSTANT EOF

\* The log of operations that occur on the sync source.
VARIABLE oplog 

\* The state of the sync source collection.
VARIABLE remoteColl

\* A sequence containing the current documents in the remote collection
\* in the order that a cursor will traverse them.
VARIABLE remoteCollSeq

\* The position of the cursor in the remote collection.
VARIABLE cursor

\* The state of the local collection.
VARIABLE localColl

\* A boolean flag that determines whether the initial sync is in progress. The sync begins when 
\* the receiver starts fetching log entries, and completes when it stops fetching entries.
VARIABLE syncing

vars == <<oplog, remoteColl, remoteCollSeq, cursor, localColl, syncing>>
    
Range(f) == {f[i] : i \in DOMAIN f}  

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Delete an element from a sequence at a specified index.
DeleteElement(seq, index) == [i \in 1..(Len(seq)-1) |-> IF i<index THEN seq[i] ELSE seq[(i+1)]] 


(**************************************************************************************************)
(* MongoDB Collection Scan Semantics                                                              *)
(*                                                                                                *)
(* In the WiredTiger storage engine, collection scans are guaranteed to return documents in their *)
(* 'RecordId' order.  This should correspond to the insertion order of the documents.  Thus, in a *)
(* collection scan, newly inserted documents should get put at the "end" of the scan.  Updated    *)
(* documents will stay in place.  In MMAPv1, however, the internal organization of                *)
(* documents/records leads to different behavior.  A collection scan in MMAP does not follow the  *)
(* RecordId ordering, and a document insert may get placed at some arbitrary point in the scan    *)
(* order.  Similarly, an updated document may be "moved" in MMAP, in which case it can also be    *)
(* placed at some new, arbitrary point in the scan.  We encode these semantics into the operation *)
(* behaviors below.  For now, we only specify this in update operations, since we believe that is *)
(* sufficient to illustrate the behavior difference.                                              *)
(**************************************************************************************************)

\* The sync source performs an insert. (ACTION)
Insert(d) == 
    \* Cannot have duplicate documents.
    /\ remoteColl[d] = Nil
    \* Insert the initial document.
    /\ remoteColl' = [remoteColl EXCEPT ![d] = [k \in Key |-> 0]]
    \* Append documents to the end of the sequence.
    /\ remoteCollSeq' = Append(remoteCollSeq, d)
    /\ oplog' = Append(oplog, <<"i", d, Nil, [k \in Key |-> 0]>>)
    /\ UNCHANGED <<localColl, cursor, syncing>>

\* The sync source performs an update. (ACTION)
MMAPUpdate(d, k) == 
    \* The document must exist. 
    /\ remoteColl[d] # Nil
    \* The key in the doc may or may not exist already. Bump its version if it does.
    /\ LET newVersion == IF remoteColl[d][k] = Nil THEN 0 ELSE remoteColl[d][k] + 1 IN
        /\ remoteColl' = [remoteColl EXCEPT ![d] = [remoteColl[d] EXCEPT ![k] = newVersion]]
        /\ oplog' = Append(oplog, <<"u", d, k, newVersion>>)
        
    (* MMAPv1 Specific Semantics *)
    \* The document may be moved to some new, arbitrary position in the scan order. To make this spec
    \* easier to write, we assume for now that the doc is moved to the beginning of the sequence.
    \* If cursor is already EOF, there's no need to adjust its position.
    /\ LET ind == CHOOSE i \in DOMAIN remoteCollSeq : remoteCollSeq[i] = d IN
       (\/ /\ remoteCollSeq' = <<d>> \o DeleteElement(remoteCollSeq, ind) \* move to beginning.
           \* If the cursor is EOF or the document was already the first in the sequence, 
           \* do not adjust the cursor.
           /\ cursor' = IF (cursor = EOF \/ ind = 1) THEN cursor ELSE cursor + 1)
    /\ UNCHANGED <<localColl, syncing>>   

\* The sync source performs an update. (ACTION)
WTUpdate(d, k) == 
    \* The document must exist. 
    /\ remoteColl[d] # Nil
    \* The key in the doc may or may not exist already. Bump its version if it does.
    /\ LET newVersion == IF remoteColl[d][k] = Nil THEN 0 ELSE remoteColl[d][k] + 1 IN
        /\ remoteColl' = [remoteColl EXCEPT ![d] = [remoteColl[d] EXCEPT ![k] = newVersion]]
        /\ oplog' = Append(oplog, <<"u", d, k, newVersion>>)
        
    (* WiredTiger Specific Semantics *)
    \* Document is not moved and cursor position is unaffected.
    /\ UNCHANGED <<remoteCollSeq, cursor>>
    /\ UNCHANGED <<localColl, syncing>>       

\* Expression that represents whether the data clone is complete. If the cursor has moved past the end of the 
\* remote collection sequence, then it should moved transitioned to the EOF state.
CloneComplete == (cursor = EOF)

\* The syncing node fetches one new document from the sync source and advances the cursor. (ACTION)
FetchDoc == 
    \* Make sure the cursor is not exhausted.
    /\ ~CloneComplete 
    /\ cursor <= Len(remoteCollSeq)
    /\ LET d == remoteCollSeq[cursor] IN
        \* The document is fetched at its current version.
        /\ localColl' = [localColl EXCEPT ![d] = remoteColl[d]]
        \* Advance the cursor. We use a special 'EOF' value to indicate that the cursor has ran past the 
        \* end of the collection, so that it cannot retrieve any more documents.
        /\ cursor' = IF (cursor + 1) > Len(remoteCollSeq) THEN EOF ELSE (cursor + 1)
        /\ UNCHANGED <<remoteColl, remoteCollSeq, oplog, syncing>>
    
\* Finish the sync. This can happen any time after the data clone is completed. (ACTION) 
\*
\* In this spec, this means the sync source will stop executing new operations. In the real
\* system this would mean we stop fetching oplog entries from the source.   
FinishSync == 
    /\ CloneComplete /\ syncing = TRUE
    /\ syncing' = FALSE
    /\ UNCHANGED <<oplog, remoteColl, remoteCollSeq, cursor, localColl>>

\* Once the collection clone and oplog fetching has completed, apply an operation on the receiver. We remove
\* ops from the oplog as we apply them. (ACTION)
ApplyOp == 
    /\ syncing = FALSE
    /\ Len(oplog) > 0 \* we must have ops left to apply.
    /\ LET op == Head(oplog)[1]
           d  == Head(oplog)[2] 
           k  == Head(oplog)[3] 
           v  == Head(oplog)[4] IN
           \* insert.
           IF      op = "i" THEN localColl' = [localColl EXCEPT ![d] = v]
           \* update.
           ELSE IF op = "u" THEN localColl' = 
                [localColl EXCEPT ![d] = 
                    IF localColl[d] = Nil 
                    \* The document doesn't exist locally. Create it with the single key value. (i.e. an "upsert").
                    THEN [ik \in Key |-> IF ik = k THEN v ELSE Nil] 
                    \* The document exists locally and we update the key. 
                    ELSE [localColl[d] EXCEPT ![k] = v]]            
           \* delete.
           \* ELSE IF op = "d" THEN localColl' = [localColl EXCEPT ![d] = v]
           ELSE UNCHANGED <<localColl>>
    /\ oplog' = Tail(oplog)
    /\ UNCHANGED <<remoteColl, remoteCollSeq, cursor, syncing>>


\* Define the initial/next states.

Init == 
    /\ oplog = <<>>
    \* A collection is a map from document ids to the values of those documents. Document non-existence is 
    \* represented by a document mapping to 'Nil'. If a document exists, its value is itself a mapping from
    \* keys to their version numbers.
    /\ \E c \in [Document -> {Nil} \cup [Key -> {0, Nil}]]:
        /\ remoteColl = c
        \* Place each existing document at some place in the scan order.
        /\ LET docs == {d \in DOMAIN c : c[d] # Nil} IN
            /\ remoteCollSeq \in [1..Cardinality(docs) -> docs]
            /\ Injective(remoteCollSeq)
    /\ cursor = 1
    /\ localColl = [d \in Document |-> Nil]
    \* We start off with the sync in-progress, which means that operations may occur on the sync source and we can 
    \* clone documents.
    /\ syncing = TRUE

\* Only execute ops while the sync is ongoing.
InsertAction == \E d \in Document: syncing /\ Insert(d)
MMAPUpdateAction == \E d \in Document: \E k \in Key : syncing /\ MMAPUpdate(d, k)
WTUpdateAction == \E d \in Document: \E k \in Key : syncing /\ WTUpdate(d, k)

Next == 
    \* A remote op occurs.
    \/ InsertAction
    \* Can choose the collection scan semantics.
    \/ MMAPUpdateAction
\*    \/ WTUpdateAction
    \/ FetchDoc
    \/ FinishSync
    \* Apply operations after the collection clone is finished.
    \/ ApplyOp

Spec == Init /\ [][Next]_vars

\*
\* Some properties to check.
\*

\* If the sync has finished and we have applied all necessary operations, then the data between both 
\* nodes should match.
DataConsistency == (syncing = FALSE /\ oplog = <<>>) => /\ remoteColl = localColl

\* A state predicate that holds true when the next step we take would be to apply an update operation 
\* to a document that doesn't exist locally.
ApplyUpdateToMissingDoc == 
    /\ Len(oplog) > 0
    /\ syncing = FALSE 
    /\ Head(oplog)[1] = "u" \* about to apply an insert.
    /\ LET d == Head(oplog)[2] IN localColl[d] = Nil
    
\* In WiredTiger, if an insert occurs during the collection clone, we should be guaranteed to clone it.
\* (Check this)
AlwaysCloneInsertWT == 
    \E d \in Document:
        (/\ Len(oplog) > 0 
         /\ cursor # EOF 
         /\ Head(oplog)[1] = "i"
         /\ Head(oplog)[2] = d) ~> cursor # EOF /\ localColl[d] # Nil

====================================================================================================
\* Modification History
\* Last modified Wed Jul 17 16:54:15 EDT 2019 by williamschultz
\* Created Mon Jul 15 22:10:20 EDT 2019 by williamschultz
