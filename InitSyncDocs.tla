--------------------------------------- MODULE InitSyncDocs ---------------------------------------
\*
\* Initial syncing a single MongoDB collection.
\*

EXTENDS Sequences, Naturals, Integers, FiniteSets

\* The set of all possible documents.
CONSTANT Document

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

\* Nilete an element from a sequence at a specified index.
DeleteElement(seq, index) == [i \in 1..(Len(seq)-1) |-> IF i<index THEN seq[i] ELSE seq[(i+1)]]  

\* The sync source performs an insert. (ACTION)
Insert(d) == 
    \* Cannot have duplicate documents.
    /\ remoteColl[d] = Nil
    /\ remoteColl' = [remoteColl EXCEPT ![d] = 0]
    \* Append documents to the end of the sequence for now.
    /\ remoteCollSeq' = Append(remoteCollSeq, d)
    /\ oplog' = Append(oplog, <<"i", d, 0>>)
    /\ UNCHANGED <<localColl, cursor, syncing>>

\* The sync source performs an update. (ACTION)
Update(d) == 
    \* The document must exist.
    /\ remoteColl[d] # Nil
    \* Bump the version and, for now, don't re-position the document in scan order.
    /\ remoteColl' = [remoteColl EXCEPT ![d] = remoteColl[d] + 1]
    /\ oplog' = Append(oplog, <<"u", d, remoteColl[d] + 1>>)
    /\ UNCHANGED <<localColl, remoteCollSeq, cursor, syncing>>        

\* The sync source performs a delete. (ACTION)
Delete(d) == 
    \* The document must exist.
    /\ remoteColl[d] # Nil
    \* Set the document to Nil. Don't re-position the document in scan order.
    /\ remoteColl' = [remoteColl EXCEPT ![d] = Nil]
    \* We have to delete the element from the collection sequence. We don't need to adjust the cursor because
    \*
    /\ LET ind == CHOOSE i \in DOMAIN remoteCollSeq : remoteCollSeq[i] = d IN
                  /\ remoteCollSeq' = DeleteElement(remoteCollSeq, ind)
                  /\ cursor' = IF ind = cursor THEN (cursor + 0) ELSE cursor
    /\ oplog' = Append(oplog, <<"d", d, Nil>>)
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
\* In this model, this means the sync source will stop executing new operations. In the real
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
           v  == Head(oplog)[3] IN
           \* insert.
           IF      op = "i" THEN localColl' = [localColl EXCEPT ![d] = v]
           \* update.
           ELSE IF op = "u" THEN localColl' = [localColl EXCEPT ![d] = v]
           \* delete.
           ELSE IF op = "d" THEN localColl' = [localColl EXCEPT ![d] = v]
           ELSE UNCHANGED <<localColl>>
    /\ oplog' = Tail(oplog)
    /\ IF Len(oplog) = 1 THEN cursor' = Nil ELSE UNCHANGED cursor \* signal the end of initial sync.
    /\ UNCHANGED <<remoteColl, remoteCollSeq, syncing>>

\*
\* Define the possible initial states.
\*

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

Init == 
    /\ oplog = <<>>
    \* A collection is a map from document ids to their current version.
    /\ \E c \in [Document -> {0, Nil}]:
        /\ remoteColl = c
        /\ LET existingDocs == {d \in DOMAIN c : c[d] # Nil} IN
            /\ remoteCollSeq \in [1..Cardinality(existingDocs) -> existingDocs]
            /\ Injective(remoteCollSeq)
    /\ cursor = 1
    /\ localColl = [d \in Document |-> Nil]
    \* We start off with the sync in-progress, which means that operations may occur on the sync source and we can 
    \* clone documents.
    /\ syncing = TRUE

Next == 
    \* A remote op occurs.
    \E d \in Document:
        /\ syncing \* Stop executing new ops after the sync has completed.
        /\ \/ Insert(d) 
           \/ Update(d)
           \/ Delete(d)
    \* The syncing node fetches a new document.
    \/ FetchDoc
    \* Apply operations after the collection clone is finished.
    \/ ApplyOp

Spec == Init /\ [][Next]_vars

\* If the sync has finished and we have applied all necessary operations, then the data between both 
\* nodes should match.
DataConsistency == (syncing = FALSE /\ oplog = <<>>) => /\ remoteColl = localColl

====================================================================================================
\* Modification History
\* Last modified Tue Jul 16 15:06:20 EDT 2019 by williamschultz
\* Created Mon Jul 15 22:10:20 EDT 2019 by williamschultz
