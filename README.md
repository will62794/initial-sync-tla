# Specification of MongoDB Initial Sync


This TLA+ specification models a simplified version of the MongoDB initial sync process. Initial sync is a protocol for transferring data from one replica set node to another while data operations are still occurring on the source node. One of the spec's main goals is to illustrate how the divergent collection scan semantics between the MMAPv1 and WiredTiger storage engine affect whether or not initial sync may need to re-fetch documents from its sync source during the oplog application phase.

The cursor semantics for updates can be toggled between MMAPv1 and WiredTiger behavior by choosing the `MMAPUpdateAction` or the `WTUpdateAction`. The key correctness requirement is defined in the `DataConsistency` predicate, which states that if the initial sync has completed then the data on the local and remote nodes should be the same. 

## Model Checking

I ran TLC with a model that instantiates the following:

```
Nil -> model value
EOF -> model value
Document -> {d1, d2, d3}  \* set of model values (symmetry set).
Key -> {k1, k2}           \* set of model values (symmetry set).

StateConstraint: Len(oplog) <= 4
```
When using the `MMAPUpdateAction` and checking the `DataConsistency` invariant, a violation is found in a few seconds. [Here](traces/mmap_initial_sync_consistency_violation.txt) is a raw trace of such a run. When using the `WTUpdateAction` and checking the same invariant, no violation is found. The model checker ran for around 1 minute and produced 1,328,041 distinct states.

### Further Inspection

We can also ask some additional questions about possible behaviors of the system. For example, is it possible that, during cloning, we may insert a document into the local collection that already exists? Similarly, we can ask whether it is possible for us to apply an update to a non-existent document during oplog application. These are encoded, respectively, into the following state predicates:

- `InsertExistingDocDuringClone`
- `ApplyUpdateToMissingDoc`

By checking the negation of these predicates (`~` is the negation operator) as invariants, we can try to find behaviors that satisfy them. When only including insert and update operations in the model, TLC finds no state that satisfies either of these predicates when using the WiredTiger semantics i.e. `WTUpdateAction`. However, TLC finds satisfying states for both predicates when using MMAP semantics i.e. `MMAPUpdateAction`. For the `InsertExistingDocDuringClone` case, this should make sense due to the fact that WiredTiger updates do not affect a document's position in the collection scan order. So, if a document is cloned once, then it should never be cloned again, since it can never move "ahead" in the scan. In MMAP, however, after a document is fetched, it could be updated and jump forward in the scan, and we would thus copy it again. A similar reason explains why `ApplyUpdateToMissingDoc` can be satisfied only under MMAP. Before a document is cloned, it may be updated and jump back behind the current cursor position. This means the document will be "missed" in the scan and we will later apply that corresponding update operation at the end of initial sync. Under WiredTiger, semantics, updates don't affect document position, so we are guaranteed to see all documents in the scan. 

Note that incorporating delete operations into the model should change the behaviors described above, since it would then become possible for documents to be deleted and re-inserted, presumably allowing for documents to be cloned twice, even under WiredTiger collection scan semantics. This could be something to check in the future.

## Writing the Spec

It took me about 2-3 days to write the [initial version](https://github.com/will62794/initial-sync-tla/blob/0342619b1e4baaad5753f5fa68f997ffccf5f706/InitSyncDocs.tla) of this spec from scratch and demonstrate the invariant violations with TLC mentioned above. It may have been possible to reproduce the same kind of behaviors with a carefully constructed test suite in a similar amount of time, but I feel that the applicability of such a specific test suite would be considerably less general. Writing down the properties of the system at an abstract level also helps to understand the essential aspects of the problem more clearly. Additionally, once a foundational spec is written, even if it is very simple, it provides a way to ask a wide variety of questions about the system and its behaviors. It also becomes easier to extend the spec to model more detailed behaviors. For example, describing more complex document structures or other operation types. 


