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

## Writing the Spec

It took me about 2-3 days to write the [initial version](https://github.com/will62794/initial-sync-tla/blob/0342619b1e4baaad5753f5fa68f997ffccf5f706/InitSyncDocs.tla) of this spec from scratch and demonstrate the invariant violations with TLC mentioned above. It may have been possible to reproduce the same kind of behaviors with a carefully constructed test suite in a similar amount of time, but I feel that the applicability of such a specific test suite would be considerably less general. Writing down the properties of the system at an abstract level also helps to understand the essential aspects of the problem more clearly. Additionally, once a foundational spec is written, even if it is very simple, it provides a way to ask a wide variety of questions about the system and its behaviors. It also becomes easier to extend the spec to model more detailed behaviors. For example, describing more complex document structures or other operation types. 


