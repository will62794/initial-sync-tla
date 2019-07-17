## Modeling Initial Sync of a Collection

Some questions/thoughts:

- Should we allow a document to be deleted and re-inserted in the model, or should we
only allow a document to exist once before it gets deleted?
- In order to illustrate a data consistency issue when we don't refetch documents, I think we need to at least include a simplified model of document keys. If documents only map to a version number or are Nil, then I don't think an update that is made into an upsert during application would manifest as a data inconsistency, even though we would technically be updating a document that doesn't exist on the receiving node. Thus, I included a simple model of document keys. It is also probably helpful to specify that "error" cases as their own properties e.g. "do we ever need to update a document that doesn't exist during oplog application?". If we write this as a predicate and check it, then it can give a more rigorous justification for why it's OK to convert updates to upserts. Similarly for other errors like duplicate keys, etc.