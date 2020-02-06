---- MODULE MCInitSyncDocs ----
EXTENDS InitSyncDocs

StateConstraint == Len(oplog) <= 4

NeverInsertExistingDocDuringClone == ~InsertExistingDocDuringClone

====