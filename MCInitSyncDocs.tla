---- MODULE MCInitSyncDocs ----
EXTENDS InitSyncDocs, TLC

StateConstraint == Len(oplog) <= 5

NeverInsertExistingDocDuringClone == ~InsertExistingDocDuringClone
NeverApplyUpdateToMissingDoc == ~ApplyUpdateToMissingDoc

Symmetry == Permutations(Document \cup Key)

====