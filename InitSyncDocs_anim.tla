---- MODULE InitSyncDocs_anim ----
\*
\* Spectacle-style SVG animation view for InitSyncDocs.
\*
\* Visualizes:
\*   - oplog       : queued operations (i / u / d) with payload text, head at left
\*   - remoteCollSeq : the sync source's scan order, with each remote doc state shown
\*   - localColl   : per-scan-position document state in the local collection
\*   - syncing / cursor : status line at the bottom
\*

EXTENDS InitSyncDocs, TLC

\* ---------- SVG primitives (same shape as AbstractRaft_anim.tla) ----------

Merge(r1, r2) ==
    LET D1 == DOMAIN r1
        D2 == DOMAIN r2
    IN  [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) ==
    [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText]

Text(x, y, text, attrs) ==
    LET svgAttrs == [x |-> x, y |-> y]
    IN  SVGElem("text", Merge(svgAttrs, attrs), <<>>, text)

Rect(x, y, w, h, attrs) ==
    LET svgAttrs == [x |-> x, y |-> y, width |-> w, height |-> h]
    IN  SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Group(children, attrs) == SVGElem("g", attrs, children, "")

\* ---------- Layout constants ----------

X0 == 20
CellW == 130
CellH == 44
RowOplogY == 36
\* Extra vertical space between the oplog strip and the remote scan row.
GapBelowOplog == 28
RowRemoteY == 96 + GapBelowOplog
RowLocalY == 176 + GapBelowOplog
StatusY == 272 + GapBelowOplog

\* ---------- Status / labels ----------

CursorLabel ==
    IF cursor = EOF THEN "cursor=EOF"
    ELSE "cursor=" \o ToString(cursor)

SyncLine ==
    "syncing=" \o ToString(syncing)
        \o "   cloneComplete=" \o ToString(CloneComplete)
        \o "   " \o CursorLabel

DataConsistencyLine ==
    "DataConsistency=" \o IF DataConsistency THEN "OK" ELSE "VIOLATED"

\* ---------- Remote scan row ----------

RemoteDocStateLabel(d) ==
    IF remoteColl[d] = Nil THEN ToString(d) \o ": Nil"
    ELSE ToString(d) \o ": " \o ToString(remoteColl[d])

RemoteCell(i) ==
    LET d == remoteCollSeq[i]
        atCursor == IF cursor = EOF THEN FALSE ELSE i = cursor
    IN  Group(<<
            Rect(
                X0 + (i - 1) * CellW,
                RowRemoteY,
                CellW - 2,
                CellH,
                [ fill        |-> IF atCursor THEN "#fff3cd" ELSE "#e9ecef",
                  stroke      |-> IF atCursor THEN "#0d6efd" ELSE "#333333" ]),
            Text(
                X0 + (i - 1) * CellW + 3,
                RowRemoteY + 16,
                RemoteDocStateLabel(d),
                ( "font-size" :> "10px" @@ "font-family" :> "sans-serif" ))
        >>, [a \in {} |-> {}])

RemoteRow ==
    IF Len(remoteCollSeq) = 0 THEN
        Text(X0, RowRemoteY + 19, "(remoteCollSeq empty)", [ fill |-> "#666666" ])
    ELSE
        Group([i \in 1..Len(remoteCollSeq) |-> RemoteCell(i)], [a \in {} |-> {}])

\* ---------- Local clone row (aligned under each scan position) ----------

LocalDocStateLabel(d) ==
    IF localColl[d] = Nil THEN ToString(d) \o ": Nil"
    ELSE ToString(d) \o ": " \o ToString(localColl[d])

LocalCell(i) ==
    LET d   == remoteCollSeq[i]
        lv  == localColl[d]
    IN  Group(<<
            Rect(
                X0 + (i - 1) * CellW,
                RowLocalY,
                CellW - 2,
                CellH,
                [ fill   |-> IF lv = Nil THEN "#f8d7da" ELSE "#d1e7dd",
                  stroke |-> "#333333" ]),
            Text(
                X0 + (i - 1) * CellW + 3,
                RowLocalY + 16,
                LocalDocStateLabel(d),
                ( "font-size" :> "10px" @@ "font-family" :> "sans-serif" ))
        >>, [a \in {} |-> {}])

LocalRow ==
    IF Len(remoteCollSeq) = 0 THEN
        Text(X0, RowLocalY + 19, "(no scan positions)", [ fill |-> "#666666" ])
    ELSE
        Group([i \in 1..Len(remoteCollSeq) |-> LocalCell(i)], [a \in {} |-> {}])

\* ---------- Oplog row (head at left) ----------

\* Per-entry horizontal stride (kind + payload; narrow width, text may extend past rect in SVG).
OplogCellW == 100
OplogCellH == 40
OplogCellDX == OplogCellW + 4
\* SVG corner radius for oplog rects (`rx` / `ry` on `<rect>`).
OplogCornerR == "6"

OpKind(j)  == oplog[j][1]

\* Human-readable payload for each op tuple <<op, d, k_or_nil, v_or_doc>>.
OplogOpDetail(j) ==
    LET op == oplog[j][1]
        d  == oplog[j][2]
        k  == oplog[j][3]
        v  == oplog[j][4]
    IN IF op = "i" THEN
           ToString(d) \o " ← " \o ToString(v)
       ELSE IF op = "u" THEN
           ToString(d) \o "." \o ToString(k) \o "=" \o ToString(v)
       ELSE IF op = "d" THEN
           ToString(d)
       ELSE
           ToString(oplog[j])

OplogCell(j) ==
    LET x == X0 + (j - 1) * OplogCellDX
    IN  Group(<<
            Rect(x, RowOplogY, OplogCellW - 2, OplogCellH,
                [ fill |-> "#cfe2ff", stroke |-> "#084298",
                  rx |-> OplogCornerR, ry |-> OplogCornerR ]),
            Text(x + 6, RowOplogY + 16, OpKind(j),
                ( "font-size" :> "12px" @@ "font-weight" :> "600"
                  @@ "font-family" :> "sans-serif" )),
            Text(x + 6, RowOplogY + 32, OplogOpDetail(j),
                ( "font-size" :> "9px" @@ "font-family" :> "sans-serif" ))
        >>, [a \in {} |-> {}])

OplogRow ==
    IF Len(oplog) = 0 THEN
        Text(X0, RowOplogY + 22, "oplog: (empty)", [ fill |-> "#666666" ])
    ELSE
        Group([j \in 1..Len(oplog) |-> OplogCell(j)], [a \in {} |-> {}])

\* ---------- Section titles + status ----------

SectionTitles ==
    Group(<<
        Text(X0, RowOplogY  - 14, "oplog (head at left)",
            ( "font-weight" :> "bold" @@ "font-family" :> "sans-serif" @@ "font-size" :> "12px" )),
        Text(X0, RowRemoteY - 14, "remote scan order (remoteCollSeq)",
            ( "font-weight" :> "bold" @@ "font-family" :> "sans-serif" @@ "font-size" :> "12px" )),
        Text(X0, RowLocalY  - 14, "local clone (localColl per position)",
            ( "font-weight" :> "bold" @@ "font-family" :> "sans-serif" @@ "font-size" :> "12px" )),
        Text(X0, StatusY, SyncLine,
            ( "fill" :> (IF syncing THEN "#856404" ELSE "#155724") @@ "font-size" :> "13px" @@ "font-family" :> "sans-serif" )),
        Text(X0, StatusY + 18, DataConsistencyLine,
            ( "fill" :> (IF DataConsistency THEN "#155724" ELSE "#842029") @@ "font-size" :> "13px" @@ "font-family" :> "sans-serif" ))
    >>, [a \in {} |-> {}])

\* ---------- Top-level animation view ----------

AnimView ==
    Group(<< SectionTitles, OplogRow, RemoteRow, LocalRow >>,
          [ transform |-> "translate(12, 12)" ])

=============================================================================
