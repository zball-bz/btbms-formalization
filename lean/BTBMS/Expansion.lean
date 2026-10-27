import BTBMS.Syntax

/-!
# The fundamental operation `E[n]`, seeds and standard expressions (paper §1.2–§1.3)

`expand e n` is a line-by-line port of `FS` in the reference `BTBM.ts`
(SmileLee-lyx/ne-rewritten@88df798, `src/notations/BM-like/BTBM.ts`, lines 105–289).
It returns `none` exactly where the reference throws:
* the owner-root branch with an exhausted root scan and `n ≥ 1` (`'Illegal state'`), and
* a failed root lookup (`root_layer` reads past the last forest it can reach and crashes).

On raw syntax outside conditions V and I the reference can also find the root one layer
below the stopping forest, in a child forest that ends in an empty column; its column offset
`t - r` is then negative. `expand` reproduces that case too (`expandExtraLayer`), so that it
agrees with the reference on every natural-labelled forest, not only on admissible ones.

On the empty forest it returns `some ∅`, like the reference (the paper leaves `∅[n]`
undefined; this self-loop adds nothing to `IsStd`, see G-001 / D-3 in the tracker).

Standard expressions are those obtained from the seeds `L_m` by finitely many *defined*
operations (paper §1.3), which is `IsStd`.
-/

namespace BTBMS

open Tree

/-! ## The last-column, last-entry route -/

/-- The last entry of the last column, if there is one. -/
def lastEntry? (e : Forest) : Option (Nat × Forest) :=
  e.cols.getLast? >>= List.getLast?

/-- `next_layer`: the height of the last entry of the last column (`∅` if there is none). -/
def nextLayer (e : Forest) : Forest :=
  match lastEntry? e with
  | some (_, h) => h
  | none => .empty

/-- `skip_layers`: follow the route `n` times. -/
def skipLayers (e : Forest) : Nat → Forest
  | 0 => e
  | n + 1 => skipLayers (nextLayer e) n

/-- Total number of columns of the first `n` forests on the route (`current_left`). -/
def leftCount (e : Forest) : Nat → Nat
  | 0 => 0
  | n + 1 => e.cols.length + leftCount (nextLayer e) n

mutual
/-- `tail_layer`: the depth `ℓ` of the stopping column, or `-1` when the last column of `e`
is empty (or `e` is empty). -/
def tailLayer : Forest → Int
  | .node cols => tailLayerCols cols

def tailLayerCols : List Column → Int
  | [] => -1
  | [c] => tailLayerCol c
  | _ :: rest@(_ :: _) => tailLayerCols rest

def tailLayerCol : Column → Int
  | [] => -1
  | [(_, h)] => 1 + tailLayer h
  | _ :: rest@(_ :: _) => tailLayerCol rest
end

/-- `tail`: the column number `t` of the stopping column at depth `tl`. -/
def tailNum (e : Forest) (tl : Nat) : Nat :=
  leftCount e tl + (skipLayers e tl).cols.length - 1

/-- `root`: the parent `r` of the last entry of the stopping column. -/
def rootAt (e : Forest) (tl : Nat) : Nat :=
  ((lastEntry? (skipLayers e tl)).map Prod.fst).getD 0

/-- `root_layer`: the depth and index of column `r` on the route. The reference searches
forest after forest until it finds `r`. It can succeed in the first `tl + 2` forests: the
`tl + 1` forests of the route, and the height of the stopping entry, which on raw syntax can be
a nonempty forest ending in an empty column. Reading the next forest after that crashes; `none`
records the crash. -/
def rootLayerAux (r : Nat) : Nat → Forest → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, cur, left, layer =>
    if r < left + cur.cols.length then some (layer, r - left)
    else rootLayerAux r fuel (nextLayer cur) (left + cur.cols.length) (layer + 1)

def rootLayer (e : Forest) (r tl : Nat) : Option (Nat × Nat) :=
  rootLayerAux r (tl + 2) e 0 0

/-! ## Shifts and replacement (paper §1.1, `T_{r,d}` and `A_{r,d,ℓ,Z}`) -/

/-- Add `d` to a parent that is at least `r`. -/
def shiftVal (r d p : Nat) : Nat := if r ≤ p then p + d else p

/-- Apply `g` to the last element of a list and `f` to every other element. -/
def mapLast {β γ : Type} (f g : β → γ) : List β → List γ
  | [] => []
  | [x] => [g x]
  | x :: xs@(_ :: _) => f x :: mapLast f g xs

/-- Subtract `k` from a parent that is at least `r` (a negative shift; used only when the
reference's offset `t - r` is negative, see `expandExtraLayer`). -/
def shiftDownVal (r k p : Nat) : Nat := if r ≤ p then p - k else p

/-- `A_{r,d,k,Z}`: shift every parent `≥ r` by `d` at every depth, except that the last column
at depth `k` on the route is replaced by the columns of `Z` (which are not shifted). This is
the paper's `A_{r,d,ℓ,Z}` whenever the route reaches a column at depth `k`; on a forest with no
columns it returns `∅`, as the reference does. -/
def replaceAt (r d : Nat) (Z : Forest) : Nat → Forest → Forest
  | 0, .node cols =>
    match cols with
    | [] => .node []
    | _ => .node (cols.dropLast.map (Tree.mapCol (shiftVal r d)) ++ Z.cols)
  | k + 1, .node cols =>
    .node (mapLast (Tree.mapCol (shiftVal r d))
      (mapLast (fun (p, h) => (shiftVal r d p, Tree.map (shiftVal r d) h))
        (fun (p, h) => (shiftVal r d p, replaceAt r d Z k h)))
      cols)

/-- `ascend_replace` with an optional, possibly negative, depth. A missing or negative depth
never reaches a replacement, so it is the plain shift `T_{r,d}`. -/
def ascendReplace (r d : Nat) (tl : Option Int) (Z F : Forest) : Forest :=
  match tl with
  | some (Int.ofNat k) => replaceAt r d Z k F
  | _ => Tree.map (shiftVal r d) F

/-! ## The special branch -/

/-- `is_special`: depth `tl > 0`, the stopping column is a single entry with empty height, and
its parent is the direct owner of the stopping forest. -/
def isSpecial (e : Forest) (tl : Nat) : Bool :=
  tl != 0 &&
    match (skipLayers e tl).cols.getLast? with
    | some [(v, h)] => h.cols.isEmpty && v == leftCount e tl - 1
    | _ => false

/-- `expand_special`: replace the containing entry `(p, C ⌢ [[(a, ∅)]])` by `n + ε` copies of
`(p, C)`, where `ε = 1` iff no entry precedes it in its column. -/
def expandSpecial (n : Nat) : Nat → Forest → Forest
  | k + 2, .node cols =>
    let col := cols.getLast?.getD []
    let (v, h) := col.getLast?.getD (0, .empty)
    .node (cols.dropLast ++ [col.dropLast ++ [(v, expandSpecial n (k + 1) h)]])
  | _, .node cols =>
    let col := cols.getLast?.getD []
    let (v, h) := col.getLast?.getD (0, .empty)
    let ne : Nat × Forest := (v, .node h.cols.dropLast)
    let rest := col.dropLast
    let first := if rest.isEmpty then [ne] else rest
    .node (cols.dropLast ++ [first ++ List.replicate n ne])

/-! ## The ordinary branch -/

/-- The two-cursor scan of `root_appending_start`: at keys `x, y` advance the source cursor
when `x ≤ y` and the query cursor when `x ≥ y`; stop when either list ends. Returns the
final source cursor. -/
def scanCount : List Key → List Key → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys =>
    match keyCmp x y with
    | .lt => scanCount xs (y :: ys) + 1
    | .eq => scanCount xs ys + 1
    | .gt => scanCount (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- `root_appending_start`: scan the root heights, normalized at `r`, against the heights of
the query `Q` (the stopping column without its last entry), normalized at `t`. -/
def rootAppendingStart (colRoot : Column) (r : Nat) (colTail : Column) (t : Nat) : Nat :=
  scanCount (colRoot.map fun x => relKey r x.2) (colTail.dropLast.map fun x => relKey t x.2)

/-- Run `step` for `j = n, n - 1, …, 1`, starting from `Z`. -/
def iterDown (step : Nat → Forest → Forest) : Nat → Forest → Forest
  | 0, Z => Z
  | j + 1, Z => iterDown step j (step (j + 1) Z)

/-- The ordinary branch when the root lies in the height of the stopping entry (raw syntax
only; it violates V). There the reference has stopping number `t < r`, an empty query, nothing
consumed by the scan, and a negative continuation depth, so the tail built for `j` is never
inserted into the tail for `j - 1`: the result is the `j = 1` tail, shifted by `t - r < 0`.
* Root in the final (empty) column: the owner-root branch with an exhausted scan.
* Otherwise: the head is the whole root column with heights shifted, then the later columns.
`n = 0` deletes the stopping column in both cases. -/
def expandExtraLayer (e eRoot : Forest) (n tl t r ri : Nat) : Option Forest :=
  if n == 0 then some (replaceAt 0 0 .empty tl e)
  else if ri == eRoot.cols.length - 1 then none
  else
    let sh := shiftDownVal r (r - t)
    let head : Column := (eRoot.cols.getD ri []).map fun x => (x.1, Tree.map sh x.2)
    let body := (eRoot.cols.drop (ri + 1)).map (Tree.mapCol sh)
    some (replaceAt 0 0 (.node (head :: body)) tl e)

/-- The fundamental operation `E[n]` (paper §1.2), as `FS` in `BTBM.ts`; `none` where the
reference throws. -/
def expand (e : Forest) (n : Nat) : Option Forest :=
  match e.cols with
  | [] => some e
  | _ =>
    let tlI := tailLayer e
    if tlI < 0 then some (.node e.cols.dropLast) else
    let tl := tlI.toNat
    if isSpecial e tl then some (expandSpecial n tl e) else
    let t := tailNum e tl
    let r := rootAt e tl
    match rootLayer e r tl with
    | none => none
    | some (rl, ri) =>
      let eRoot := skipLayers e rl
      if tl < rl then expandExtraLayer e eRoot n tl t r ri else
      let colRoot := eRoot.cols.getD ri []
      let colTail := (skipLayers eRoot (tl - rl)).cols.getLast?.getD []
      let app := rootAppendingStart colRoot r colTail t
      let d := t - r
      -- the head: `T_{r,(j-1)d}(Q)` followed by the unconsumed root suffix `U`
      let headQ (j : Nat) : Column := Tree.mapCol (shiftVal r ((j - 1) * d)) colTail.dropLast
      let U := colRoot.drop app
      if ri != eRoot.cols.length - 1 then
        let step (j : Nat) (Z : Forest) : Forest :=
          let body := ascendReplace r (j * d) (some ((tl : Int) - rl)) Z (.node (eRoot.cols.drop (ri + 1)))
          let head := headQ j ++ U.map fun x => (x.1, Tree.map (shiftVal r (j * d)) x.2)
          .node (head :: body.cols)
        some (replaceAt 0 0 (iterDown step n .empty) tl e)
      -- the reference throws inside its loop over `j = n, …, 1`, so only when `n ≥ 1`
      else if n != 0 && app == colRoot.length then none
      else
        let step (j : Nat) (Z : Forest) : Forest :=
          let head := headQ j ++ mapLast (fun x => (x.1, Tree.map (shiftVal r (j * d)) x.2))
            (fun x => (x.1, ascendReplace r (j * d) (some ((tl : Int) - rl - 1)) Z x.2)) U
          .node [head]
        some (replaceAt 0 0 (iterDown step n .empty) tl e)

/-! ## Seeds and standard expressions (paper §1.3) -/

/-- The singleton branch with parents `i, i + 1, …, i + k`; the innermost height is empty. -/
def branch : Nat → Nat → Column
  | i, 0 => [(i, .empty)]
  | i, k + 1 => [(i, .node [branch (i + 1) k])]

/-- The seed `L_m`: `L_0 = ()` (one empty column); for `m > 0`, an empty outer column followed
by a branch of `m` singleton entries whose parents are `0, 1, …, m - 1`. As `infinity_FS(m)`. -/
def seed : Nat → Forest
  | 0 => .node [[]]
  | m + 1 => .node [[], branch 0 m]

/-- Standard expressions: obtainable from the seeds by finitely many defined operations. -/
inductive IsStd : Forest → Prop
  | seed (m : Nat) : IsStd (seed m)
  | expand {e e' : Forest} (n : Nat) : IsStd e → expand e n = some e' → IsStd e'

end BTBMS
