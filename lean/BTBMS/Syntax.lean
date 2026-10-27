/-!
# BTBMS syntax and its order (paper §1.1)

A forest is a finite list of columns, a column is a finite list of entries, and an entry is a
pair `(p, H)` of a parent label and a height `H`, itself a forest. `Tree α` is this shape with
labels in `α`: forests use `Nat`, relative keys (§1.1, `h_a`) use `Bool × Nat`.

The order compares entries by label, then height; columns and forests lexicographically, with a
proper prefix smaller. It mirrors `compare` / `height_compare` in the reference `BTBM.ts`.
-/

namespace BTBMS

/-- Finite forests with labels in `α`. -/
inductive Tree (α : Type) where
  | node (cols : List (List (α × Tree α)))

namespace Tree

variable {α : Type}

instance : Inhabited (Tree α) := ⟨.node []⟩

/-- The columns of a forest. -/
def cols : Tree α → List (List (α × Tree α))
  | .node c => c

/-- The empty forest `∅` (no columns). -/
def empty : Tree α := .node []

mutual
/-- Lexicographic comparison of forests, given a comparison of labels. -/
def cmp (c : α → α → Ordering) : Tree α → Tree α → Ordering
  | .node a, .node b => cmpCols c a b

/-- Lexicographic comparison of column lists; a proper prefix is smaller. -/
def cmpCols (c : α → α → Ordering) :
    List (List (α × Tree α)) → List (List (α × Tree α)) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => (cmpCol c x y).then (cmpCols c xs ys)

/-- Lexicographic comparison of columns; entries compare by label, then height. -/
def cmpCol (c : α → α → Ordering) : List (α × Tree α) → List (α × Tree α) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (p, h) :: es, (q, k) :: fs => ((c p q).then (cmp c h k)).then (cmpCol c es fs)
end

mutual
/-- Relabel every entry of a forest. -/
def map {β : Type} (f : α → β) : Tree α → Tree β
  | .node a => .node (mapCols f a)

def mapCols {β : Type} (f : α → β) : List (List (α × Tree α)) → List (List (β × Tree β))
  | [] => []
  | x :: xs => mapCol f x :: mapCols f xs

def mapCol {β : Type} (f : α → β) : List (α × Tree α) → List (β × Tree β)
  | [] => []
  | (p, h) :: es => (f p, map f h) :: mapCol f es
end

end Tree

/-- BTBMS expressions: forests labelled by parent column numbers. -/
abbrev Forest := Tree Nat

/-- A column of a forest. -/
abbrev Column := List (Nat × Forest)

/-- The syntax order on forests (paper §1.1). -/
instance : LT Forest := ⟨fun a b => Tree.cmp compare a b = .lt⟩

instance (a b : Forest) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Tree.cmp compare a b = .lt))

/-- Relative keys (paper §1.1, `h_a`): a parent `p` becomes the false field `(false, p)` when
`p < a`, and the true field `(true, p - a)` otherwise; the same threshold is used at every
depth. Mirrors `to_height` in `BTBM.ts`. -/
abbrev Key := Tree (Bool × Nat)

def relKey (a : Nat) (H : Forest) : Key :=
  H.map fun p => if p < a then (false, p) else (true, p - a)

/-- Comparison of relative-key labels: false fields before true fields, then by value.
Mirrors `height_entry_comparator` in `BTBM.ts`. -/
def keyLabelCmp (x y : Bool × Nat) : Ordering :=
  (compare x.1 y.1).then (compare x.2 y.2)

/-- Comparison of relative keys. -/
def keyCmp (x y : Key) : Ordering := Tree.cmp keyLabelCmp x y

end BTBMS
