import BTBMS.Statement
import BTBMS.Plan.U5

/-!
# The main theorem: proof

Not locked. The proof of `std_isWellOrder` will import the development; `mainTheorem` and
`paperTheorem` restate it against the locked `MainTheorem` and `PaperTheorem`.
-/

namespace BTBMS

universe u

theorem std_isWellOrder (h : ∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) :
    IsWellOrder Std Std.lt :=
  Descent.abstract_implies_main (fun hM => ⟨_, Descent.finalHyps Hier.jInterface hM⟩) h

theorem mainTheorem : MainTheorem.{u} := std_isWellOrder

theorem paperTheorem : PaperTheorem.{u} := mainTheorem.paper

end BTBMS
