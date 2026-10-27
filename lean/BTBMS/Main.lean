import BTBMS.Statement

/-!
# The main theorem: proof

Not locked. The proof of `std_isWellOrder` will import the development; `mainTheorem` and
`paperTheorem` restate it against the locked `MainTheorem` and `PaperTheorem`.
-/

namespace BTBMS

universe u

theorem std_isWellOrder (h : ∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) :
    IsWellOrder Std Std.lt := by
  sorry

theorem mainTheorem : MainTheorem.{u} := std_isWellOrder

theorem paperTheorem : PaperTheorem.{u} := mainTheorem.paper

end BTBMS
