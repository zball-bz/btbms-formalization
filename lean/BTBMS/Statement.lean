import BTBMS.Expansion
import BTBMS.Mahlo

/-!
# The main theorem (paper §9)

> ZFC plus the existence of an n-Mahlo cardinal for each n ∈ ω proves that (Std, <) is a
> well-order.

This file only states it. `std_isWellOrder` uses weakly n-Mahlo cardinals (the stronger
theorem; tracker D-2); `std_isWellOrder_of_mahlo` is the paper's form and follows from it.
The hypothesis lives in an arbitrary universe `u`: it is not provable in Lean (whose strength
is roughly ZFC plus finitely many inaccessibles for each finite number), so it is an explicit
premise.
-/

namespace BTBMS

universe u

/-- The standard BTBMS expressions (paper §1.3). -/
def Std : Type := {e : Forest // IsStd e}

/-- The syntax order restricted to standard expressions. -/
def Std.lt (a b : Std) : Prop := a.1 < b.1

/-- **Main theorem**, with weakly n-Mahlo cardinals: if for every `n` there is a weakly
`n`-Mahlo cardinal, then the standard expressions are well-ordered by the syntax order. -/
theorem std_isWellOrder (h : ∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) :
    IsWellOrder Std Std.lt := by
  sorry

/-- **Main theorem**, as stated in the paper (§9), with n-Mahlo cardinals over inaccessibles. -/
theorem std_isWellOrder_of_mahlo (h : ∀ n : Nat, ∃ κ : Cardinal.{u}, IsMahlo n κ) :
    IsWellOrder Std Std.lt :=
  std_isWellOrder.{u} fun n => (h n).imp fun _ hκ => hκ.isWeaklyMahlo

end BTBMS
