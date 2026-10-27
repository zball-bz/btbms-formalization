import BTBMS.Expansion
import BTBMS.Mahlo

/-!
# The main theorem (paper §9): statement only

> ZFC plus the existence of an n-Mahlo cardinal for each n ∈ ω proves that (Std, <) is a
> well-order.

This file is **locked** (user gate G2, 2026-10-27), together with `Syntax.lean`,
`Expansion.lean` and `Mahlo.lean`; `checks/lock/check.sh` refuses any change. The proof lives
elsewhere and must have type `MainTheorem` (see `BTBMS/Main.lean`).

`MainTheorem` uses weakly n-Mahlo cardinals (the stronger theorem; tracker D-2); `PaperTheorem`
is the paper's form and follows from it. The hypothesis lives in an arbitrary universe `u` and
is an explicit premise. Parts of it are available in Lean: weakly 0-Mahlo cardinals exist in
every universe (`ℵ₁`), and Mathlib's `Cardinal.IsInaccessible.univ` gives an inaccessible one
universe up. No positive Mahlo level is supplied by Lean or Mathlib, and the premise is about
the single universe `u`.
-/

namespace BTBMS

universe u

/-- The standard BTBMS expressions (paper §1.3). -/
def Std : Type := {e : Forest // IsStd e}

/-- The syntax order restricted to standard expressions. -/
def Std.lt (a b : Std) : Prop := a.1 < b.1

/-- **Main theorem**, with weakly n-Mahlo cardinals: if for every `n` there is a weakly
`n`-Mahlo cardinal, then the standard expressions are well-ordered by the syntax order. -/
def MainTheorem : Prop :=
  (∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt

/-- **Main theorem**, as stated in the paper (§9), with n-Mahlo cardinals over inaccessibles. -/
def PaperTheorem : Prop :=
  (∀ n : Nat, ∃ κ : Cardinal.{u}, IsMahlo n κ) → IsWellOrder Std Std.lt

/-- The paper's form follows from the weakly Mahlo form. -/
theorem MainTheorem.paper (hm : MainTheorem.{u}) : PaperTheorem.{u} :=
  fun h => hm fun n => (h n).imp fun _ hκ => hκ.isWeaklyMahlo

end BTBMS
