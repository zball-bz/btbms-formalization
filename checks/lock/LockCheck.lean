import BTBMS

/-! Run by `checks/lock/check.sh`. The file hashes in `statement.lock.json` pin the locked
sources; this file pins the elaborated statements and prints the main theorem's axioms. -/

namespace BTBMS

universe u

-- The locked statements are the types reviewed in T-014 and signed off at G2.
example : MainTheorem.{u} =
    ((∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt) := rfl
example : PaperTheorem.{u} =
    ((∀ n : Nat, ∃ κ : Cardinal.{u}, IsMahlo n κ) → IsWellOrder Std Std.lt) := rfl

-- The exported theorems prove the locked statements.
example : MainTheorem.{u} := mainTheorem
example : PaperTheorem.{u} := paperTheorem

end BTBMS

#print axioms BTBMS.mainTheorem
