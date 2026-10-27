import BTBMS.Statement

/-!
# Sanity checks on the statement's definitions

Not part of the statement. These guard against definitions that are accidentally trivial:
the base of the Mahlo recursion is inhabited, "stationary" is neither always true nor always
false, and the order and seeds behave as expected on small cases.
-/

namespace BTBMS

open Cardinal

/-- `ℵ₁` is weakly 0-Mahlo (an uncountable regular cardinal), so the recursion's base is
inhabited. -/
example : IsWeaklyMahlo 0 ℵ₁ := ⟨aleph0_lt_aleph_one, isRegular_aleph_one⟩

/-- Below an uncountable cardinal, the set of all ordinals is stationary. -/
example {κ : Cardinal} (h : ℵ₀ < κ) : StationaryIn κ Set.univ := by
  have h0 : (0 : Ordinal) < κ.ord := Cardinal.lt_ord.2 (by simpa using aleph0_pos.trans h)
  have : Nonempty (Set.Iio κ.ord) := ⟨⟨0, h0⟩⟩
  simp only [StationaryIn, Set.mem_univ, Set.ofPred_true]
  exact IsStationary.univ

/-- The empty set is never stationary. -/
example (κ : Cardinal) : ¬ StationaryIn κ ∅ := by
  simp only [StationaryIn, Set.mem_empty_iff_false, Set.ofPred_false]
  exact not_isStationary_empty

/-- The seeds are standard, and `L_1 = (0)(1)` lies below `L_2 = (0)(1^(2))`. -/
example : IsStd (seed 1) := .seed 1
example : seed 1 < seed 2 := by decide
example : ¬ seed 2 < seed 1 := by decide
example : (Tree.empty : Forest) < seed 0 := by decide

end BTBMS
