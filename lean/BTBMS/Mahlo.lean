import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Finite Mahlo hierarchies (paper §6.2)

The paper sets `M₀` = inaccessible cardinals and `Mₙ₊₁ = {κ ∈ M₀ : Mₙ ∩ κ is stationary in κ}`.
`IsMahlo n` is that hierarchy. `IsWeaklyMahlo n` is the same recursion over uncountable
regular cardinals; the proof only uses regularity and stationarity (tracker S-1), so the
main theorem is stated with it and the paper's form follows (`IsMahlo.isWeaklyMahlo`).

Cardinals are identified with their initial ordinals, so "`S ∩ κ` stationary in `κ`" means:
the ordinals of `S` below `κ.ord`, viewed as a subset of the well-order `Set.Iio κ.ord`, meet
every club of it (Mathlib's `IsStationary`, with clubs closed under suprema and cofinal).
-/

namespace BTBMS

open Cardinal

universe u

/-- `S` is stationary in `κ`. -/
def StationaryIn (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  IsStationary {x : Set.Iio κ.ord | x.1 ∈ S}

theorem StationaryIn.mono {κ : Cardinal.{u}} {S T : Set Ordinal.{u}} (h : StationaryIn κ S)
    (hST : S ⊆ T) : StationaryIn κ T :=
  IsStationary.mono h fun _ hx => hST hx

/-- Weakly `n`-Mahlo: `W₀` = uncountable regular cardinals, `Wₙ₊₁ = {κ ∈ W₀ : Wₙ ∩ κ is
stationary in κ}`. -/
def IsWeaklyMahlo : Nat → Cardinal.{u} → Prop
  | 0, κ => ℵ₀ < κ ∧ κ.IsRegular
  | n + 1, κ => (ℵ₀ < κ ∧ κ.IsRegular) ∧
      StationaryIn κ {o | ∃ μ : Cardinal.{u}, IsWeaklyMahlo n μ ∧ μ.ord = o}

/-- `n`-Mahlo as in the paper: `M₀` = inaccessible cardinals, `Mₙ₊₁ = {κ ∈ M₀ : Mₙ ∩ κ is
stationary in κ}`. -/
def IsMahlo : Nat → Cardinal.{u} → Prop
  | 0, κ => κ.IsInaccessible
  | n + 1, κ => κ.IsInaccessible ∧
      StationaryIn κ {o | ∃ μ : Cardinal.{u}, IsMahlo n μ ∧ μ.ord = o}

theorem IsMahlo.isWeaklyMahlo : ∀ {n : Nat} {κ : Cardinal.{u}}, IsMahlo n κ → IsWeaklyMahlo n κ
  | 0, _, h => ⟨h.aleph0_lt, h.isRegular⟩
  | _ + 1, _, h => ⟨⟨h.1.aleph0_lt, h.1.isRegular⟩,
      h.2.mono fun _ ⟨μ, hμ, hμo⟩ => ⟨μ, hμ.isWeaklyMahlo, hμo⟩⟩

end BTBMS
