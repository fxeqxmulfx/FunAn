/-
  Section 21, Task 2.
  A(ξ₁,ξ₂,...) = (0, ξ₁/1, ξ₂/2, ..., ξₙ/n, ...) is compact on ℓ².
  This is a diagonal operator with entries aₖ = 1/(k+1) → 0.
  By the diagonal compactness criterion (Task04), it is compact.
-/
import FunAn.Section21_CompactOperators.Task04
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open scoped ENNReal
open Filter

/-- The diagonal operator with entries 1/(k+1) is compact on ℓ². -/
theorem weighted_shift_compact : ∃ A : lp (fun _ : ℕ => ℝ) 2 → lp (fun _ : ℕ => ℝ) 2,
    IsCompactOperator A ∧
    ∀ (x : lp (fun _ : ℕ => ℝ) 2) (k : ℕ),
      (A x : ℕ → ℝ) k = (1 / ((k : ℝ) + 1)) * (x : ℕ → ℝ) k := by
  set a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ha : ∃ C, ∀ k, |a k| ≤ C := ⟨1, fun k => by
    simp only [a, one_div]
    have hk : (0 : ℝ) < (↑k + 1) := by positivity
    rw [abs_of_nonneg (inv_nonneg.mpr hk.le)]
    exact inv_le_one_of_one_le₀ (by linarith)⟩
  refine ⟨_, (diagonal_operator_compact_iff_tendsto_zero a ha).mpr ?_, fun x k => rfl⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat
