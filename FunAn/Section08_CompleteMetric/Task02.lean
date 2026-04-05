/-
  Section 8, Task 02.
  Completeness of classical function spaces: ℓᵖ, ℓ_∞, c₀, etc.

  In Mathlib, the ℓᵖ spaces are complete when the codomain spaces are complete.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

open scoped ENNReal

/-- ℓᵖ spaces are complete when the codomain is complete (for p ≥ 1). -/
theorem completeness_of_classical_spaces
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    CompleteSpace (lp (fun _ : ℕ => ℝ) p) :=
  lp.completeSpace
