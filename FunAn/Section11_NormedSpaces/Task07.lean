/-
  Section 11, Task 7.
  Prove that the sup norm and L¹ norm are not equivalent on C[0,1].

  Proof: for f(t) = tⁿ: ‖f‖_sup = 1, ‖f‖_L1 = 1/(n+1) → 0.
  So no C > 0 satisfies 1 ≤ C/(n+1) for all n.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-- No constant C satisfies 1 ≤ C / (n+1) for all n ∈ ℕ. -/
theorem no_constant_bound :
    ¬ ∃ (C : ℝ), 0 < C ∧ ∀ (n : ℕ), (1 : ℝ) ≤ C / (↑n + 1) := by
  intro ⟨C, hC, h⟩
  have h_ceil := h ⌈C⌉₊
  have : (↑⌈C⌉₊ : ℝ) + 1 > 0 := by positivity
  rw [le_div_iff₀ this] at h_ceil
  linarith [Nat.le_ceil C]
