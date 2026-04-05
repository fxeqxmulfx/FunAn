/-
  Section 5, Task 1.
  Prove that a function of bounded variation on [a, b] can be represented
  as the difference of two increasing functions (Jordan decomposition).
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-- Jordan decomposition: every BV function is the difference of two monotone functions. -/
theorem jordan_decomposition_bv {a b : ℝ} (_hab : a ≤ b) (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc a b)) :
    ∃ (g₁ g₂ : ℝ → ℝ), MonotoneOn g₁ (Set.Icc a b) ∧
      MonotoneOn g₂ (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, f x = g₁ x - g₂ x := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  exact ⟨p, q, hp, hq, fun x hx => by simp [hpq]⟩
