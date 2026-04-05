/-
  Section 4, Task 3.
  ∫₀¹ βᵢ(x)·βⱼ(x) dμ = 1/4 if i ≠ j, 1/2 if i = j,
  where βₖ is the k-th binary digit.

  Key principles:
  - For i ≠ j: βᵢ and βⱼ are independent {0,1}-valued random variables
    with E[βₖ] = 1/2. By independence: E[βᵢβⱼ] = E[βᵢ]·E[βⱼ] = 1/4.
  - For i = j: βᵢ² = βᵢ (since βᵢ ∈ {0,1}), so E[βᵢ²] = E[βᵢ] = 1/2.
-/
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

/-- For independent integrable random variables, E[X·Y] = E[X]·E[Y].
    Applied to binary digits: E[βᵢβⱼ] = E[βᵢ]·E[βⱼ] = 1/4 for i ≠ j. -/
theorem integral_mul_of_independent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXY : IndepFun X Y μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ :=
  hXY.integral_mul_eq_mul_integral hX hY

/-- If X takes values in {0, 1}, then X² = X pointwise.
    Applied to binary digits: E[βᵢ²] = E[βᵢ] = 1/2 for i = j. -/
theorem sq_eq_self_of_zero_one {Ω : Type*} {X : Ω → ℝ}
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) :
    ∀ ω, X ω ^ 2 = X ω := by
  intro ω
  rcases hX ω with h | h <;> simp [h]
