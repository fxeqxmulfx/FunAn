/-
  Section 09, Task 05.
  ℝⁿ, C[a,b], ℓᵖ, s, C⁽ᵐ⁾, Lᵖ are separable.

  We prove separability of ℝⁿ, ℝ, and Lᵖ spaces.
-/
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open TopologicalSpace

/-- ℝ is separable. -/
instance : SeparableSpace ℝ := inferInstance

/-- ℝⁿ is separable (product of separable spaces). -/
instance : SeparableSpace (Fin n → ℝ) := inferInstance

/-- Lᵖ is separable (second-countable) when the measure and codomain are separable. -/
theorem Lp_separable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsSeparable μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    {p : ENNReal} [Fact (1 ≤ p)] [hp : Fact (p ≠ ⊤)] :
    SecondCountableTopology (MeasureTheory.Lp E p μ) :=
  MeasureTheory.Lp.SecondCountableTopology
