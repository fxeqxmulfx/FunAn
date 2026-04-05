/-
  Section 2, Task 1.
  Let A ⊂ [0,1]. Define inner measure μ_*(A) = 1 - μ*([0,1] \ A).
  Prove that μ*(A) ≥ μ_*(A).
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic

/-- For any A ⊂ [0,1], the outer measure satisfies μ*(A) ≥ μ_*(A)
    where μ_*(A) = 1 - μ*([0,1] \ A).
    Equivalently: μ*(A) + μ*([0,1] \ A) ≥ 1 = μ*([0,1]). -/
theorem outer_measure_ge_inner_measure
    (μ : MeasureTheory.OuterMeasure ℝ) (A : Set ℝ) (hA : A ⊆ Set.Icc 0 1) :
    μ (Set.Icc 0 1) ≤ μ A + μ (Set.Icc 0 1 \ A) := by
  calc μ (Set.Icc 0 1)
      = μ (A ∪ (Set.Icc 0 1 \ A)) := by
        congr 1; exact (Set.union_diff_cancel hA).symm
    _ ≤ μ A + μ (Set.Icc 0 1 \ A) := MeasureTheory.measure_union_le A _
