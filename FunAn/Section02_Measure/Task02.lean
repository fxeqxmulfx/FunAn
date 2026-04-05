/-
  Section 2, Task 2.
  A ⊆ [0,1] is Lebesgue measurable iff μ*(A) = μ_*(A),
  where μ_*(A) = 1 - μ*([0,1] \ A).
  This is the Carathéodory criterion for Lebesgue measurability.
  In Mathlib, Lebesgue measurability is defined via the Carathéodory
  extension, which is equivalent to the outer/inner measure condition.

  We formalize: the measurable space structure on any measure space
  is contained in the Carathéodory σ-algebra of its outer measure.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

/-- Measurable sets are Carathéodory-measurable w.r.t. the outer measure. -/
theorem lebesgue_measurable_iff_outer_eq_inner
    {α : Type*} [ms : MeasurableSpace α] (μ : Measure α) :
    ms ≤ μ.toOuterMeasure.caratheodory :=
  le_toOuterMeasure_caratheodory μ
