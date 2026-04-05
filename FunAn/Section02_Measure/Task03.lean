/-
  Section 2, Task 3.
  Prove that Borel sets are Lebesgue measurable.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory

/-- Every Borel set in ℝ is Lebesgue measurable.
    In Mathlib, ℝ has `BorelSpace ℝ`, meaning the measurable space structure
    on ℝ is exactly the Borel σ-algebra. Therefore every Borel-measurable set
    is automatically measurable (and hence Lebesgue measurable). -/
theorem borel_measurableSet_lebesgue {s : Set ℝ}
    (hs : MeasurableSet[borel ℝ] s) :
    MeasurableSet s := by
  exact Real.borelSpace.measurable_eq ▸ hs
