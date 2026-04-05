/-
  Section 3, Task 02a.
  A monotone function on [a,b] (real-valued) is Lebesgue measurable.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-- A monotone real-valued function is measurable. -/
theorem monotone_real_measurable {f : ℝ → ℝ} (hf : Monotone f) : Measurable f :=
  hf.measurable
