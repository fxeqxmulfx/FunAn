/-
  Section 3, Task 08.
  If f is differentiable everywhere on [0,1], then f' is Lebesgue measurable.
  In fact, deriv f is always measurable (even without differentiability).
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-- The derivative of any function ℝ → ℝ is measurable. -/
theorem deriv_measurable (f : ℝ → ℝ) : Measurable (deriv f) :=
  measurable_deriv f
