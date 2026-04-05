/-
  Section 10, Task 4.
  f(x) = π/2 + x - arctan(x) has no fixed point on ℝ.
  f(x) = x requires arctan(x) = π/2, but arctan(x) < π/2 for all x.
  This does not contradict Banach's theorem because (ℝ, f) is not
  a complete metric space with f as a contraction (f maps ℝ to ℝ
  but the fixed-point-free property shows it's not a contraction on ℝ).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-- arctan(x) < π/2 for all x, so f(x) = π/2 + x - arctan(x) > x,
    hence f has no fixed point. -/
theorem contraction_no_fixed_point_arctan (x : ℝ) :
    Real.arctan x < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two x
