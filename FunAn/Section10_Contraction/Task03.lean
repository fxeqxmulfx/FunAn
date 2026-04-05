/-
  Section 10, Task 3.
  Show that f(x) = (x² + 2) / (2x) is a contraction on [1, 2].
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

theorem contraction_sqrt2 (x y : ℝ) (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) :
    |((x ^ 2 + 2) / (2 * x)) - ((y ^ 2 + 2) / (2 * y))| ≤ (1 / 2) * |x - y| := by
  have hx0 : (0 : ℝ) < x := by linarith [hx.1]
  have hy0 : (0 : ℝ) < y := by linarith [hy.1]
  have h2xy : (0 : ℝ) < 2 * x * y := by positivity
  have key : (x ^ 2 + 2) / (2 * x) - (y ^ 2 + 2) / (2 * y) =
      (x - y) * (x * y - 2) / (2 * x * y) := by field_simp; ring
  rw [key]
  suffices h : |x * y - 2| ≤ x * y by
    rw [abs_div, abs_mul, abs_of_pos h2xy]
    rw [div_le_iff₀ h2xy]
    calc |x - y| * |x * y - 2|
        ≤ |x - y| * (x * y) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = 1 / 2 * |x - y| * (2 * x * y) := by ring
  rw [abs_le]
  exact ⟨by nlinarith [hx.1, hy.1], by nlinarith [hx.2, hy.2]⟩
