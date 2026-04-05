/-
  Section 12, Task 2.
  Prove the parallelogram law:
    ‖x + y‖² + ‖x - y‖² = 2‖x‖² + 2‖y‖²
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The parallelogram law in an inner product space. -/
theorem parallelogram_law' (x y : H) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖) + 2 * (‖y‖ * ‖y‖) := by
  simp only [← @real_inner_self_eq_norm_mul_norm H]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  have hcomm := @real_inner_comm H _ _ x y
  linarith
