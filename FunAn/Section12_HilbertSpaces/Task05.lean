/-
  Section 12, Task 5.
  Prove the real polarization identity:
    4⟨x, y⟩ = ‖x + y‖² - ‖x - y‖²
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real polarization identity. -/
theorem polarization_identity_real' (x y : H) :
    4 * @inner ℝ H _ x y = ‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖ := by
  simp only [← @real_inner_self_eq_norm_mul_norm H]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  have hcomm := @real_inner_comm H _ _ x y
  linarith
