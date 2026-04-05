/-
  Section 2, Task 4.
  T = {(x, 1/2) : 0 ≤ x < 1} is not measurable w.r.t. the semiring
  of rectangles [a,b) × [c,d), and has outer measure 0.

  The outer measure is 0 because T ⊆ [0,1) × {1/2}, and {1/2} has
  Lebesgue measure 0 (no atoms), so the product measure is 0.
  Since T has measure 0, it is Lebesgue-measurable (as a null set),
  but it is not in the semiring of half-open rectangles itself.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

open MeasureTheory Set

/-- T = {(x, 1/2) : 0 ≤ x < 1} has product Lebesgue measure 0.
    This is the outer measure of T w.r.t. the rectangle premeasure:
    T ⊆ [0,1) × [1/2-ε, 1/2+ε) for any ε > 0, with measure 2ε → 0. -/
theorem section02_task04 :
    volume (Ico (0 : ℝ) 1 ×ˢ ({1/2} : Set ℝ)) = 0 := by
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    Measure.prod_prod, Real.volume_singleton, mul_zero]
