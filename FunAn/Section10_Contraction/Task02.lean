/-
  Section 10, Task 2.
  f(x) = √(1 + x²) satisfies |f(x) - f(y)| < |x - y| for x ≠ y,
  yet f has no fixed point.
  Proof of no fixed point: f(x) = x means √(1+x²) = x, so 1+x² = x²,
  giving 1 = 0 — contradiction.
  This doesn't contradict Banach because the contraction constant is not
  strictly less than 1 uniformly (sup |f'(x)| = 1).
-/
import Mathlib.Tactic

/-- √(1+x²) has no fixed point: √(1+x²) = x implies 1+x² = x², contradiction. -/
theorem sqrt_one_plus_sq_no_fixed_point : ¬ ∃ x : ℝ, Real.sqrt (1 + x ^ 2) = x := by
  push_neg; intro x
  by_cases hx : x ≤ 0
  · -- √(1+x²) > 0 ≥ x
    exact ne_of_gt (lt_of_le_of_lt hx (Real.sqrt_pos_of_pos (by positivity)))
  · -- √(1+x²) > x: square both sides
    push_neg at hx
    intro h
    have h1 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
    have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + x ^ 2)
    nlinarith [h ▸ h2]
