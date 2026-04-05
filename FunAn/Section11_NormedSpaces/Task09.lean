/-
  Section 11, Task 9.
  Show that the norms max(‖x₁‖, ‖x₂‖), ‖x₁‖+‖x₂‖, √(‖x₁‖²+‖x₂‖²)
  are equivalent on E × E.
-/
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic

variable {E : Type*} [NormedAddCommGroup E]

/-- max norm ≤ sum norm. -/
theorem max_le_sum (a b : E) : max ‖a‖ ‖b‖ ≤ ‖a‖ + ‖b‖ :=
  max_le (le_add_of_nonneg_right (norm_nonneg b)) (le_add_of_nonneg_left (norm_nonneg a))

/-- sum norm ≤ 2 * max norm. -/
theorem sum_le_two_max (a b : E) : ‖a‖ + ‖b‖ ≤ 2 * max ‖a‖ ‖b‖ := by
  linarith [le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖]

/-- max norm ≤ Euclidean norm: max(‖a‖, ‖b‖) ≤ √(‖a‖² + ‖b‖²). -/
theorem max_le_euclidean (a b : E) :
    max ‖a‖ ‖b‖ ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  apply max_le
  · calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
      _ ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖b‖])
  · calc ‖b‖ = Real.sqrt (‖b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg b)).symm
      _ ≤ Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])

/-- Euclidean norm ≤ sum norm: √(‖a‖² + ‖b‖²) ≤ ‖a‖ + ‖b‖. -/
theorem euclidean_le_sum (a b : E) :
    Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖a‖ + ‖b‖ := by
  rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)])

/-- Euclidean norm ≤ √2 · max norm. -/
theorem euclidean_le_sqrt2_max (a b : E) :
    Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ Real.sqrt 2 * max ‖a‖ ‖b‖ := by
  rw [← Real.sqrt_sq (by positivity : 0 ≤ max ‖a‖ ‖b‖),
      ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  have h1 : ‖a‖ ^ 2 ≤ max ‖a‖ ‖b‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg a) (le_max_left ‖a‖ ‖b‖) 2
  have h2 : ‖b‖ ^ 2 ≤ max ‖a‖ ‖b‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg b) (le_max_right ‖a‖ ‖b‖) 2
  linarith
