/-
  Section 17, Task 10.
  In a Hilbert space H, weak convergence xₙ ⇀ x plus ‖xₙ‖ → ‖x‖
  implies strong convergence xₙ → x.
  Proof: ‖xₙ - x‖² = ‖xₙ‖² - 2Re⟨xₙ,x⟩ + ‖x‖² → ‖x‖² - 2‖x‖² + ‖x‖² = 0.
  (Radon-Riesz property, which holds in all uniformly convex spaces.)
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped InnerProductSpace
open Filter

/-- Radon–Riesz property in a real inner product space: weak convergence
    plus norm convergence implies strong convergence. -/
theorem weak_plus_norm_implies_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℕ → H} {x₀ : H}
    (hweak : ∀ y : H, Tendsto (fun n => ⟪x n, y⟫_ℝ) atTop (nhds ⟪x₀, y⟫_ℝ))
    (hnorm : Tendsto (fun n => ‖x n‖) atTop (nhds ‖x₀‖)) :
    Tendsto x atTop (nhds x₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  -- Show ‖x n - x₀‖² → 0
  have hnorm_sq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (nhds (‖x₀‖ ^ 2)) := hnorm.pow 2
  have hinner : Tendsto (fun n => ⟪x n, x₀⟫_ℝ) atTop (nhds (‖x₀‖ ^ 2)) := by
    have := hweak x₀; rwa [real_inner_self_eq_norm_sq] at this
  have hsq : Tendsto (fun n => ‖x n - x₀‖ ^ 2) atTop (nhds 0) := by
    have hcomb : Tendsto (fun n => ‖x n‖ ^ 2 - 2 * ⟪x n, x₀⟫_ℝ + ‖x₀‖ ^ 2)
        atTop (nhds (‖x₀‖ ^ 2 - 2 * ‖x₀‖ ^ 2 + ‖x₀‖ ^ 2)) :=
      (hnorm_sq.sub (hinner.const_mul 2)).add tendsto_const_nhds
    rw [show ‖x₀‖ ^ 2 - 2 * ‖x₀‖ ^ 2 + ‖x₀‖ ^ 2 = 0 from by ring] at hcomb
    exact hcomb.congr (fun n => (norm_sub_sq_real (x n) x₀).symm)
  -- Extract N from hsq at ε²
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hsq) (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  simp only [dist_zero_right] at h1
  rw [Real.norm_of_nonneg (sq_nonneg _)] at h1
  simp only [dist_zero_right]
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  nlinarith [sq_nonneg ‖x n - x₀‖, sq_nonneg ε, sq_abs ‖x n - x₀‖]
