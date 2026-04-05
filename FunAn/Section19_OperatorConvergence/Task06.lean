/-
  Section 19, Task 06.
  (a) If Aₙ → A in weak operator topology and xₙ → x strongly,
      then Aₙxₙ → Ax weakly.

  Proof: Fix f ∈ F*. By Banach-Steinhaus, ‖f ∘ Aₙ‖ is uniformly bounded (say ≤ C),
  since f(Aₙy) converges for each y. Then:
    |f(Aₙxₙ) - f(A₀x₀)| ≤ |f(Aₙ(xₙ-x₀))| + |f(Aₙx₀) - f(A₀x₀)|
                           ≤ C·‖xₙ-x₀‖ + |f(Aₙx₀) - f(A₀x₀)| → 0.

  (b) Counterexample: strong operator Aₙ → 0 + weak xₙ → 0 but Aₙxₙ = e₁ ≠ 0.
      Take Aₙy = ⟨y, eₙ⟩·e₁ and xₙ = eₙ in ℓ².
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Tactic

open Filter

/-- Weak operator + strong vector convergence ⟹ weak convergence.
    If f(Aₙy) → f(A₀y) for all y ∈ E, f ∈ F*, and ‖xₙ − x₀‖ → 0,
    then f(Aₙxₙ) → f(A₀x₀) for all f ∈ F*. -/
theorem section19_task06
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℕ → E →L[ℝ] F} {A₀ : E →L[ℝ] F}
    (hop : ∀ (y : E) (f : F →L[ℝ] ℝ),
      Tendsto (fun n => f (A n y)) atTop (nhds (f (A₀ y))))
    {x : ℕ → E} {x₀ : E} (hx : Tendsto x atTop (nhds x₀)) :
    ∀ (f : F →L[ℝ] ℝ),
      Tendsto (fun n => f (A n (x n))) atTop (nhds (f (A₀ x₀))) := by
  intro f
  -- Uniform bound on ‖f ∘ Aₙ‖ by Banach-Steinhaus
  have hbdd : ∃ C, ∀ n, ‖f.comp (A n)‖ ≤ C := by
    apply banach_steinhaus; intro y
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hop y f) 1 one_pos
    refine ⟨‖f (A₀ y)‖ + 1 + ∑ i ∈ Finset.range N, ‖f (A i y)‖, fun n => ?_⟩
    simp only [ContinuousLinearMap.comp_apply]
    by_cases hn : N ≤ n
    · have h1 : ‖f (A n y) - f (A₀ y)‖ < 1 := by
        have := hN n hn; rwa [dist_eq_norm] at this
      have h2 : ‖f (A n y)‖ ≤ ‖f (A₀ y)‖ + 1 :=
        calc ‖f (A n y)‖ = ‖f (A₀ y) + (f (A n y) - f (A₀ y))‖ := by
              rw [add_sub_cancel]
          _ ≤ ‖f (A₀ y)‖ + ‖f (A n y) - f (A₀ y)‖ := norm_add_le _ _
          _ ≤ ‖f (A₀ y)‖ + 1 := by linarith
      linarith [Finset.sum_nonneg (s := Finset.range N)
        (fun i _ => norm_nonneg (f (A i y)))]
    · push Not at hn
      linarith [Finset.single_le_sum (s := Finset.range N)
        (f := fun i => ‖f (A i y)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hn), norm_nonneg (f (A₀ y))]
  obtain ⟨C, hC⟩ := hbdd
  -- Decompose: f(Aₙxₙ) - f(A₀x₀) = f(Aₙ(xₙ-x₀)) + (f(Aₙx₀) - f(A₀x₀))
  apply Metric.tendsto_atTop.mpr; intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (hop x₀ f) (ε/2) (half_pos hε)
  have hC1 : (0:ℝ) < C + 1 := by
    linarith [le_trans (norm_nonneg (f.comp (A 0))) (hC 0)]
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hx (ε/(2*(C+1)))
    (div_pos hε (mul_pos two_pos hC1))
  exact ⟨max N₁ N₂, fun n hn => by
    have d1 := hN₁ n (le_of_max_le_left hn)
    have d2 := hN₂ n (le_of_max_le_right hn)
    simp only [dist_eq_norm] at d1 d2 ⊢
    calc ‖f (A n (x n)) - f (A₀ x₀)‖
        = ‖f (A n (x n - x₀)) + (f (A n x₀) - f (A₀ x₀))‖ := by
          congr 1; simp [map_sub]
      _ ≤ ‖f (A n (x n - x₀))‖ + ‖f (A n x₀) - f (A₀ x₀)‖ := norm_add_le _ _
      _ ≤ C * ‖x n - x₀‖ + ‖f (A n x₀) - f (A₀ x₀)‖ := by
          have h1 := (f.comp (A n)).le_opNorm (x n - x₀)
          simp only [ContinuousLinearMap.comp_apply] at h1
          have h2 := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg (x n - x₀))
          linarith
      _ ≤ C * (ε/(2*(C+1))) + ε/2 := by
          have hC0 : (0:ℝ) ≤ C :=
            le_trans (norm_nonneg (f.comp (A 0))) (hC 0)
          linarith [mul_le_mul_of_nonneg_left d2.le hC0]
      _ < ε := by
          suffices C * (ε/(2*(C+1))) < ε/2 by linarith
          calc C * (ε/(2*(C+1)))
              = C*ε / (2*(C+1)) := by ring
            _ < (C+1)*ε / (2*(C+1)) := by
                apply div_lt_div_of_pos_right _ (by linarith : 0 < 2*(C+1))
                exact mul_lt_mul_of_pos_right (by linarith) hε
            _ = ε/2 := by field_simp⟩
