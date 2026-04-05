/-
  Section 17, Task 05.
  Fₙ(x) = n[x(1/n) + x(-1/n) - 2x(0)].

  (a) ‖Fₙ‖_{C²*} → 0: for f ∈ C², |Fₙ(f)| ≤ 2·sup|f''|/n.
  (b) Fₙ → 0 weakly in C¹[-1,1]*: for each C¹ function f, Fₙ(f) → 0.
  (c) Not weakly convergent in C[-1,1]*: Fₙ(√|·|) = 2√n → ∞.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter Set Real
open scoped Topology

noncomputable section

/-- The functional Fₙ applied to f: Fₙ(f) = n(f(1/n) + f(-1/n) - 2f(0)). -/
def Fn (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (f (1 / (n : ℝ)) + f (-(1 / (n : ℝ))) - 2 * f 0)

-- ============================================================================
-- Part (c): Fₙ(√|·|) = 2√n → ∞
-- ============================================================================

private lemma Fn_sqrt_abs (n : ℕ) (hn : 0 < n) :
    Fn (fun t => √|t|) n = 2 * √n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [Fn, abs_zero, sqrt_zero, mul_zero, sub_zero]
  rw [abs_of_nonneg (div_nonneg zero_le_one hn'.le)]
  rw [show |-(1 / (n : ℝ))| = 1 / n from by rw [abs_neg, abs_of_nonneg (div_nonneg zero_le_one hn'.le)]]
  rw [← two_mul (√(1 / ↑n)), one_div, sqrt_inv]
  -- Goal: ↑n * (2 * (√↑n)⁻¹) = 2 * √↑n
  -- Use: ↑n * (√↑n)⁻¹ = √↑n (i.e., n/√n = √n)
  have key : (↑n : ℝ) * (√↑n)⁻¹ = √↑n := by
    rw [← div_eq_mul_inv]; exact div_sqrt
  nlinarith

theorem section17_task05c_not_weak_in_C :
    Tendsto (fun n : ℕ => Fn (fun t => √|t|) n) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨max 1 (⌈(b / 2) ^ 2⌉₊ + 1), fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  rw [Fn_sqrt_abs n hn1]
  by_cases hb : b ≤ 0
  · linarith [mul_nonneg (two_pos.le) (sqrt_nonneg (n : ℝ))]
  · simp only [not_le] at hb
    have hb2 : (0 : ℝ) < b / 2 := by linarith
    have hsq : (b / 2) ^ 2 < ↑n := by
      have : n ≥ ⌈(b / 2) ^ 2⌉₊ + 1 := by omega
      calc (b / 2) ^ 2 ≤ ↑(⌈(b / 2) ^ 2⌉₊) := Nat.le_ceil _
        _ < ↑(⌈(b / 2) ^ 2⌉₊ + 1) := by push_cast; linarith
        _ ≤ (↑n : ℝ) := by exact_mod_cast ‹_›
    linarith [show b / 2 < √↑n from by rw [← sqrt_sq hb2.le]; exact sqrt_lt_sqrt (sq_nonneg _) hsq]

-- ============================================================================
-- Core MVT identity: Fₙ(f) = f'(c₁) - f'(c₂)
-- ============================================================================

private lemma Fn_eq_deriv_diff {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1)) :
    ∃ c₁ ∈ Ioo 0 (1 / (n : ℝ)),
    ∃ c₂ ∈ Ioo (-(1 / (n : ℝ))) 0,
    Fn f n = deriv f c₁ - deriv f c₂ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnn : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have h1n_pos : (0 : ℝ) < 1 / ↑n := div_pos one_pos hn'
  have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  have hI1 : Icc 0 (1 / (n : ℝ)) ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) h1n
  have hI2 : Icc (-(1 / (n : ℝ))) 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (neg_le_neg h1n) (by linarith)
  obtain ⟨c₁, hc₁, hc₁_eq⟩ := exists_deriv_eq_slope f h1n_pos
    (hfc.mono hI1) ((hf.mono hI1).mono Ioo_subset_Icc_self)
  obtain ⟨c₂, hc₂, hc₂_eq⟩ := exists_deriv_eq_slope f (by linarith : -(1 / (↑n : ℝ)) < 0)
    (hfc.mono hI2) ((hf.mono hI2).mono Ioo_subset_Icc_self)
  refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
  show ↑n * (f (1 / ↑n) + f (-(1 / ↑n)) - 2 * f 0) = deriv f c₁ - deriv f c₂
  -- From MVT: deriv f c₁ = (f(1/n) - f(0)) / (1/n - 0)
  have hc₁_s : deriv f c₁ = (f (1/↑n) - f 0) / (1/↑n) := by rwa [sub_zero] at hc₁_eq
  -- From MVT: deriv f c₂ = (f(0) - f(-1/n)) / (1/n)
  have hc₂_s : deriv f c₂ = (f 0 - f (-(1/↑n))) / (1/↑n) := by
    rwa [show (0 : ℝ) - -(1 / ↑n) = 1 / ↑n from by ring] at hc₂_eq
  have eq1 : f (1 / ↑n) - f 0 = deriv f c₁ * (1 / ↑n) := by
    rw [hc₁_s, div_mul_cancel₀ _ (ne_of_gt h1n_pos)]
  have eq2 : f 0 - f (-(1 / ↑n)) = deriv f c₂ * (1 / ↑n) := by
    rw [hc₂_s, div_mul_cancel₀ _ (ne_of_gt h1n_pos)]
  have h_sum : f (1 / ↑n) + f (-(1 / ↑n)) - 2 * f 0 = (deriv f c₁ - deriv f c₂) / ↑n := by
    rw [show (deriv f c₁ - deriv f c₂) / ↑n = deriv f c₁ * (1/↑n) - deriv f c₂ * (1/↑n) from by ring]
    linarith
  rw [h_sum, mul_div_cancel₀ _ hnn]

-- ============================================================================
-- Part (a): C² estimate |Fₙ(f)| ≤ 2M/n via MVT applied three times
-- ============================================================================

theorem section17_task05a_C2_bound
    {f : ℝ → ℝ} {M : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hf' : DifferentiableOn ℝ (deriv f) (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hfc' : ContinuousOn (deriv f) (Icc (-1) 1))
    (hbound : ∀ x ∈ Icc (-(1 : ℝ)) 1, |deriv (deriv f) x| ≤ M)
    {n : ℕ} (hn : 0 < n) :
    |Fn f n| ≤ 2 * M / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  obtain ⟨c₁, hc₁, c₂, hc₂, hkey⟩ := Fn_eq_deriv_diff hn hf hfc
  rw [hkey]
  have hlt : c₂ < c₁ := lt_trans hc₂.2 hc₁.1
  have hIc : Icc c₂ c₁ ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (by linarith [hc₂.1, neg_le_neg h1n]) (by linarith [hc₁.2])
  -- Apply MVT a third time: to deriv f on [c₂, c₁]
  obtain ⟨c₃, hc₃, hc₃_eq⟩ := exists_deriv_eq_slope (deriv f) hlt
    (hfc'.mono hIc) ((hf'.mono hIc).mono Ioo_subset_Icc_self)
  -- deriv (deriv f) c₃ = (deriv f c₁ - deriv f c₂) / (c₁ - c₂)
  -- So |deriv f c₁ - deriv f c₂| = |deriv (deriv f) c₃| * |c₁ - c₂|
  have hc₃_in : c₃ ∈ Icc (-1 : ℝ) 1 := hIc (Ioo_subset_Icc_self hc₃)
  have h_diff : deriv f c₁ - deriv f c₂ = deriv (deriv f) c₃ * (c₁ - c₂) := by
    have hsub : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hlt.ne'
    rw [hc₃_eq, div_mul_cancel₀ _ hsub]
  rw [h_diff, abs_mul]
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound 0 ⟨by linarith, by linarith⟩)
  have hc_diff_nn : 0 ≤ c₁ - c₂ := sub_nonneg.mpr hlt.le
  have hc_diff_le : c₁ - c₂ ≤ 2 / ↑n := by
    have h1 : c₁ - c₂ ≤ 1 / ↑n - (-(1 / ↑n)) :=
      sub_le_sub (le_of_lt hc₁.2) (le_of_lt hc₂.1)
    have h2 : (1 : ℝ) / ↑n - -(1 / ↑n) = 2 / ↑n := by ring
    linarith
  calc |deriv (deriv f) c₃| * |c₁ - c₂|
      ≤ M * |c₁ - c₂| := mul_le_mul_of_nonneg_right (hbound c₃ hc₃_in) (abs_nonneg _)
    _ = M * (c₁ - c₂) := by rw [abs_of_nonneg hc_diff_nn]
    _ ≤ M * (2 / ↑n) := mul_le_mul_of_nonneg_left hc_diff_le hM
    _ = 2 * M / ↑n := by ring

-- ============================================================================
-- Part (b): Fₙ(f) → 0 for C¹ functions
-- ============================================================================

theorem section17_task05b_weak_in_C1
    {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hfc' : ContinuousOn (deriv f) (Icc (-1) 1)) :
    Tendsto (fun n : ℕ => Fn f n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousWithinAt_iff.mp
    (hfc'.continuousWithinAt h0) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have h1n : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  obtain ⟨c₁, hc₁, c₂, hc₂, hkey⟩ := Fn_eq_deriv_diff hn1 hf hfc
  rw [hkey, dist_zero_right, Real.norm_eq_abs]
  have hI1 : Icc 0 (1 / (n : ℝ)) ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) h1n
  have hI2 : Icc (-(1 / (n : ℝ))) 0 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (neg_le_neg h1n) (by linarith)
  -- Key: dist c₁ 0 < δ and dist c₂ 0 < δ
  have hN_le : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have h_1n_lt_δ : 1 / (↑n : ℝ) < δ := by
    rw [div_lt_iff₀ hn']
    have h : 1 / δ < ↑n := lt_of_lt_of_le hN hN_le
    rw [div_lt_iff₀ hδ] at h
    linarith [mul_comm (↑n : ℝ) δ]
  have hc₁_dist : dist c₁ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc₁.1]; linarith [hc₁.2]
  have hc₂_dist : dist c₂ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hc₂.2]; linarith [hc₂.1]
  have hd1 := hδ_spec (hI1 (Ioo_subset_Icc_self hc₁)) hc₁_dist
  have hd2 := hδ_spec (hI2 (Ioo_subset_Icc_self hc₂)) hc₂_dist
  rw [Real.dist_eq] at hd1 hd2
  calc |deriv f c₁ - deriv f c₂|
      ≤ |deriv f c₁ - deriv f 0| + |deriv f 0 - deriv f c₂| := by
        rw [show deriv f c₁ - deriv f c₂ =
          (deriv f c₁ - deriv f 0) + (deriv f 0 - deriv f c₂) from by ring]
        exact abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith [abs_sub_comm (deriv f c₂) (deriv f 0)]
    _ = ε := add_halves ε
