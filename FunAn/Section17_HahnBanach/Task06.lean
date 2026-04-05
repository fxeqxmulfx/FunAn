/-
  Section 17, Task 06.
  Gₙ(f) = n²[f(1/n) + f(-1/n) - 2f(0)].

  (a) |Gₙ(f) - f''(0)| ≤ M/n for C³ (norm convergence in C³*).
  (b) Gₙ(f) → f''(0) for C² functions (weak convergence in C²*).
  (c) Not weakly convergent in C¹*: Gₙ(|·|^{3/2}) = 2√n → ∞.
-/
import FunAn.Section17_HahnBanach.Task05
import Mathlib.Tactic

open Filter Set Real
open scoped Topology

noncomputable section

/-- The functional Gₙ: Gₙ(f) = n²(f(1/n) + f(-1/n) - 2f(0)).
    Second-order symmetric difference quotient (approximates f''(0)). -/
def Gn (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (f (1 / (n : ℝ)) + f (-(1 / (n : ℝ))) - 2 * f 0)

-- ============================================================================
-- Part (c): Gₙ(|·|^{3/2}) = 2√n → ∞ (not weak in C¹)
-- ============================================================================

private lemma Gn_abs_three_halves (n : ℕ) (hn : 0 < n) :
    Gn (fun t => |t| * √|t|) n = 2 * √↑n := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  simp only [Gn, abs_zero, mul_zero, sqrt_zero, sub_zero]
  have h1 : |1 / (↑n : ℝ)| = 1 / ↑n := abs_of_nonneg (by positivity)
  rw [h1, show |-(1 / (↑n : ℝ))| = 1 / ↑n from by rw [abs_neg]; exact h1, ← two_mul,
      one_div, sqrt_inv]
  have : (↑n : ℝ) ≠ 0 := ne_of_gt hn'
  have : √(↑n : ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn')
  field_simp
  nlinarith [sq_sqrt hn'.le]

/-- Gₙ(|·|^{3/2}) = 2√n → ∞: witnesses non-convergence.
    The function |x|^{3/2} = |x|·√|x| is C¹ (derivative (3/2)√|x|·sgn(x)),
    so Gₙ is not weakly convergent in C¹[-1,1]*. -/
theorem section17_task06c_not_weak_in_C1 :
    Tendsto (fun n : ℕ => Gn (fun t => |t| * √|t|) n) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨max 1 (⌈(b / 2) ^ 2⌉₊ + 1), fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  rw [Gn_abs_three_halves n hn1]
  by_cases hb : b ≤ 0
  · linarith [mul_nonneg two_pos.le (sqrt_nonneg (↑n : ℝ))]
  · push Not at hb
    have hb2 : (0 : ℝ) < b / 2 := by linarith
    have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn1
    have hsq : (b / 2) ^ 2 < (↑n : ℝ) := by
      have : n ≥ ⌈(b / 2) ^ 2⌉₊ + 1 := by omega
      calc (b / 2) ^ 2 ≤ ↑(⌈(b / 2) ^ 2⌉₊) := Nat.le_ceil _
        _ < ↑(⌈(b / 2) ^ 2⌉₊ + 1) := by push_cast; linarith
        _ ≤ (↑n : ℝ) := by exact_mod_cast ‹_›
    linarith [show b / 2 < √(↑n : ℝ) from by
      rw [← sqrt_sq hb2.le]; exact sqrt_lt_sqrt (sq_nonneg _) hsq]

-- ============================================================================
-- Part (b): Gₙ(f) → f''(0) for C² functions (via Cauchy MVT + MVT)
-- ============================================================================

/-- Key identity: Gₙ(f) = f''(d) for some d ∈ (-1/n, 1/n).
    Step 1: Cauchy MVT on F(x)=f(x)+f(-x), G(x)=x² gives Gₙ(f) = (f'(c)-f'(-c))/(2c).
    Step 2: MVT on f' on [-c,c] gives (f'(c)-f'(-c))/(2c) = f''(d). -/
private lemma Gn_eq_second_deriv {f : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hf' : DifferentiableOn ℝ (deriv f) (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hfc' : ContinuousOn (deriv f) (Icc (-1) 1)) :
    ∃ d ∈ Ioo (-(1 / (↑n : ℝ))) (1 / (↑n : ℝ)),
      Gn f n = deriv (deriv f) d := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hne : (↑n : ℝ) ≠ 0 := ne_of_gt hn'
  have h1n_pos : (0 : ℝ) < 1 / ↑n := div_pos one_pos hn'
  have h1n_le : 1 / (↑n : ℝ) ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  -- Subset inclusions
  have hI : Icc 0 (1 / (↑n : ℝ)) ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (by linarith) h1n_le
  have hIn : Icc (-(1 / (↑n : ℝ))) 0 ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (neg_le_neg h1n_le) (by linarith)
  -- F(x) = f(x) + f(-x) is continuous on [0, 1/n]
  have hFc : ContinuousOn (fun x => f x + f (-x)) (Icc 0 (1 / ↑n)) :=
    (hfc.mono hI).add ((hfc.mono hIn).comp continuousOn_neg
      (fun x hx => ⟨neg_le_neg hx.2, by linarith [hx.1]⟩))
  -- F differentiable on (0, 1/n)
  have hFd : DifferentiableOn ℝ (fun x => f x + f (-x)) (Ioo 0 (1 / ↑n)) :=
    ((hf.mono hI).mono Ioo_subset_Icc_self).add
      (((hf.mono hIn).mono Ioo_subset_Icc_self).comp
        (differentiable_neg.differentiableOn)
        (fun x hx => ⟨by linarith [hx.2], neg_lt_zero.mpr hx.1⟩))
  -- Step 1: Apply Cauchy's MVT
  obtain ⟨c, hc, hc_eq⟩ := exists_ratio_deriv_eq_ratio_slope
    (fun x => f x + f (-x)) h1n_pos hFc hFd
    (fun x => x ^ 2) (by fun_prop) (differentiable_pow 2).differentiableOn
  have hc_pos : (0 : ℝ) < c := hc.1
  have hc_lt : c < 1 / ↑n := hc.2
  have h2c_pos : (0 : ℝ) < 2 * c := by linarith
  have h2c_ne : (2 * c : ℝ) ≠ 0 := ne_of_gt h2c_pos
  -- c and -c are in (-1, 1)
  have hc11 : c ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith [h1n_le]⟩
  have hnc11 : -c ∈ Ioo (-1 : ℝ) 1 := ⟨by nlinarith [h1n_le], by linarith⟩
  have hda : DifferentiableAt ℝ f c :=
    hf.differentiableAt (Icc_mem_nhds hc11.1 hc11.2)
  have hdna : DifferentiableAt ℝ f (-c) :=
    hf.differentiableAt (Icc_mem_nhds hnc11.1 hnc11.2)
  -- Compute HasDerivAt for F and G at c (to rewrite deriv in hc_eq)
  have hF_at : HasDerivAt (fun x => f x + f (-x)) (deriv f c - deriv f (-c)) c := by
    have h1 := hda.hasDerivAt
    have h2 : HasDerivAt (fun x => f (-x)) (-deriv f (-c)) c := by
      have := hdna.hasDerivAt.comp c (hasDerivAt_neg c)
      simpa [Function.comp_def] using this
    exact h1.add h2
  have hG_at : HasDerivAt (fun x : ℝ => x ^ 2) (2 * c) c := by
    have := hasDerivAt_pow 2 c; simpa [pow_one] using this
  -- Replace derivatives in Cauchy MVT equation
  rw [hF_at.deriv, hG_at.deriv] at hc_eq
  -- hc_eq now has form involving function values and derivative values
  -- Clean it up to: (1/n)^2 * (f'(c)-f'(-c)) = (f(1/n)+f(-1/n)-2f(0)) * 2c
  have h_cauchy : (1 / ↑n : ℝ) ^ 2 * (deriv f c - deriv f (-c)) =
      (f (1 / ↑n) + f (-(1 / ↑n)) - 2 * f 0) * (2 * c) := by
    have := hc_eq
    simp only [neg_zero] at this
    nlinarith
  -- Step 2: Apply MVT to deriv f on [-c, c]
  have hIc : Icc (-c) c ⊆ Icc (-1 : ℝ) 1 :=
    Icc_subset_Icc (by linarith [hnc11.1]) (by linarith [hc11.2])
  obtain ⟨d, hd, hd_eq⟩ := exists_deriv_eq_slope (deriv f) (by linarith : -c < c)
    (hfc'.mono hIc) ((hf'.mono hIc).mono Ioo_subset_Icc_self)
  -- hd_eq: deriv (deriv f) d = (deriv f c - deriv f (-c)) / (c - (-c))
  -- Combine: f'(c)-f'(-c) = f''(d) * 2c, substitute into h_cauchy
  have h_sub : c - (-c) = 2 * c := by ring
  have h_diff_eq : deriv f c - deriv f (-c) = deriv (deriv f) d * (2 * c) := by
    rw [hd_eq, h_sub, div_mul_cancel₀ _ h2c_ne]
  -- From h_cauchy with substitution: (1/n)^2 * f''(d) * 2c = S * 2c
  -- Cancel 2c: (1/n)^2 * f''(d) = S
  -- So Gn = n^2 * S = n^2 * (1/n)^2 * f''(d) = f''(d)
  refine ⟨d, ⟨by linarith [hd.1], by linarith [hd.2]⟩, ?_⟩
  simp only [Gn]
  have h_S : f (1 / ↑n) + f (-(1 / ↑n)) - 2 * f 0 =
      (1 / ↑n) ^ 2 * deriv (deriv f) d := by
    have h := h_cauchy
    rw [h_diff_eq] at h
    -- h: (1/n)^2 * (f''(d) * 2c) = S * 2c
    nlinarith
  rw [h_S]
  have : (↑n : ℝ) ^ 2 * ((1 / ↑n) ^ 2 * deriv (deriv f) d) = deriv (deriv f) d := by
    field_simp
  linarith

/-- Weak convergence in C²*: Gₙ(f) → f''(0) for each C² function.
    Proof: Gₙ(f) = f''(dₙ) with dₙ → 0, so result follows from continuity of f''. -/
theorem section17_task06b_weak_in_C2
    {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hf' : DifferentiableOn ℝ (deriv f) (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hfc' : ContinuousOn (deriv f) (Icc (-1) 1))
    (hfc'' : ContinuousOn (deriv (deriv f)) (Icc (-1) 1)) :
    Tendsto (fun n : ℕ => Gn f n) atTop (nhds (deriv (deriv f) 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h0_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousWithinAt_iff.mp
    (hfc''.continuousWithinAt h0_mem) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn1
  have h1n_le : 1 / (↑n : ℝ) ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  obtain ⟨d, hd, hGn_eq⟩ := Gn_eq_second_deriv hn1 hf hf' hfc hfc'
  rw [hGn_eq]
  have hd_mem : d ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hd.1, neg_le_neg h1n_le], by linarith [hd.2, h1n_le]⟩
  have hN_le : (N : ℝ) ≤ ↑n := by exact_mod_cast (show N ≤ n by omega)
  have h_1n_lt_δ : 1 / (↑n : ℝ) < δ := by
    rw [div_lt_iff₀ hn']
    have : 1 / δ < ↑n := lt_of_lt_of_le hN hN_le
    rwa [div_lt_iff₀ hδ, mul_comm] at this
  exact hδ_spec hd_mem (by
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩)

-- ============================================================================
-- Part (a): |Gₙ(f) - f''(0)| ≤ M/n for C³ (norm convergence in C³*)
-- ============================================================================

/-- C³ bound: |Gₙ(f) - f''(0)| ≤ M/n where M = sup|f'''|.
    From key identity Gₙ(f) = f''(d) with |d| < 1/n, MVT gives
    |f''(d) - f''(0)| ≤ |f'''(ξ)|·|d| ≤ M/n. -/
theorem section17_task06a_C3_bound
    {f : ℝ → ℝ} {M : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (-1) 1))
    (hf' : DifferentiableOn ℝ (deriv f) (Icc (-1) 1))
    (hf'' : DifferentiableOn ℝ (deriv (deriv f)) (Icc (-1) 1))
    (hfc : ContinuousOn f (Icc (-1) 1))
    (hfc' : ContinuousOn (deriv f) (Icc (-1) 1))
    (hfc'' : ContinuousOn (deriv (deriv f)) (Icc (-1) 1))
    (hbound : ∀ x ∈ Icc (-(1 : ℝ)) 1, |deriv (deriv (deriv f)) x| ≤ M)
    {n : ℕ} (hn : 0 < n) :
    |Gn f n - deriv (deriv f) 0| ≤ M / ↑n := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have h1n_le : 1 / (↑n : ℝ) ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast (by omega : 1 ≤ n)
  have h0_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hbound 0 h0_mem)
  obtain ⟨d, hd, hGn_eq⟩ := Gn_eq_second_deriv hn hf hf' hfc hfc'
  rw [hGn_eq]
  have hd_mem : d ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hd.1, neg_le_neg h1n_le], by linarith [hd.2, h1n_le]⟩
  -- Apply MVT to f'' between 0 and d to bound |f''(d) - f''(0)|
  by_cases hd0 : 0 ≤ d
  · -- Case d ≥ 0
    rcases eq_or_lt_of_le hd0 with rfl | hd_pos
    · simp [div_nonneg hM_nn hn'.le]
    · have hI0d : Icc 0 d ⊆ Icc (-1 : ℝ) 1 :=
        Icc_subset_Icc (by linarith) (by linarith [hd.2, h1n_le])
      obtain ⟨ξ, hξ, hξ_eq⟩ := exists_deriv_eq_slope (deriv (deriv f)) hd_pos
        (hfc''.mono hI0d) ((hf''.mono hI0d).mono Ioo_subset_Icc_self)
      rw [sub_zero] at hξ_eq
      have hξ_mem : ξ ∈ Icc (-1 : ℝ) 1 := hI0d (Ioo_subset_Icc_self hξ)
      have h_diff : deriv (deriv f) d - deriv (deriv f) 0 =
          deriv (deriv (deriv f)) ξ * d := by
        rw [hξ_eq]; field_simp
      rw [h_diff, abs_mul]
      calc |deriv (deriv (deriv f)) ξ| * |d|
          ≤ M * |d| := by apply mul_le_mul_of_nonneg_right (hbound ξ hξ_mem) (abs_nonneg _)
        _ = M * d := by rw [abs_of_nonneg hd0]
        _ ≤ M * (1 / ↑n) := by apply mul_le_mul_of_nonneg_left (le_of_lt hd.2) hM_nn
        _ = M / ↑n := by ring
  · -- Case d < 0
    push Not at hd0
    have hId0 : Icc d 0 ⊆ Icc (-1 : ℝ) 1 :=
      Icc_subset_Icc (by linarith [hd.1, neg_le_neg h1n_le]) (by linarith)
    obtain ⟨ξ, hξ, hξ_eq⟩ := exists_deriv_eq_slope (deriv (deriv f)) hd0
      (hfc''.mono hId0) ((hf''.mono hId0).mono Ioo_subset_Icc_self)
    have hξ_mem : ξ ∈ Icc (-1 : ℝ) 1 := hId0 (Ioo_subset_Icc_self hξ)
    have h_diff : deriv (deriv f) d - deriv (deriv f) 0 =
        deriv (deriv (deriv f)) ξ * d := by
      have hne : (0 : ℝ) - d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hd0)
      rw [show deriv (deriv f) d - deriv (deriv f) 0 =
        -(deriv (deriv f) 0 - deriv (deriv f) d) from by ring, hξ_eq]
      field_simp; ring
    rw [h_diff, abs_mul]
    calc |deriv (deriv (deriv f)) ξ| * |d|
        ≤ M * |d| := by apply mul_le_mul_of_nonneg_right (hbound ξ hξ_mem) (abs_nonneg _)
      _ = M * (-d) := by rw [abs_of_neg hd0]
      _ ≤ M * (1 / ↑n) := by apply mul_le_mul_of_nonneg_left _ hM_nn; linarith [hd.1]
      _ = M / ↑n := by ring
