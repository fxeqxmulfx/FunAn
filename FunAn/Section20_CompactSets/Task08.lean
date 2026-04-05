/-
  Section 20, Task 8.
  The parallelepiped P = {x ∈ ℓ² : |xₖ| ≤ 1/(k+1)} is compact in ℓ².
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open scoped ENNReal
open Filter

private lemma memℓp_of_coord_le {x : ℕ → ℝ}
    (hx : ∀ k : ℕ, |x k| ≤ 1 / ((k : ℝ) + 1)) : Memℓp x 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat]
  exact ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ) < 2)).comp_injective
    Nat.succ_injective |>.congr fun k => by simp [Nat.cast_succ, one_div, sq]).of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) fun k =>
    Real.rpow_le_rpow (norm_nonneg _) (hx k) (by norm_num)

private lemma summable_sq_bound : Summable (fun k : ℕ => (2 / ((k : ℝ) + 1)) ^ 2) := by
  simp_rw [div_pow]; apply Summable.mul_left
  exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ) < 2)).comp_injective
    Nat.succ_injective |>.congr fun k => by simp [Nat.cast_succ, one_div, sq]

-- ‖f‖² = ∑' k, (f k)² via inner product on ℓ²
private lemma lp_norm_sq_eq_tsum (f : lp (fun _ : ℕ => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' k, (f k) ^ 2 := by
  rw [sq, ← real_inner_self_eq_norm_mul_norm, lp.inner_eq_tsum]
  congr 1; ext k; rw [real_inner_self_eq_norm_mul_norm, Real.norm_eq_abs]
  change |f k| * |f k| = (f k : ℝ) ^ 2; rw [← sq_abs]; ring

theorem parallelepiped_compact_in_l2 :
    IsCompact {x : lp (fun _ : ℕ => ℝ) 2 |
      ∀ k : ℕ, |x k| ≤ 1 / (k + 1 : ℝ)} := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [isCompact_iff_isSeqCompact]; intro x hx
  obtain ⟨y, hyS, φ, hφ, hconv⟩ :=
    (isCompact_pi_infinite (fun k : ℕ => isCompact_Icc)).tendsto_subseq
      (fun n k => abs_le.mp (hx n k) : ∀ n, (↑(x n) : ℕ → ℝ) ∈ _)
  have hybd : ∀ k : ℕ, |y k| ≤ 1 / ((k:ℝ)+1) := fun k => abs_le.mpr (hyS k)
  set y' : lp (fun _ : ℕ => ℝ) 2 := ⟨y, memℓp_of_coord_le hybd⟩
  refine ⟨y', hybd, φ, hφ, ?_⟩
  -- ‖d_n‖² = ∑' k, (d_n k)²
  have hnorm_sq : ∀ n, ‖x (φ n) - y'‖ ^ 2 =
      ∑' k, ((x (φ n) : ℕ → ℝ) k - y k) ^ 2 := fun n => by
    have := lp_norm_sq_eq_tsum (x (φ n) - y')
    simp only [lp.coeFn_sub, Pi.sub_apply, y'] at this; exact this
  -- Tannery: ∑' k, (d_n k)² → 0
  have hsq : Tendsto (fun n => ∑' k, ((x (φ n) : ℕ → ℝ) k - y k) ^ 2) atTop (nhds 0) := by
    have hpw : ∀ k, Tendsto (fun n => ((x (φ n) : ℕ → ℝ) k - y k) ^ 2) atTop (nhds 0) := by
      intro k
      have hk := ((continuous_apply k).tendsto y).comp hconv
      have hsub : Tendsto (fun n => (x (φ n) : ℕ → ℝ) k - y k) atTop (nhds 0) := by
        have := hk.sub (tendsto_const_nhds (x := y k)); rwa [sub_self] at this
      have := ((continuous_pow 2).tendsto 0).comp hsub
      simp only [Function.comp_def, zero_pow two_ne_zero] at this; exact this
    have hbd : ∀ᶠ n in atTop, ∀ k,
        ‖((x (φ n) : ℕ → ℝ) k - y k) ^ 2‖ ≤ (2 / ((k : ℝ) + 1)) ^ 2 :=
      Eventually.of_forall fun n k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        gcongr
        have h3 := norm_sub_le ((x (φ n) : ℕ → ℝ) k) (y k)
        simp only [Real.norm_eq_abs] at h3
        have h1 := hx (φ n) k; have h2 := hybd k
        have h4 : (1 : ℝ) / ((k:ℝ)+1) + 1 / ((k:ℝ)+1) = 2 / ((k:ℝ)+1) := by ring
        linarith
    simpa [tsum_zero] using tendsto_tsum_of_dominated_convergence summable_sq_bound hpw hbd
  -- ‖d_n‖² → 0 ⟹ ‖d_n‖ → 0 ⟹ x(φ n) → y'
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (show Tendsto (fun n => ‖x (φ n) - y'‖ ^ 2)
    atTop (nhds 0) from by simp_rw [hnorm_sq]; exact hsq) (ε ^ 2) (by positivity)
  exact ⟨N, fun n hn => by
    simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h : ‖x (φ n) - y'‖ ^ 2 < ε ^ 2 := by
      have := hN n hn
      rwa [dist_zero_right, Real.norm_of_nonneg (by positivity)] at this
    simp only [Function.comp_def] at *
    nlinarith [norm_nonneg (x (φ n) - y'), mul_self_nonneg (‖x (φ n) - y'‖ - ε)]⟩
