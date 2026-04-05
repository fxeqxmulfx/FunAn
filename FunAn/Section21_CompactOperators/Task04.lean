/-
  Section 21, Task 4.
  Diagonal operator on ℓ² compact iff entries tend to 0.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

open scoped ENNReal
open Filter Finset

set_option maxHeartbeats 400000

private lemma memℓp_mul {a : ℕ → ℝ} (ha : ∃ C, ∀ k, |a k| ≤ C) {x : ℕ → ℝ}
    (hx : Memℓp x 2) : Memℓp (fun k => a k * x k) 2 := by
  obtain ⟨C, hC⟩ := ha
  rw [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal)] at hx ⊢
  simp only [ENNReal.toReal_ofNat] at hx ⊢
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (a 0)) (hC 0)
  exact (hx.mul_left (C ^ (2:ℝ))).of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) fun k => by
      calc ‖a k * x k‖ ^ (2:ℝ)
          ≤ (C * ‖x k‖) ^ (2:ℝ) := by
            apply Real.rpow_le_rpow (norm_nonneg _) _ (by norm_num)
            rw [norm_mul]; exact mul_le_mul_of_nonneg_right
              (by rw [Real.norm_eq_abs]; exact hC k) (norm_nonneg _)
        _ = C ^ (2:ℝ) * ‖x k‖ ^ (2:ℝ) := Real.mul_rpow hC0 (norm_nonneg _)

theorem diagonal_operator_compact_iff_tendsto_zero
    (a : ℕ → ℝ) (ha : ∃ C, ∀ k, |a k| ≤ C) :
    let A : lp (fun _ : ℕ => ℝ) 2 → lp (fun _ : ℕ => ℝ) 2 :=
      fun x => ⟨fun k => a k * x k, memℓp_mul ha (lp.memℓp x)⟩
    IsCompactOperator A ↔ Tendsto a atTop (nhds 0) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  intro A
  constructor
  · -- Forward: compact ⟹ a → 0
    intro ⟨K, hK, hK_nhds⟩
    obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hK_nhds
    rw [Metric.tendsto_atTop]; intro ε hε
    by_contra h_inf; push_neg at h_inf
    obtain ⟨φ, hφ, hφε⟩ := extraction_of_frequently_atTop (frequently_atTop.mpr h_inf)
    have hp2 : (0 : ℝ≥0∞) < 2 := by norm_num
    have hr2 : (0 : ℝ) < r / 2 := by linarith
    set s : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun n => (r/2) • lp.single 2 (φ n) (1 : ℝ)
    have hAs_in_K : ∀ n, A (s n) ∈ K := fun n => hr_sub (by
      rw [Metric.mem_ball, dist_zero_right]
      simp only [s, norm_smul, lp.norm_single hp2, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos hr2]; linarith)
    have hAs_sep : ∀ m n, m ≠ n → r / 2 * ε ≤ dist (A (s m)) (A (s n)) := by
      intro m n hmn
      rw [dist_eq_norm]
      have hne : φ m ≠ φ n := hφ.injective.ne hmn
      calc r / 2 * ε
          ≤ r / 2 * |a (φ m)| := by
            have := hφε m; simp [dist_zero_right, Real.norm_eq_abs] at this; nlinarith
        _ = ‖(A (s m) - A (s n)) (φ m)‖ := by
            simp only [A, s, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
              lp.coeFn_single, Pi.single_apply, if_neg hne, smul_eq_mul,
              mul_one, mul_zero, sub_zero, abs_mul, abs_of_pos hr2, mul_comm,
              if_true, zero_mul, one_mul, Real.norm_eq_abs]
        _ ≤ ‖A (s m) - A (s n)‖ := lp.norm_apply_le_norm hp2.ne' _ _
    obtain ⟨y, _, ψ, hψ, hconv⟩ := hK.isSeqCompact hAs_in_K
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (r / 2 * ε / 2) (by positivity)
    have h1 := hN N le_rfl
    have h2 := hN (N + 1) (Nat.le_succ N)
    have h3 : dist (A (s (ψ N))) (A (s (ψ (N + 1)))) < r / 2 * ε :=
      calc dist _ _ ≤ dist _ y + dist y _ := dist_triangle _ y _
        _ < r / 2 * ε / 2 + r / 2 * ε / 2 := add_lt_add h1 (by rwa [dist_comm])
        _ = r / 2 * ε := by ring
    linarith [hAs_sep (ψ N) (ψ (N + 1)) (hψ (by omega : N < N + 1)).ne]
  · -- Backward: a → 0 ⟹ compact
    intro ha_zero
    refine ⟨closure (A '' Metric.ball 0 1),
      isCompact_iff_totallyBounded_isComplete.mpr
        ⟨?_, isClosed_closure.isComplete⟩, ?_⟩
    · -- closure(A(B₁)) totally bounded ← A(B₁) totally bounded
      apply TotallyBounded.closure
      rw [Metric.totallyBounded_iff]; intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha_zero (ε / 2) (by linarith)
      -- Compact set K_N containing "truncations" of A(B₁) to first N coords
      -- K_N = image of compact cube under continuous map Φ
      set Φ : (Fin N → ℝ) → lp (fun _ : ℕ => ℝ) 2 :=
        fun c => ∑ i : Fin N, lp.single 2 (i : ℕ) (c i)
      have hΦ_cont : Continuous Φ := continuous_finset_sum _ fun i _ =>
        (lp.singleContinuousLinearMap (𝕜 := ℝ) (p := 2) (E := fun _ => ℝ) (i : ℕ)).continuous.comp
          (continuous_apply i)
      set cube := Set.pi Set.univ fun i : Fin N => Set.Icc (-|a (i : ℕ)|) |a (i : ℕ)|
      have hcube : IsCompact cube := isCompact_univ_pi fun _ => isCompact_Icc
      -- Get finite ε/2-net from compact image Φ(cube)
      have hK := hcube.image hΦ_cont
      obtain ⟨F, hF_fin, hF_cover⟩ := Metric.totallyBounded_iff.mp
        hK.totallyBounded (ε / 2) (by linarith)
      refine ⟨F, hF_fin, fun y hy => ?_⟩
      obtain ⟨x, hx_ball, rfl⟩ := hy
      -- Truncation of A(x) to first N coords is in Φ(cube)
      set c : Fin N → ℝ := fun i => a (i : ℕ) * x (i : ℕ)
      have hx_lt : ‖x‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hx_ball
      have hc_cube : c ∈ cube := fun i _ => by
        simp only [c, Set.mem_Icc]
        have h1 : |x (i : ℕ)| ≤ 1 := by
          have := lp.norm_apply_le_norm (show (2:ℝ≥0∞) ≠ 0 by norm_num) x (i : ℕ)
          rw [Real.norm_eq_abs] at this; linarith
        have h2 : |a (i : ℕ) * (x : ℕ → ℝ) (i : ℕ)| ≤ |a (i : ℕ)| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
        exact ⟨by linarith [neg_abs_le (a (↑i) * (↑x : ℕ → ℝ) ↑i)], by linarith [le_abs_self (a (↑i) * (↑x : ℕ → ℝ) ↑i)]⟩
      have hΦc_in : Φ c ∈ Φ '' cube := Set.mem_image_of_mem _ hc_cube
      -- ∃ f ∈ F with dist(Φ(c), f) < ε/2
      obtain ⟨f, hf, hf_dist⟩ := Set.mem_iUnion₂.mp (hF_cover hΦc_in)
      -- dist(A(x), f) ≤ dist(A(x), Φ(c)) + dist(Φ(c), f) < ε/2 + ε/2
      refine Set.mem_iUnion₂.mpr ⟨f, hf, ?_⟩
      calc dist (A x) f ≤ dist (A x) (Φ c) + dist (Φ c) f := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add ?_ (Metric.mem_ball.mp hf_dist)
        _ = ε := by ring
      -- ‖A(x) - Φ(c)‖ < ε/2: tail bound via inner product
      -- (A x - Φ c)(k) = 0 for k < N, a(k)x(k) for k ≥ N
      -- Each |a(k)x(k)|² < (ε/2)²|x(k)|², sum ≤ (ε/2)²‖x‖² < (ε/2)²
      set d := A x - Φ c
      -- Pointwise: (d k)² ≤ (ε/2)² * (x k)² for all k
      have hdk_le : ∀ k, ((d : ℕ → ℝ) k) ^ 2 ≤ (ε / 2) ^ 2 * ((x : ℕ → ℝ) k) ^ 2 := by
        intro k
        simp only [d, A, Φ, c, lp.coeFn_sub, Pi.sub_apply,
          lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Pi.single_apply]
        by_cases hk : k < N
        · rw [Finset.sum_eq_single ⟨k, hk⟩
            (fun i _ hi => by simp [show k ≠ (i : ℕ) from Fin.val_ne_of_ne (Ne.symm hi)])
            (by simp)]; simp; positivity
        · push_neg at hk
          rw [Finset.sum_eq_zero (fun i _ => by simp [show k ≠ (i : ℕ) from by omega])]
          simp only [sub_zero, mul_pow]
          exact mul_le_mul_of_nonneg_right (by
            have := hN k hk; rw [dist_zero_right, Real.norm_eq_abs] at this
            have := sq_abs (a k); have := abs_nonneg (a k); nlinarith [mul_self_nonneg (|a k|)]) (sq_nonneg _)
      -- ‖d‖² ≤ (ε/2)² ‖x‖² < (ε/2)² (via inner product tsum)
      have hd_sq : ‖d‖ ^ 2 = ∑' k, ((d : ℕ → ℝ) k) ^ 2 := by
        rw [sq, ← real_inner_self_eq_norm_mul_norm, lp.inner_eq_tsum]
        congr 1; ext k; rw [real_inner_self_eq_norm_mul_norm, Real.norm_eq_abs]
        change |(d : lp _ 2) k| * |(d : lp _ 2) k| = ((d : ℕ → ℝ) k) ^ 2; rw [← sq_abs]; ring
      have hx_sq : ‖x‖ ^ 2 = ∑' k, ((x : ℕ → ℝ) k) ^ 2 := by
        rw [sq, ← real_inner_self_eq_norm_mul_norm, lp.inner_eq_tsum]
        congr 1; ext k; rw [real_inner_self_eq_norm_mul_norm, Real.norm_eq_abs]
        change |(x : lp _ 2) k| * |(x : lp _ 2) k| = ((x : ℕ → ℝ) k) ^ 2; rw [← sq_abs]; ring
      rw [dist_eq_norm]
      -- Summability for tsum_le_tsum
      have hsx : Summable (fun k => ((x : ℕ → ℝ) k) ^ 2) :=
        ((lp.memℓp x).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)).congr fun k => by
          simp [ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
      have hsd : Summable (fun k => ((d : ℕ → ℝ) k) ^ 2) :=
        (hsx.mul_left ((ε/2)^2)).of_nonneg_of_le (fun _ => sq_nonneg _) hdk_le
      have hle := hsd.tsum_le_tsum hdk_le (hsx.mul_left _)
      rw [tsum_mul_left, ← hx_sq] at hle
      have h1 : ‖d‖ ^ 2 ≤ (ε / 2) ^ 2 * ‖x‖ ^ 2 := by linarith [hd_sq]
      -- ‖d‖² ≤ (ε/2)²·‖x‖² < (ε/2)² and ε/2 ≤ ‖d‖ → (ε/2)² ≤ ‖d‖². Contradiction.
      have h2 : (ε / 2) ^ 2 * ‖x‖ ^ 2 < (ε / 2) ^ 2 := by
        apply mul_lt_of_lt_one_right (by positivity)
        nlinarith [norm_nonneg x, mul_self_nonneg ‖x‖]
      nlinarith [norm_nonneg d, sq_nonneg ‖d‖]
    · exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun x hx =>
        subset_closure (Set.mem_image_of_mem A hx)
