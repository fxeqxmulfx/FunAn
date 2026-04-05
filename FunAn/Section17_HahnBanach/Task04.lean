/-
  Section 17, Task 04.
  (a) ∃ sequence of finite linear combinations of Fₜ(x) = x(t)
      converging weakly to F(x) = ∫₀¹ x(t)dt.
      Proof: Riemann sums Sₙ(f) = (1/n)Σf(k/n) → ∫₀¹ f for each continuous f.

  (b) No norm-convergent sequence of such combinations.
      Witness: gₙ(t) = cos(2πnt) has gₙ(k/n) = 1 for all k,
      so Sₙ(gₙ) = 1, while ∫₀¹ gₙ = 0. Thus ‖Sₙ − F‖ ≥ 1 for all n.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open MeasureTheory Set Finset Filter Real
open scoped Topology

noncomputable section

-- ============================================================================
-- Part (a): Riemann sums converge to the integral for continuous functions
-- ============================================================================

/-- Left Riemann sum: Sₙ(f) = (1/n) Σ_{k=0}^{n-1} f(k/n).
    Each Sₙ is a linear combination of point evaluation functionals Fₜ(x) = x(t). -/
def riemannSum (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ range n, f ((k : ℝ) / n)) / n

/-- Riemann sums converge to the integral for continuous functions on [0,1].
    This provides the weak convergence: for each f ∈ C[0,1],
    the sequence of linear combinations Sₙ(f) → F(f) = ∫₀¹ f(t)dt. -/
theorem section17_task04a_riemann_sum_tendsto
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n => riemannSum f n) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Uniform continuity on compact [0,1]
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn1
  have hne : (↑n : ℝ) ≠ 0 := hn'.ne'
  -- Key: 1/n < δ
  have h1n : 1 / (↑n : ℝ) < δ := by
    have hNn : 1 / δ < ↑n :=
      lt_of_lt_of_le hN (by exact_mod_cast show N ≤ n by omega)
    rwa [div_lt_iff₀ hδ, mul_comm, ← div_lt_iff₀ hn'] at hNn
  -- Integrability on each subinterval [k/n, (k+1)/n] ⊆ [0,1]
  have hint : ∀ k, k < n →
      IntervalIntegrable f volume ((↑k : ℝ) / ↑n) ((↑k + 1) / ↑n) := by
    intro k hk
    apply (hf.mono _).intervalIntegrable
    rw [Set.uIcc_of_le (div_le_div_of_nonneg_right
      (by linarith : (↑k : ℝ) ≤ ↑k + 1) hn'.le)]
    exact Icc_subset_Icc (div_nonneg (Nat.cast_nonneg k) hn'.le)
      ((div_le_one hn').mpr (by exact_mod_cast Nat.succ_le_of_lt hk))
  -- Decompose ∫₀¹ f = Σ ∫_{k/n}^{(k+1)/n} f
  have hdecomp : ∫ x in (0 : ℝ)..1, f x =
      ∑ k ∈ range n, ∫ x in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k => (↑k : ℝ) / ↑n) (fun k hk => by
        change IntervalIntegrable f volume ((↑k : ℝ) / ↑n) ((↑(k + 1) : ℝ) / ↑n)
        rw [show (↑(k + 1) : ℝ) / ↑n = ((↑k : ℝ) + 1) / ↑n from by push_cast; ring]
        exact hint k hk)
    dsimp only at h
    simp only [Nat.cast_zero, zero_div, div_self hne] at h
    convert h.symm using 2
    push_cast; ring
  -- Each term: f(k/n)/n = ∫ f(k/n) dt on [k/n, (k+1)/n]
  have hconst : ∀ k, k < n →
      f ((↑k : ℝ) / ↑n) / ↑n =
        ∫ _ in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f ((↑k : ℝ) / ↑n) := by
    intro k _
    rw [intervalIntegral.integral_const, smul_eq_mul,
        show ((↑k : ℝ) + 1) / ↑n - ↑k / ↑n = 1 / ↑n from by ring,
        one_div, mul_comm, ← div_eq_mul_inv]
  -- Bound each term of the difference
  have hbound : ∀ k ∈ range n,
      |f ((↑k : ℝ) / ↑n) / ↑n - ∫ x in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f x| ≤
        ε / 2 * (1 / ↑n) := by
    intro k hk
    have hk' : k < n := mem_range.mp hk
    rw [hconst k hk', ← intervalIntegral.integral_sub intervalIntegrable_const (hint k hk')]
    have hle : (↑k : ℝ) / ↑n ≤ ((↑k : ℝ) + 1) / ↑n :=
      div_le_div_of_nonneg_right (by linarith : (↑k : ℝ) ≤ ↑k + 1) hn'.le
    -- Use norm_integral bound
    have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (↑k : ℝ) / ↑n) (b := ((↑k : ℝ) + 1) / ↑n)
      (f := fun x => f ((↑k : ℝ) / ↑n) - f x) (C := ε / 2) (fun t ht => ?_)
    · rw [show |((↑k : ℝ) + 1) / ↑n - ↑k / ↑n| = 1 / ↑n from by
          rw [show ((↑k : ℝ) + 1) / ↑n - ↑k / ↑n = 1 / ↑n from by ring]
          exact abs_of_nonneg (div_nonneg one_pos.le hn'.le)] at h_norm
      rw [← Real.norm_eq_abs]; exact h_norm
    · -- ‖f(k/n) - f(t)‖ ≤ ε/2 for t in subinterval
      rw [Set.uIoc_of_le hle] at ht
      rw [Real.norm_eq_abs, abs_sub_comm]
      apply le_of_lt
      apply hδ_spec
      · -- t ∈ [0,1]
        exact ⟨le_trans (div_nonneg (Nat.cast_nonneg k) hn'.le) (le_of_lt ht.1),
               le_trans ht.2 ((div_le_one hn').mpr (by exact_mod_cast Nat.succ_le_of_lt hk'))⟩
      · -- k/n ∈ [0,1]
        exact ⟨div_nonneg (Nat.cast_nonneg k) hn'.le,
               (div_le_one hn').mpr (by exact_mod_cast hk'.le)⟩
      · -- dist t (k/n) < δ
        rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
        calc t - (↑k : ℝ) / ↑n
            ≤ ((↑k : ℝ) + 1) / ↑n - ↑k / ↑n := by linarith [ht.2]
          _ = 1 / ↑n := by ring
          _ < δ := h1n
  -- Assemble the bound
  rw [Real.dist_eq, hdecomp]
  change |riemannSum f n - ∑ k ∈ range n, ∫ x in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f x| < ε
  rw [show riemannSum f n = ∑ k ∈ range n, f ((↑k : ℝ) / ↑n) / ↑n from by
    unfold riemannSum
    exact Finset.sum_div (range n) (fun k => f ((↑k : ℝ) / ↑n)) ↑n]
  rw [← Finset.sum_sub_distrib]
  calc |∑ k ∈ range n, (f ((↑k : ℝ) / ↑n) / ↑n -
          ∫ x in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f x)|
      ≤ ∑ k ∈ range n, |f ((↑k : ℝ) / ↑n) / ↑n -
          ∫ x in ((↑k : ℝ) / ↑n)..((↑k + 1) / ↑n), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ range n, (ε / 2 * (1 / ↑n)) := Finset.sum_le_sum hbound
    _ = ε / 2 := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        field_simp
    _ < ε := half_lt_self hε

-- ============================================================================
-- Part (b): Riemann sums do not converge in operator norm
-- ============================================================================

/-- Riemann sum of cos(2πnt): since cos(2πk) = 1 for integer k,
    each f(k/n) = 1, so Sₙ = n/n = 1. -/
private lemma riemannSum_cos (n : ℕ) (hn : 0 < n) :
    riemannSum (fun x => cos (2 * π * ↑n * x)) n = 1 := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  simp only [riemannSum]
  have : ∀ k ∈ range n, cos (2 * π * ↑n * ((↑k : ℝ) / ↑n)) = 1 := by
    intro k _
    rw [show 2 * π * ↑n * ((↑k : ℝ) / ↑n) = ↑k * (2 * π) from by field_simp]
    exact cos_nat_mul_two_pi k
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  exact div_self hn'.ne'

/-- Integral of cos(2πnt) over [0,1] is 0 for n ≥ 1. -/
private lemma integral_cos_two_pi_mul (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1, cos (2 * π * ↑n * x) = 0 := by
  have hc : (2 * π * (↑n : ℝ)) ≠ 0 := by positivity
  rw [show (fun x : ℝ => cos (2 * π * ↑n * x)) = (fun x => cos ((2 * π * ↑n) * x)) from rfl,
      intervalIntegral.integral_comp_mul_left _ hc, mul_zero, mul_one, integral_cos,
      sin_zero, sub_zero]
  rw [show 2 * π * (↑n : ℝ) = ↑(2 * n) * π from by push_cast; ring,
      sin_nat_mul_pi, smul_zero]

/-- ‖Sₙ − F‖ ≥ 1 for all n ≥ 1: the witness cos(2πnt) has Sₙ(g) = 1
    but F(g) = ∫₀¹ cos(2πnt)dt = 0, while ‖g‖_∞ = 1.
    Hence Riemann sums do not converge to F in operator norm. -/
theorem section17_task04b_not_norm_convergent (n : ℕ) (hn : 0 < n) :
    |riemannSum (fun x => cos (2 * π * ↑n * x)) n -
      ∫ x in (0 : ℝ)..1, cos (2 * π * ↑n * x)| = 1 := by
  rw [riemannSum_cos n hn, integral_cos_two_pi_mul n hn, sub_zero, abs_one]
