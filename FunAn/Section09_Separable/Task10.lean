/-
  Section 09, Task 10.
  Separability of ℓᵖ_{k} (weighted ℓᵖ spaces).

  The weighted ℓᵖ space with positive weights kᵢ is homeomorphic to ℓᵖ
  via the map (Tx)ᵢ = kᵢ xᵢ. So it suffices to show ℓᵖ is separable.

  We prove: ℓᵖ(ℕ, ℝ) is separable for 1 ≤ p < ∞.
  The countable dense subset consists of finitely-supported rational sequences.
  Density uses lp.hasSum_single (partial sums converge) + density of ℚ in ℝ.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic

open scoped ENNReal
open TopologicalSpace Finset

/-- ℓᵖ(ℕ, ℝ) is separable for 1 ≤ p < ∞ (the key fact for weighted ℓᵖ_k separability). -/
theorem lp_separable (p : ℝ≥0∞) [hp1 : Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SeparableSpace (lp (fun _ : ℕ => ℝ) p) := by
  -- Map: ℕ →₀ ℚ → lp, c ↦ ∑_{i ∈ c.support} single(c_i)
  apply SeparableSpace.of_denseRange
    (u := fun (c : ℕ →₀ ℚ) =>
      ∑ i ∈ c.support, lp.single p i ((c i : ℚ) : ℝ))
  rw [Metric.denseRange_iff]
  intro f ε hε
  -- Partial sums of single vectors converge to f
  have hconv := (lp.hasSum_single hp f).tendsto_sum_nat
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv (ε / 2) (half_pos hε)
  -- Approximate each f(i) by a rational
  have hδ : (0 : ℝ) < ε / (2 * (↑N + 1)) := by positivity
  choose qf hqf using fun (i : ℕ) =>
    Rat.denseRange_cast.exists_dist_lt (f i : ℝ) hδ
  -- Build finsupp: truncate qf to range N
  set qfN : ℕ → ℚ := fun i => if i < N then qf i else 0
  set c := Finsupp.onFinset (range N) qfN (fun a ha => by
    simp only [qfN] at ha; split_ifs at ha with h; exact mem_range.mpr h; exact absurd rfl ha)
  refine ⟨c, ?_⟩
  -- Show ∑_{c.support} single(c_i) = ∑_{range N} single(qf_i)
  have hci : ∀ i ∈ range N, (c i : ℚ) = qf i := fun i hi => by
    simp [c, qfN, mem_range.mp hi]
  have hsum_eq : ∑ i ∈ c.support, lp.single p i ((c i : ℚ) : ℝ)
      = ∑ i ∈ range N, lp.single p i ((qf i : ℚ) : ℝ) := by
    rw [Finset.sum_subset Finsupp.support_onFinset_subset]
    · apply Finset.sum_congr rfl
      intro i hi; simp [hci i hi]
    · intro i _ hi
      have : c i = 0 := Finsupp.notMem_support_iff.mp hi
      simp [this]
  rw [hsum_eq]
  -- Triangle inequality
  have h1 : dist f (∑ i ∈ range N, lp.single p i (f i : ℝ)) < ε / 2 := by
    rw [dist_comm]; exact hN N le_rfl
  have hp0 : (0 : ℝ≥0∞) < p := zero_lt_one.trans_le hp1.out
  have h2 : dist (∑ i ∈ range N, lp.single p i (f i : ℝ))
      (∑ i ∈ range N, lp.single p i ((qf i : ℚ) : ℝ)) < ε / 2 := by
    -- Each lp.single is an isometry, so reduce to coordinate distances
    have hiso : ∀ i, dist (lp.single (E := fun _ : ℕ => ℝ) p i (f i))
        (lp.single p i ((qf i : ℚ) : ℝ)) = dist (f i : ℝ) ((qf i : ℚ) : ℝ) :=
      fun i => (lp.isometry_single (E := fun _ : ℕ => ℝ) i).dist_eq _ _
    calc dist _ _
        ≤ ∑ i ∈ range N, dist (lp.single (E := fun _ : ℕ => ℝ) p i (f i))
            (lp.single p i ((qf i : ℚ) : ℝ)) :=
          dist_sum_sum_le_of_le _ (fun _ _ => le_rfl)
      _ = ∑ i ∈ range N, dist (f i : ℝ) ((qf i : ℚ) : ℝ) := by
          simp_rw [hiso]
      _ ≤ ∑ _i ∈ range N, (ε / (2 * (↑N + 1))) :=
          sum_le_sum (fun i _ => (hqf i).le)
      _ = ↑N * (ε / (2 * (↑N + 1))) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ < ε / 2 := by
          rcases N.eq_zero_or_pos with rfl | _
          · simp [hε]
          · rw [show (↑N : ℝ) * (ε / (2 * (↑N + 1))) = ε * ↑N / (2 * (↑N + 1)) from by ring]
            rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (↑N + 1)) two_pos]
            nlinarith
  linarith [dist_triangle f (∑ i ∈ range N, lp.single p i (f i : ℝ))
    (∑ i ∈ range N, lp.single p i ((qf i : ℚ) : ℝ))]
