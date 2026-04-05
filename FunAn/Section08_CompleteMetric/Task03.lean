/-
  Section 08, Task 03.
  Prove completeness of ℕ with metric ρ(n,m) = 1 + 1/(n+m) for n ≠ m.

  Key insight: dist(n,m) > 1 for n ≠ m, so for ε < 1 the Cauchy
  condition forces xₙ = xₘ. Every Cauchy sequence is eventually
  constant, hence convergent.

  We prove the abstract version: in any metric space where distinct
  points have distance ≥ 1, every Cauchy sequence is eventually constant.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-- In a metric space where distinct points are distance ≥ 1 apart,
    every Cauchy sequence is eventually constant (hence convergent). -/
theorem complete_of_discrete_metric {X : Type*} [MetricSpace X]
    (hdisc : ∀ x y : X, x ≠ y → 1 ≤ dist x y)
    {f : ℕ → X} (hf : CauchySeq f) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hf (1/2) (by norm_num)
  exact ⟨N, fun n hn => by
    by_contra h
    linarith [hdisc _ _ h, hN n hn]⟩

/-- The above implies completeness: the sequence converges to f N. -/
theorem converges_of_discrete_cauchy {X : Type*} [MetricSpace X]
    (hdisc : ∀ x y : X, x ≠ y → 1 ≤ dist x y)
    {f : ℕ → X} (hf : CauchySeq f) :
    ∃ a, Filter.Tendsto f Filter.atTop (nhds a) := by
  obtain ⟨N, hN⟩ := complete_of_discrete_metric hdisc hf
  exact ⟨f N, Metric.tendsto_atTop.mpr fun ε hε => ⟨N, fun n hn => by
    rw [hN n hn, dist_self]; exact hε⟩⟩
