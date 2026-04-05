/-
  Section 2, Task 11.
  The discrete measure μ(A) = Σ_{n∈A} pₙ (where pₙ ≥ 0) is σ-additive.

  In Lean/Mathlib, all `Measure` values are σ-additive by definition.
  The content is constructing this measure and verifying μ({n}) = pₙ.
  We use the sum of weighted Dirac measures: μ = Σₙ pₙ · δₙ.
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

open MeasureTheory Measure

/-- The discrete measure μ = Σₙ pₙ · δₙ is a (σ-additive) measure
    with μ({n}) = pₙ for each n. -/
theorem discrete_measure_sigma_additive (p : ℕ → ENNReal) :
    ∃ μ : Measure ℕ, ∀ n, μ {n} = p n := by
  refine ⟨Measure.sum (fun n => p n • Measure.dirac n), fun m => ?_⟩
  rw [Measure.sum_apply _ (measurableSet_singleton m)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
  simp only [Set.indicator_apply, Set.mem_singleton_iff]
  rw [eq_comm, tsum_eq_single m (fun n hn => by simp [hn])]
  simp
