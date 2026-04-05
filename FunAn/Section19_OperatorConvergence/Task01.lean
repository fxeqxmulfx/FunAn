/-
  Section 19, Task 1.
  In finite dimensions, weak (pointwise) convergence of operators
  implies norm convergence.

  Proof strategy: Use a finite basis v of E and the bound
  ‖T‖ ≤ C · max_i ‖T(v_i)‖ (from Basis.exists_opNorm_le).
  Pointwise convergence gives convergence on each v_i,
  and the finite maximum of convergent sequences converges.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- In finite-dimensional spaces, pointwise convergence of continuous linear maps
    implies convergence in operator norm. -/
theorem pointwise_tendsto_implies_norm_tendsto
    {f : ℕ → E →L[𝕜] F} {g : E →L[𝕜] F}
    (h : ∀ x : E, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    Filter.Tendsto (fun n => ‖f n - g‖) Filter.atTop (nhds 0) := by
  set v := Module.finBasis 𝕜 E
  obtain ⟨C, hCpos, hC⟩ := v.exists_opNorm_le (F := F)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose δ so that C * δ < ε
  set δ := ε / (2 * C) with hδ_def
  have hδpos : (0 : ℝ) < δ := div_pos hε (mul_pos two_pos hCpos)
  -- For each basis element i, find N_i with ‖f n (v i) - g (v i)‖ < δ for n ≥ N_i
  have hconv : ∀ i, ∃ N, ∀ n ≥ N, dist (f n (v i)) (g (v i)) < δ := by
    intro i
    exact (Metric.tendsto_atTop.mp (h (v i))) δ hδpos
  choose N hN using hconv
  -- Take the max of all N_i
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  -- For all i, N i ≤ n
  have hNi : ∀ i, N i ≤ n := fun i =>
    le_trans (Finset.le_sup (f := N) (Finset.mem_univ i)) hn
  -- So ‖(f n - g)(v i)‖ ≤ δ for all i
  have hle : ∀ i, ‖(f n - g) (v i)‖ ≤ δ := by
    intro i
    rw [ContinuousLinearMap.sub_apply]
    rw [← dist_eq_norm]
    exact le_of_lt (hN i n (hNi i))
  -- By the basis bound: ‖f n - g‖ ≤ C * δ
  have hbound := hC hδpos.le hle
  -- dist ‖f n - g‖ 0 = ‖f n - g‖ ≤ C * δ = ε/2 < ε
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖f n - g‖ ≤ C * δ := hbound
    _ = ε / 2 := by rw [hδ_def]; field_simp
    _ < ε := half_lt_self hε
