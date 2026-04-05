/-
  Section 11, Task 12.
  In an infinite-dimensional normed space, there exists an infinite bounded set
  with pairwise distances ≥ 1 (and hence ≥ 0.5).
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In an infinite-dimensional normed space, there exists a bounded sequence
    with pairwise distances ≥ 1. -/
theorem exists_bounded_seq_pairwise_dist_ge_one (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧
      Pairwise fun m n => 1 ≤ ‖f m - f n‖ :=
  exists_seq_norm_le_one_le_norm_sub h
