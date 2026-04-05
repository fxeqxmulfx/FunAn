/-
  Section 20, Task 7.
  In an infinite-dimensional normed space, every compact set is nowhere dense.

  Proof: If interior K ≠ ∅, K contains a ball, hence a closed ball,
  which is compact (closed subset of compact). But a compact closed ball
  forces the space to be finite-dimensional (Riesz's lemma). Contradiction.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In an infinite-dimensional normed space, every compact set has empty interior. -/
theorem compact_nowhere_dense_of_infinite_dim
    (hinfin : ¬ FiniteDimensional ℝ E)
    {K : Set E} (hK : IsCompact K) :
    interior K = ∅ := by
  by_contra h
  rw [← Ne, ← Set.nonempty_iff_ne_empty] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx₀
  obtain ⟨r, hr, hball⟩ := hx₀
  -- closedBall x₀ (r/2) ⊆ ball x₀ r ⊆ K, hence compact
  have hcb_compact : IsCompact (Metric.closedBall x₀ (r / 2)) :=
    hK.of_isClosed_subset Metric.isClosed_closedBall
      ((Metric.closedBall_subset_ball (by linarith)).trans hball)
  exact hinfin (FiniteDimensional.of_isCompact_closedBall (𝕜 := ℝ) (by linarith) hcb_compact)
