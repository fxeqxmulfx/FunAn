/-
  Section 21, Task 9.
  Show that the image of a compact operator is separable.

  Proof: range A = ⋃ n, A '' closedBall 0 n. Each A '' closedBall 0 n
  has compact closure (since A is compact), hence is separable.
  Countable union of separable sets is separable.
-/
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The range of a compact operator is separable. -/
theorem compact_operator_range_separable
    (A : X →L[ℝ] Y) (hA : IsCompactOperator (A : X → Y)) :
    TopologicalSpace.IsSeparable (Set.range A) := by
  -- range A = ⋃ n : ℕ, A '' closedBall 0 n
  have hrange : Set.range A = ⋃ n : ℕ, A '' Metric.closedBall 0 (n : ℝ) := by
    ext y; simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⌈‖x‖⌉₊, x, Metric.mem_closedBall.mpr (by simp [dist_zero_right]; exact Nat.le_ceil _), rfl⟩
    · rintro ⟨n, x, _, rfl⟩; exact ⟨x, rfl⟩
  rw [hrange]
  rw [TopologicalSpace.isSeparable_iUnion]
  intro n
  -- A '' closedBall 0 n is bounded, its closure is compact
  have hbdd : Bornology.IsBounded (Metric.closedBall (0 : X) n) :=
    Metric.isBounded_closedBall
  exact ((hA.isCompact_closure_image_of_bounded hbdd).isSeparable).mono
    subset_closure
