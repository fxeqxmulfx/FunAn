/-
  Section 14, Task 7.
  The orthogonal projection P : H → L onto a closed subspace L of a
  Hilbert space H is linear, continuous, and ‖P‖ ≤ 1.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]

/-- The orthogonal projection onto a closed subspace is continuous (as a CLM). -/
theorem orthogonal_projection_continuous :
    Continuous (K.orthogonalProjection : H → K) :=
  ContinuousLinearMap.continuous _

/-- The operator norm of the orthogonal projection is at most 1. -/
theorem orthogonal_projection_norm_le_one :
    ‖K.orthogonalProjection‖ ≤ 1 :=
  K.orthogonalProjection_norm_le

/-- The orthogonal projection is contractive: ‖Pv‖ ≤ ‖v‖. -/
theorem orthogonal_projection_apply_norm_le (v : H) :
    ‖K.orthogonalProjection v‖ ≤ ‖v‖ :=
  K.norm_orthogonalProjection_apply_le v
