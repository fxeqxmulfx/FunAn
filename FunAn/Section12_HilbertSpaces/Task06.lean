/-
  Section 12, Task 6.
  Prove that for any M ⊂ H, M⊥ is a closed subspace.
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The orthogonal complement of any submodule is closed. -/
theorem orthogonal_isClosed (K : Submodule ℝ H) :
    IsClosed (Kᗮ : Set H) :=
  K.isClosed_orthogonal
