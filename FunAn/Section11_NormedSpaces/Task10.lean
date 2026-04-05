/-
  Section 11, Task 10.
  Prove that every finite-dimensional subspace of a normed space is closed.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every finite-dimensional subspace of a normed space is closed. -/
theorem finiteDimensional_subspace_isClosed (S : Submodule ℝ E)
    [FiniteDimensional ℝ S] : IsClosed (S : Set E) :=
  S.closed_of_finiteDimensional
