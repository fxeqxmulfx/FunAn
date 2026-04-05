/-
  Section 12, Task 4.
  C[0,π] with the L² inner product is not a Hilbert space (not complete).

  Abstract version: a dense proper subspace of a Hilbert space, with
  the induced inner product, is NOT complete. If it were, it would be
  closed; but a closed dense subspace equals the whole space, contradicting
  "proper". C[0,π] ⊂ L²[0,π] is such a dense proper subspace.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-- A dense proper subspace of a complete space is not complete.
    Applied to C[0,π] ⊂ L²[0,π]: C[0,π] is dense but not all of L². -/
theorem not_completeSpace_of_dense_proper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Submodule ℝ E)
    (hdense : Dense (S : Set E))
    (hproper : (S : Set E) ≠ Set.univ) :
    ¬CompleteSpace S := by
  intro hS
  -- CompleteSpace S ⟹ S is closed (complete subspace of metric space)
  have hclosed : IsClosed (S : Set E) := completeSpace_coe_iff_isComplete.mp hS |>.isClosed
  -- Closed + dense ⟹ S = univ
  have := hclosed.closure_eq
  rw [hdense.closure_eq] at this
  exact hproper this.symm
