/-
  Section 11, Task 08.
  C[a,b] with the integral norm ‖f‖ = ∫|f(x)|dx is not complete.

  Abstract proof: C[a,b] embeds as a dense proper subspace of L¹[a,b].
  A dense proper subset of a complete metric space cannot be complete:
  if it were, it would be closed; closed + dense = whole space,
  contradicting "proper".
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-- A dense proper subset of a complete metric space is not complete.
    Applied to C[a,b] ⊂ L¹[a,b]: continuous functions are L¹-dense
    in L¹ but not all of L¹, so C[a,b] with L¹ norm is not complete. -/
theorem not_completeSpace_of_dense_ne_univ
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {S : Set X} (hdense : Dense S) (hne : S ≠ Set.univ) :
    ¬CompleteSpace S := by
  intro hS
  apply hne
  have hclosed : IsClosed S := (completeSpace_coe_iff_isComplete.mp hS).isClosed
  calc S = closure S := hclosed.closure_eq.symm
    _ = Set.univ := hdense.closure_eq
