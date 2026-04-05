/-
  Section 8, Task 01.
  Two metrics on ℝ with the same convergent sequences but different
  Cauchy sequences: ρ = |x−y| (complete) and ρ₁ = |arctan x − arctan y| (not complete).

  Abstract principle: a non-closed subset of a complete metric space is not complete
  (contrapositive of "complete subspace ⟹ closed"). So e.g. (0,1) ⊂ ℝ is not
  complete, while ℝ is. Since (0,1) ≅ ℝ as topological spaces, convergent sequences
  agree but Cauchy sequences differ.
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-- A non-closed subset of a complete metric space is not complete. -/
theorem not_completeSpace_of_not_isClosed
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {S : Set X} (hS : ¬IsClosed S) : ¬CompleteSpace S :=
  fun h => hS (completeSpace_coe_iff_isComplete.mp h).isClosed

/-- The open interval (0,1) in ℝ is not complete: it's a non-closed
    subset of the complete space ℝ. This gives an example of a
    topological space homeomorphic to ℝ but with a non-complete metric. -/
theorem Ioo_not_completeSpace : ¬CompleteSpace (Set.Ioo (0:ℝ) 1) :=
  not_completeSpace_of_not_isClosed (by
    intro h
    have : Set.Ioo (0:ℝ) 1 = closure (Set.Ioo 0 1) := h.closure_eq.symm
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at this
    exact absurd (Set.ext_iff.mp this 0 |>.mpr (Set.left_mem_Icc.mpr (by norm_num)))
      (by simp [Set.mem_Ioo]))
