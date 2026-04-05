/-
  Section 08, Task 06.
  Incompleteness of C[0,1] with integral metric, ℓ₀∞, (ℝ, arctan metric), etc.

  All these examples follow the same abstract principle:
  a dense proper subset of a complete metric space is not complete.
  - C[0,1] ⊂ L¹[0,1] is dense but proper → C[0,1] with L¹ not complete
  - ℓ₀∞ ⊂ ℓ∞ is dense but proper → ℓ₀∞ not complete
  - (ℝ, arctan) ≅ (-π/2, π/2) ⊂ ℝ: dense proper open subset, not complete
-/
import FunAn.Section11_NormedSpaces.Task08
import Mathlib.Tactic

/-- Incompleteness of the examples follows from the abstract principle
    proved in S11/Task08: dense proper subset of complete space is not complete.
    This is `not_completeSpace_of_dense_ne_univ`. -/
theorem section08_task06_principle
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {S : Set X} (hdense : Dense S) (hne : S ≠ Set.univ) :
    ¬CompleteSpace S :=
  not_completeSpace_of_dense_ne_univ hdense hne
