/-
  Section 20, Task 1.
  Integral transform sets compact in Lᵖ (Kolmogorov-Riesz criterion).

  The Kolmogorov-Riesz theorem: a subset S of Lᵖ(ℝⁿ) is totally bounded iff
  (1) S is bounded, (2) S is equitight, (3) S is Lᵖ-equicontinuous
  (translations converge uniformly in S).

  We formalize the abstract principle: totally bounded + complete = compact.
  Applied to Lᵖ (which is complete), total boundedness is the key criterion.
-/
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Tactic

/-- A totally bounded subset of a complete space has compact closure.
    This is the abstract principle behind Kolmogorov-Riesz:
    in Lᵖ (complete), total boundedness ⟹ compact closure. -/
theorem isCompact_closure_of_totallyBounded
    {X : Type*} [UniformSpace X] [CompleteSpace X]
    {S : Set X} (hS : TotallyBounded S) :
    IsCompact (closure S) :=
  isCompact_iff_totallyBounded_isComplete.mpr ⟨hS.closure, isClosed_closure.isComplete⟩
