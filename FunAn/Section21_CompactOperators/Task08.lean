/-
  Section 21, Task 08.
  A : ℓ² → ℝ, Ax = Σ ξₖ/2ᵏ is a compact operator (finite-dimensional range).

  Any continuous linear map to a finite-dimensional space is compact,
  because bounded sets in finite-dimensional spaces have compact closure.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-- Any continuous linear map to a finite-dimensional space is compact.
    This applies to A: ℓ²→ℝ, Ax = Σξₖ/2ᵏ (range = ℝ is 1-dimensional). -/
theorem clm_to_finiteDim_isCompact
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) : IsCompactOperator A := by
  haveI : ProperSpace F := FiniteDimensional.proper_real F
  exact isCompactOperator_id.comp_clm A
