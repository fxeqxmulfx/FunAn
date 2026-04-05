/-
  Section 21, Task 1.
  Any linear operator A : ℝⁿ → ℝᵐ is compact.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

/-- Any continuous linear map from a finite-dimensional real space is compact. -/
theorem linear_map_finiteDim_isCompact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) :
    IsCompactOperator (A : E → F) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  -- closed ball is compact in a proper space
  refine ⟨A '' Metric.closedBall 0 1,
    (isCompact_closedBall 0 1).image A.continuous,
    ?_⟩
  -- A⁻¹'(A '' closedBall 0 1) ⊇ closedBall 0 1 ∈ 𝓝 0
  exact Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos)
    (Set.subset_preimage_image A _)
