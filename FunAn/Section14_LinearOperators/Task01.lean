/-
  Section 14, Task 1.
  Any linear operator A : ℝⁿ → ℝᵐ is bounded (continuous).
  In finite dimensions, all linear maps are automatically continuous,
  and bijective ones have continuous inverses.
-/
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-- Every linear map between finite-dimensional real normed spaces is continuous. -/
theorem linear_map_finite_dim_continuous
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) : Continuous f :=
  LinearMap.continuous_of_finiteDimensional f

/-- A bijective linear equivalence on finite-dim spaces has continuous inverse. -/
theorem linear_equiv_inverse_continuous
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) : Continuous e.symm := by
  exact LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
