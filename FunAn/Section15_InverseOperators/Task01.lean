/-
  Section 15, Task 1.
  Any linear operator A : ℝⁿ → ℝⁿ is bounded, and a bijective one
  has a continuous inverse (by open mapping / finite-dim automaticity).
-/
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-- Any linear operator between finite-dim real spaces is bounded. -/
theorem matrix_operator_bounded
    {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : Continuous f :=
  LinearMap.continuous_of_finiteDimensional f

/-- A bijective linear map between finite-dim real spaces has a
    continuous inverse (all linear maps are continuous in finite dim). -/
theorem matrix_operator_inverse_continuous
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    Continuous e.symm := by
  exact LinearMap.continuous_of_finiteDimensional (e.symm.toLinearMap)
