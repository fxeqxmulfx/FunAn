/-
  Section 18, Task 5.
  If A is invertible, then A* is invertible and (A*)⁻¹ = (A⁻¹)*.

  In Mathlib, for a linear equivalence f : M₁ ≃ₗ[R] M₂,
  `LinearEquiv.dualMap_symm` states: (dualMap f).symm = dualMap f.symm.
  This is exactly (A*)⁻¹ = (A⁻¹)*.
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

variable {R M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- If A is invertible (a linear equivalence), then A* is invertible
    and (A*)⁻¹ = (A⁻¹)*. This is `LinearEquiv.dualMap_symm` in Mathlib. -/
theorem adjoint_inv_eq_inv_adjoint' (f : M₁ ≃ₗ[R] M₂) :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  LinearEquiv.dualMap_symm
