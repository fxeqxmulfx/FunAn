/-
  Section 15, Task 9.
  a) Prove that if A⁻¹ and B⁻¹ exist, then (AB)⁻¹ = B⁻¹A⁻¹.
  b) Prove that if A⁻¹ and (BA)⁻¹ exist, then B⁻¹ exists.
-/
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

variable {X : Type*} [Monoid X]

/-- (AB)⁻¹ = B⁻¹A⁻¹ for invertible elements. -/
theorem inv_mul_eq (A B : Xˣ) :
    ((A * B)⁻¹ : Xˣ) = B⁻¹ * A⁻¹ :=
  mul_inv_rev A B

/-- If A⁻¹ and (BA)⁻¹ exist, then B⁻¹ exists.
    Proof: B = (BA) · A⁻¹, product of two invertible elements. -/
theorem isUnit_of_mul_isUnit_of_isUnit
    {a b : X} (ha : IsUnit a) (hba : IsUnit (b * a)) :
    IsUnit b := by
  obtain ⟨u, rfl⟩ := ha
  suffices h : IsUnit (b * ↑u * ↑u⁻¹) by
    simpa [mul_assoc] using h
  exact hba.mul u⁻¹.isUnit
