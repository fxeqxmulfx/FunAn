/-
  Section 9, Task 3.
  A = {eⁱⁿ : n ∈ ℤ} is dense in the unit circle {z ∈ ℂ : |z| = 1}.
  Proof: The map n ↦ eⁱⁿ = eⁱ·ⁿ gives an orbit of the irrational
  rotation by 1 radian on S¹. Since 1/(2π) is irrational, the orbit
  is dense by Weyl's equidistribution theorem (or Jacobi's theorem).

  In Mathlib: multiples of a on AddCircle p are dense iff a/p is irrational.
  Here a = 1 and p = 2π, so 1/(2π) is irrational.
-/
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Tactic

open AddCircle

/-- 1/(2π) is irrational (since π is irrational). -/
private theorem irrational_one_div_two_pi : Irrational (1 / (2 * Real.pi)) := by
  rw [one_div, show (2 : ℝ) * Real.pi = Real.pi * 2 from mul_comm _ _]
  exact irrational_inv_iff.mpr (irrational_mul_natCast_iff.mpr ⟨two_ne_zero, irrational_pi⟩)

/-- The integer multiples of 1 are dense on the circle ℝ/2πℤ,
    i.e., {eⁱⁿ : n ∈ ℤ} is dense in S¹. -/
theorem exp_in_dense_in_circle :
    DenseRange (· • (1 : ℝ) : ℤ → AddCircle (2 * Real.pi)) := by
  rw [denseRange_zsmul_coe_iff]
  exact irrational_one_div_two_pi
