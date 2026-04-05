/-
  Section 15, Task 11.
  If (1 - ab) is invertible then (1 - ba) is invertible (Jacobson's lemma).

  The inverse is (1 - ba)⁻¹ = 1 + b·(1-ab)⁻¹·a.
-/
import Mathlib.Algebra.Ring.Units
import Mathlib.Tactic

variable {R : Type*} [Ring R]

/-- Jacobson's lemma: if (1 - a*b) is a unit, then (1 - b*a) is also a unit. -/
theorem isUnit_one_sub_ba_of_isUnit_one_sub_ab (a b : R) (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  set c : R := ↑u⁻¹
  have huc : (1 - a * b) * c = 1 := by change (1 - a * b) * ↑u⁻¹ = 1; rw [← hu]; exact u.mul_inv
  have hcu : c * (1 - a * b) = 1 := by change ↑u⁻¹ * (1 - a * b) = 1; rw [← hu]; exact u.inv_mul
  -- abc = c - 1 (from (1-ab)c = 1)
  have habc : a * b * c = c - 1 := by
    have h : c - a * b * c = 1 := by rwa [sub_mul, one_mul] at huc
    rw [eq_sub_iff_add_eq, add_comm]; exact (sub_eq_iff_eq_add.mp h).symm
  -- cab = c - 1 (from c(1-ab) = 1)
  have hcab : c * a * b = c - 1 := by
    have h : c - c * a * b = 1 := by rw [mul_sub, mul_one, ← mul_assoc] at hcu; exact hcu
    rw [eq_sub_iff_add_eq, add_comm]; exact (sub_eq_iff_eq_add.mp h).symm
  -- Construct the unit: val = 1 - ba, inv = 1 + bca
  refine ⟨⟨1 - b * a, 1 + b * c * a, ?_, ?_⟩, rfl⟩
  · -- (1 - ba)(1 + bca) = 1
    have key : b * a * (b * c * a) = b * c * a - b * a := by
      have : b * a * (b * c * a) = b * (a * b * c) * a := by simp only [mul_assoc]
      rw [this, habc, mul_sub, mul_one, sub_mul]
    calc (1 - b * a) * (1 + b * c * a)
        = 1 + b * c * a - b * a - b * a * (b * c * a) := by noncomm_ring
      _ = 1 + b * c * a - b * a - (b * c * a - b * a) := by rw [key]
      _ = 1 := by noncomm_ring
  · -- (1 + bca)(1 - ba) = 1
    have key : b * c * a * (b * a) = b * c * a - b * a := by
      have : b * c * a * (b * a) = b * (c * a * b) * a := by simp only [mul_assoc]
      rw [this, hcab, mul_sub, mul_one, sub_mul]
    calc (1 + b * c * a) * (1 - b * a)
        = 1 - b * a + b * c * a - b * c * a * (b * a) := by noncomm_ring
      _ = 1 - b * a + b * c * a - (b * c * a - b * a) := by rw [key]
      _ = 1 := by noncomm_ring
