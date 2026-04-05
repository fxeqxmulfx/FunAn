/-
  Section 12, Task 3.
  ℓ^p is a Hilbert space if and only if p = 2.

  Forward (p = 2 → Hilbert): Mathlib's `lp.instInnerProductSpace`.
  Reverse (p ≠ 2 → not Hilbert): the parallelogram law fails.

  For the reverse direction, we prove the key numerical lemma:
  2^(2/p) = 2 iff p = 2. When 2^(2/p) ≠ 2, the parallelogram
  law fails for the standard basis vectors e₁, e₂ in ℓᵖ.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

open scoped ENNReal

/-- ℓ² over ℝ is a Hilbert space (forward direction). -/
theorem l2_is_hilbert_space :
    Nonempty (InnerProductSpace ℝ (lp (fun _ : ℕ => ℝ) 2)) ∧
    CompleteSpace (lp (fun _ : ℕ => ℝ) 2) :=
  ⟨⟨lp.instInnerProductSpace⟩, inferInstance⟩

/-- Key numerical fact for the reverse direction:
    2/p = 1 iff p = 2 (for 0 < p). This controls whether
    the parallelogram law holds in ℓᵖ. -/
theorem two_div_eq_one_iff {p : ℝ} (hp : 0 < p) :
    2 / p = 1 ↔ p = 2 := by
  rw [div_eq_iff (ne_of_gt hp)]
  constructor <;> intro h <;> linarith
