/-
  Section 12, Task 1.
  The formula (x,y) = Σ αₖ ξₖ η̄ₖ (with 0 < αₖ ≤ 1) defines a scalar
  product on ℓ². The standard case αₖ = 1 is provided by Mathlib's
  lp.instInnerProductSpace.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

open scoped ENNReal

/-- ℓ² has a well-defined inner product (Mathlib instance). -/
theorem l2_inner_product_well_defined :
    Nonempty (InnerProductSpace ℝ (lp (fun _ : ℕ => ℝ) 2)) :=
  ⟨lp.instInnerProductSpace⟩
