/-
  Section 10, Task 7.
  If sup_i Σⱼ |aᵢⱼ| < 1, the infinite system has a unique solution in ℓ∞.

  Proof: The row-sum condition gives ‖T‖_{ℓ∞→ℓ∞} < 1, making T a
  contraction on ℓ∞. Banach fixed point theorem applies.

  We formalize: a contraction on ℓ∞(ℕ, ℝ) has a unique fixed point.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped ENNReal

/-- A contraction on ℓ∞(ℕ, ℝ) has a unique fixed point.
    Applied to Task 7: the row-sum condition sup_i Σⱼ |aᵢⱼ| < 1
    makes the operator a contraction on ℓ∞, giving unique solution. -/
theorem contraction_linfty_unique_fixedPoint
    {K : NNReal} {f : lp (fun _ : ℕ => ℝ) ∞ → lp (fun _ : ℕ => ℝ) ∞}
    (hf : ContractingWith K f) [Nonempty (lp (fun _ : ℕ => ℝ) ∞)] :
    ∃! x, f x = x :=
  ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt,
   fun _ hy => hf.fixedPoint_unique hy⟩
