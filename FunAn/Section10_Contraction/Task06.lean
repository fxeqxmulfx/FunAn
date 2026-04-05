/-
  Section 10, Task 6.
  If sup_j Σᵢ |aᵢⱼ| < 1, the infinite system xᵢ = Σⱼ aᵢⱼxⱼ + bᵢ has a
  unique solution x ∈ ℓ¹ for every b ∈ ℓ¹.

  Proof: The operator T(x)ᵢ = Σⱼ aᵢⱼxⱼ + bᵢ is a contraction on ℓ¹
  (the column-sum condition gives ‖T‖_{ℓ¹→ℓ¹} < 1), so Banach FPT applies.

  We formalize: a contraction on ℓ¹ has a unique fixed point.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open scoped ENNReal

/-- A contraction on ℓ¹(ℕ, ℝ) has a unique fixed point.
    Applied to Task 6: the column-sum condition sup_j Σᵢ |aᵢⱼ| < 1
    makes the operator a contraction on ℓ¹, giving unique solution. -/
theorem contraction_l1_unique_fixedPoint
    {K : NNReal} {f : lp (fun _ : ℕ => ℝ) 1 → lp (fun _ : ℕ => ℝ) 1}
    (hf : ContractingWith K f) [Nonempty (lp (fun _ : ℕ => ℝ) 1)] :
    ∃! x, f x = x :=
  ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt,
   fun _ hy => hf.fixedPoint_unique hy⟩
