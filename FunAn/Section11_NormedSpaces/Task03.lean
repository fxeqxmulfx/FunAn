/-
  Section 11, Task 3.
  Prove that a normed space X is Banach iff every absolutely convergent series converges.
-/
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Tactic

variable {X : Type*} [NormedAddCommGroup X]

/-- A normed group is complete iff every absolutely convergent series has
    convergent partial sums. This is
    `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace` in Mathlib. -/
theorem banach_iff_abs_convergent :
    (∀ (f : ℕ → X), Summable (‖f ·‖) →
      ∃ a, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop (nhds a)) ↔
    CompleteSpace X :=
  NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace
