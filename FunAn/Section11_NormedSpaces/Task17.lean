/-
  Section 11, Task 17.
  The closed unit ball of ℓ¹ is a closed set in ℓ².

  Formalized as: {x ∈ ℓ² | ∀ finite S, Σ_{n∈S} |x(n)| ≤ 1} is closed in ℓ².
  This characterizes elements whose ℓ¹ norm is ≤ 1 (equivalently: all finite
  partial sums of |x(n)| are ≤ 1, which implies summability and tsum ≤ 1).

  Proof: it is an intersection of closed sets (preimages of (-∞,1] under
  continuous functions x ↦ Σ_{n∈S} |x(n)|).
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

open scoped ENNReal

/-- The closed unit ball of ℓ¹, viewed inside ℓ², is closed.
    Here the ball is characterized by: every finite partial sum of |x(n)| is ≤ 1. -/
theorem l1_closedBall_closed_in_l2 :
    IsClosed {x : lp (fun _ : ℕ => ℝ) 2 |
      ∀ S : Finset ℕ, ∑ n ∈ S, ‖x n‖ ≤ 1} := by
  simp_rw [Set.setOf_forall]
  apply isClosed_iInter; intro S
  apply isClosed_le _ continuous_const
  exact continuous_finset_sum S fun n _ =>
    continuous_norm.comp ((continuous_apply n).comp lp.uniformContinuous_coe.continuous)
