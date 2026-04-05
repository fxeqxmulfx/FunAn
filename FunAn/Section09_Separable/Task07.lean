/-
  Section 9, Task 07.
  The space M[a,b] of bounded measurable functions on [a,b] with the
  sup norm is not separable.

  Proof: The family {1_{[a,t]} : t ∈ (a,b)} has pairwise sup-distance 1.
  We formalize the underlying principle: any metric space with an uncountable
  family of pairwise ε-separated points is not separable.
  Applied to M[a,b] with the indicator functions, this gives the result.
-/
import Mathlib.Topology.Bases
import Mathlib.Tactic

open TopologicalSpace

/-- A metric space with an uncountable family of pairwise ε-separated
    points is not separable. This is the key principle behind the
    non-separability of M[a,b] (bounded measurable functions, sup norm). -/
theorem not_separableSpace_of_uncountable_pairwise_dist
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} (hι : ¬Countable ι)
    {f : ι → X} {ε : ℝ} (hε : 0 < ε)
    (hf : Pairwise fun i j => ε ≤ dist (f i) (f j)) :
    ¬SeparableSpace X := by
  intro hsep
  apply hι
  have hpw : Pairwise (Function.onFun Disjoint fun i => Metric.ball (f i) (ε / 3)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    linarith [hf hij]
  have hcount := hpw.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball)
    (fun i => ⟨f i, Metric.mem_ball_self (by linarith)⟩)
  exact hcount
