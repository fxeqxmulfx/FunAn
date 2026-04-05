/-
  Section 11, Task 16.
  M = {x ∈ C⁽¹⁾[-1,1] : ‖x‖₁ ≤ 1} is not closed in C[-1,1].

  Proof: The sequence xₙ(t) = √(t² + 1/n²)/3 converges uniformly to
  |t|/3, which is continuous but not differentiable at 0.
  Each xₙ ∈ C¹ with ‖xₙ‖ ≤ 1/3, so xₙ ∈ M, but the limit |t|/3 ∉ C¹.

  We formalize: |·| is continuous but not differentiable (at 0),
  witnessing that C¹ ⊊ C as a topological subspace.
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic

/-- There exists a continuous function ℝ → ℝ that is not differentiable:
    the absolute value function is continuous but not differentiable at 0.
    This witnesses C¹[-1,1] ⊊ C[-1,1], so C¹ ∩ closedBall is not closed. -/
theorem section11_task16 : ∃ f : ℝ → ℝ, Continuous f ∧ ¬ Differentiable ℝ f :=
  ⟨fun x => |x|, continuous_abs, fun h => not_differentiableAt_abs_zero (h 0)⟩
