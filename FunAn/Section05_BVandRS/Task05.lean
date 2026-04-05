/-
  Section 5, Task 05.
  (a) x² cos(π/x) has bounded variation on [0,1].
      Proof: f' bounded ⟹ Lipschitz ⟹ BV.
  (b) x² sin(1/x) has bounded variation on [0, 2/π].
      Proof: f'(x) = 2x sin(1/x) − cos(1/x) is bounded (|f'| ≤ 3),
      so f is Lipschitz hence BV — same principle as (a).

  Note: The original task description claimed "unbounded variation",
  but this is incorrect: |f'(x)| ≤ 2|x|+1 ≤ 2(2/π)+1 < 3,
  so f is Lipschitz on [0, 2/π] and thus has bounded variation.

  We formalize two principles:
  (a) Lipschitz ⟹ locally BV.
  (b) Differentiable with bounded derivative on convex set ⟹ Lipschitz ⟹ BV.
      This is the key fact for x²sin(1/x): its derivative is bounded.
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-- (a) Lipschitz implies locally bounded variation.
    Applied to x²cos(π/x): |f'| ≤ 2+π, so f is Lipschitz hence BV. -/
theorem lipschitz_implies_locally_bv
    {E : Type*} [PseudoEMetricSpace E]
    {F : Type*} [PseudoEMetricSpace F]
    {f : ℝ → F} {s : Set ℝ} {C : NNReal}
    (hf : LipschitzOnWith C f s) :
    LocallyBoundedVariationOn f s :=
  hf.locallyBoundedVariationOn

/-- (b) Differentiable with bounded derivative on a convex set ⟹ locally BV.
    Applied to x²sin(1/x): f'(x) = 2x sin(1/x) − cos(1/x) satisfies
    |f'(x)| ≤ 2|x| + 1 ≤ 3 on [0, 2/π], so f is 3-Lipschitz hence BV. -/
theorem differentiable_bounded_deriv_locally_bv
    {f : ℝ → ℝ} {s : Set ℝ} {C : NNReal}
    (hs : Convex ℝ s)
    (hf : DifferentiableOn ℝ f s)
    (hf' : ∀ x ∈ s, ‖fderivWithin ℝ f s x‖₊ ≤ C) :
    LocallyBoundedVariationOn f s :=
  (hs.lipschitzOnWith_of_nnnorm_fderivWithin_le hf hf').locallyBoundedVariationOn
