/-
  Section 17, Task 07.
  Weak convergence in ℓ² implies coordinatewise convergence.

  Proof: x(k) = ⟪x, eₖ⟫ where eₖ = lp.single 2 k 1.
  Weak convergence applied to y = eₖ gives xₙ(k) → x₀(k).
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

open scoped InnerProductSpace
open Filter

private theorem real_inner_one (a : ℝ) : ⟪a, (1 : ℝ)⟫_ℝ = a := by
  simp [Inner.inner]

/-- Weak convergence in ℓ² implies coordinatewise convergence. -/
theorem weak_implies_coordinatewise_l2
    {x : ℕ → lp (fun _ : ℕ => ℝ) 2} {x₀ : lp (fun _ : ℕ => ℝ) 2}
    (hweak : ∀ y : lp (fun _ : ℕ => ℝ) 2,
      Tendsto (fun n => ⟪x n, y⟫_ℝ) atTop (nhds ⟪x₀, y⟫_ℝ))
    (k : ℕ) :
    Tendsto (fun n => (x n : ℕ → ℝ) k) atTop (nhds ((x₀ : ℕ → ℝ) k)) := by
  have h := hweak (lp.single 2 k (1 : ℝ))
  simp only [lp.inner_single_right, real_inner_one] at h
  exact h
