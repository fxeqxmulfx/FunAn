/-
  Section 10, Task 8.
  The Volterra equation x(t) = ∫₀ᵗ K(t,s)x(s)ds can have infinitely
  many solutions when K is not continuous (Lipschitz condition fails).

  Key point: without the contraction condition, fixed points need not
  be unique. If a linear operator T has two distinct fixed points x₁, x₂,
  then x₂ + c·(x₁ - x₂) is a fixed point for every c ∈ ℝ.
  The Volterra equation with K(t,s) = 1/t has solutions x(t) = c/t for all c;
  the operator is not a contraction, so Banach FPT does not apply.
-/
import Mathlib.Tactic

/-- If a linear operator T has two distinct fixed points x₁ ≠ x₂,
    then T(x₂ + c·(x₁-x₂)) = x₂ + c·(x₁-x₂) for all c ∈ ℝ,
    giving infinitely many fixed points along the line through x₁, x₂. -/
theorem infinitely_many_fixed_points_of_linear
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {T : E →ₗ[ℝ] E} {x₁ x₂ : E}
    (hfix₁ : T x₁ = x₁) (hfix₂ : T x₂ = x₂) :
    ∀ c : ℝ, T (x₂ + c • (x₁ - x₂)) = x₂ + c • (x₁ - x₂) := by
  intro c
  simp [map_add, map_smul, map_sub, hfix₁, hfix₂]
