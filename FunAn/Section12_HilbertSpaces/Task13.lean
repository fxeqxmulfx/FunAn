/-
  Section 12, Task 13.
  The Rademacher system is ONS but not a basis in L²(0,1).

  Abstract principle: if M⊥ ≠ {0}, then M ≠ H, so any ONS spanning M
  is not a Hilbert basis.
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- If M⊥ ≠ {0}, then M ≠ H. Any ONS spanning M is not a basis. -/
theorem ne_top_of_orthogonal_ne_bot (M : Submodule 𝕜 H) (h : M.orthogonal ≠ ⊥) :
    M ≠ ⊤ := by
  intro htop; exact h (htop ▸ Submodule.top_orthogonal_eq_bot)
