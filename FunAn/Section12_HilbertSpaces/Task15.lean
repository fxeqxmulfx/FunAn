/-
  Section 12, Task 15.
  {sin μₙt} where μₙ are positive roots of tan μ = μ is orthogonal
  in L²(0,1), not normalized, and not a basis.

  Same principle: an orthogonal system is not a basis if it doesn't
  span the whole space (M⊥ ≠ {0}).
-/
import FunAn.Section12_HilbertSpaces.Task13
import Mathlib.Tactic

/-- An orthogonal system that doesn't span H is not a basis.
    M⊥ ≠ {0} ⟹ M ≠ H. -/
theorem orthogonal_system_not_basis
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M : Submodule 𝕜 H) (h : M.orthogonal ≠ ⊥) :
    M ≠ ⊤ :=
  ne_top_of_orthogonal_ne_bot M h
