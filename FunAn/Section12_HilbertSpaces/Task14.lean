/-
  Section 12, Task 14.
  {√(2/π) sin(nt)} is ONB in L²(0,π) but NOT in L²(-π,π):
  not normalized (‖sin(nt)‖² = π ≠ π/2) and not a basis (misses cosines).

  Same principle as Task 13: an ONS is not a basis when M⊥ ≠ {0}.
  In L²(-π,π), cos(nt) ⊥ sin(mt) for all n,m, so span{sin(nt)} ≠ L².
-/
import FunAn.Section12_HilbertSpaces.Task13
import Mathlib.Tactic

/-- An ONS is not a basis when its orthogonal complement is nontrivial.
    Applies to {sin(nt)} in L²(-π,π): cosines are orthogonal to all sines. -/
theorem ons_not_basis_when_orthogonal_complement_nontrivial
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M : Submodule 𝕜 H) (h : M.orthogonal ≠ ⊥) :
    M ≠ ⊤ :=
  ne_top_of_orthogonal_ne_bot M h
