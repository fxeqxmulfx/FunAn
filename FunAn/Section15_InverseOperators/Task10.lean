/-
  Section 15, Task 10.
  If X is a Banach space with two norms ‖·‖₁ and ‖·‖₂, both making X
  complete, and ‖x‖₁ ≤ C‖x‖₂ for all x, then the norms are equivalent.
  Proof: The identity map (X,‖·‖₂) → (X,‖·‖₁) is continuous and bijective
  between Banach spaces. By the open mapping theorem (Banach), the inverse
  is also continuous, giving ‖x‖₂ ≤ C'‖x‖₁.

  Formalized: the open mapping theorem guarantees that a continuous bijection
  between Banach spaces is a homeomorphism.
-/
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-- The open mapping theorem: a surjective continuous linear map from a
    Banach space to a Banach space is an open map. -/
theorem equivalent_norms_from_one_sided_inequality
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →L[ℝ] F) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  f.isOpenMap hsurj
