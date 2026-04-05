/-
  Section 18, Task 6.
  For a reflexive Banach space X and A ∈ L(X,Y), (A*)* = A under the
  canonical embedding X → X**. That is, the double adjoint recovers A
  when X is reflexive (the canonical embedding is surjective).

  In the Hilbert space setting, this is ContinuousLinearMap.adjoint_adjoint.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- In Hilbert spaces, the double adjoint is the identity: (A†)† = A. -/
theorem double_adjoint_eq (A : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) = A :=
  ContinuousLinearMap.adjoint_adjoint A
