/-
  Section 18, Task 4.
  The map Φ : L(X,Y) → L(Y*,X*) defined by Φ(A) = A* is a continuous
  linear operator. In fact it is an isometry: ‖A*‖ = ‖A‖.
  This follows from ‖A*‖ = sup{|A*f(x)| : ‖f‖≤1, ‖x‖≤1}
  = sup{|f(Ax)| : ‖f‖≤1, ‖x‖≤1} = sup{‖Ax‖ : ‖x‖≤1} = ‖A‖
  by Hahn-Banach.

  In the Hilbert space setting, the adjoint is a linear isometry equivalence
  (Mathlib: ContinuousLinearMap.adjoint).
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The adjoint map A ↦ A† is an isometry: ‖A†‖ = ‖A‖. -/
theorem adjoint_map_isometry (A : E →L[𝕜] F) :
    ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ :=
  ContinuousLinearMap.adjoint.norm_map A
