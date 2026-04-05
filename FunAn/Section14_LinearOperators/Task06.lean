/-
  Section 14, Task 6.
  A continuous linear operator remains continuous when norms are replaced
  by equivalent norms.

  Formalization: if f : E →L[𝕜] F is a continuous linear map and
  e : E' →L[𝕜] E is continuous (modeling the identity under norm change),
  then f ∘ e is continuous with ‖f ∘ e‖ ≤ ‖f‖ · ‖e‖.
-/
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Continuity is preserved under equivalent norms: composing a CLM with
    a continuous linear map (modeling norm change) gives a CLM with
    ‖f ∘ e‖ ≤ ‖f‖ · ‖e‖. -/
theorem continuous_under_equiv_norms (f : E →L[𝕜] F) (e : E' →L[𝕜] E) :
    ‖f.comp e‖ ≤ ‖f‖ * ‖e‖ :=
  ContinuousLinearMap.opNorm_comp_le f e
