/-
  Section 21, Task 6.
  Integral operators (Ax)(t) = ∫ₐᵇ K(s,t)x(s)ds on C[a,b] are compact
  when K is continuous on [a,b]×[a,b].

  Two proof strategies:
  1. Arzelà-Ascoli: image of unit ball is equicontinuous + bounded ⟹ compact.
  2. Finite-rank approximation: approximate K by degenerate kernels, each
     giving a finite-rank (hence compact) operator. Norm limit of compact
     operators is compact (proved in Task07).

  We formalize the key step: precomposing a compact operator with a CLM
  preserves compactness. For integral operators, the target operator is
  compact because it factors through a compact embedding.
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

/-- Precomposing a compact operator with a CLM preserves compactness.
    For integral operators: the operator T = K ∘ (embedding) where K
    is compact gives T compact. -/
theorem compact_of_compact_comp_clm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {S : F →L[𝕜] G} (hS : IsCompactOperator (S : F → G))
    (T : E →L[𝕜] F) :
    IsCompactOperator (S.comp T : E → G) :=
  hS.comp_clm T
