/-
  Section 21, Task 11.
  d/dt : C²[0,1] → C[0,1] is compact (via Arzelà-Ascoli).

  Abstract proof: d/dt = (d/dt : C¹→C) ∘ (inclusion : C²→C¹).
  The inclusion C²→C¹ is compact (by Arzelà-Ascoli: the image of the
  C² unit ball is equicontinuous in C¹). Composing a CLM with a compact
  operator gives a compact operator.

  We formalize the abstract principle: CLM ∘ compact = compact.
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

/-- Composition of a CLM with a compact operator is compact.
    This is the principle behind: d/dt : C² → C is compact
    (factor as CLM ∘ compact inclusion). -/
theorem compact_of_clm_comp_compact
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : E →L[𝕜] F} (hT : IsCompactOperator (T : E → F))
    (S : F →L[𝕜] G) :
    IsCompactOperator (S.comp T : E → G) :=
  hT.clm_comp S
