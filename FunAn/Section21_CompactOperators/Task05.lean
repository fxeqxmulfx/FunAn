/-
  Section 21, Task 5.
  The multiplication operator (Ax)(t) = x₀(t)·x(t) on C[a,b] where
  x₀ ≠ 0 everywhere is NOT compact (on infinite-dimensional spaces).

  Abstract version: an invertible operator on an infinite-dimensional
  Banach space cannot be compact, because id = T⁻¹ ∘ T would be compact,
  contradicting the Riesz theorem (id compact iff finite-dimensional).
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-- An invertible compact operator forces the space to be finite-dimensional.
    Contrapositive: on infinite-dim spaces, invertible operators are not compact. -/
theorem finiteDimensional_of_compact_invertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E →L[ℝ] E} (hT : IsCompactOperator T)
    {S : E →L[ℝ] E} (hinv : S.comp T = ContinuousLinearMap.id ℝ E) :
    FiniteDimensional ℝ E := by
  have hid : IsCompactOperator (_root_.id : E → E) := by
    have h := hT.clm_comp S
    rwa [show (⇑S ∘ ⇑T : E → E) = _root_.id from by
      ext x; show S (T x) = x; exact congr_fun (congr_arg DFunLike.coe hinv) x] at h
  haveI : LocallyCompactSpace ℝ := locallyCompact_of_proper
  exact (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mp hid

/-- Corollary: no invertible operator is compact on an infinite-dim space. -/
theorem not_compact_of_invertible_infinite_dim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hinfin : ¬FiniteDimensional ℝ E)
    {T : E →L[ℝ] E} (hT : IsCompactOperator T)
    {S : E →L[ℝ] E} (hinv : S.comp T = ContinuousLinearMap.id ℝ E) :
    False :=
  hinfin (finiteDimensional_of_compact_invertible hT hinv)
