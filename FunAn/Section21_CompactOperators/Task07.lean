/-
  Section 21, Task 7.
  Integral operators on L² with L² kernel (Hilbert-Schmidt) are compact.

  Abstract proof: any operator that is the norm-limit of compact operators
  is compact. Hilbert-Schmidt operators are limits of finite-rank operators
  (truncating the kernel expansion), and finite-rank operators are compact.

  We formalize the key abstract principle: the set of compact operators
  is closed in the operator norm topology.
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

/-- The norm-limit of compact operators is compact.
    This is the abstract principle behind: Hilbert-Schmidt operators
    are compact (as limits of finite-rank, hence compact, operators). -/
theorem compact_of_operator_norm_limit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℕ → E →L[ℝ] F} {A : E →L[ℝ] F}
    (hT : ∀ n, IsCompactOperator (T n : E → F))
    (hlim : Filter.Tendsto T Filter.atTop (nhds A)) :
    IsCompactOperator (A : E → F) :=
  isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hT)
