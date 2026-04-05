/-
  Section 21, Task 03.
  A compact operator maps bounded sequences to sequences with
  convergent subsequences (sequential characterization, forward direction).

  Proof: If A is compact and (xₙ) is bounded, then (Axₙ) lies in
  A(closedBall 0 R) whose closure is compact, hence (Axₙ) has a
  convergent subsequence by sequential compactness.
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Sequences
import Mathlib.Tactic

open Filter

/-- A compact operator maps bounded sequences to sequences with
    convergent subsequences. -/
theorem IsCompactOperator.exists_convergent_subseq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →L[ℝ] F} (hA : IsCompactOperator (A : E → F))
    {x : ℕ → E} {R : ℝ} (hR : 0 < R) (hx : ∀ n, ‖x n‖ ≤ R) :
    ∃ y : F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => A (x (φ n))) atTop (nhds y) := by
  -- A(closedBall 0 R) has compact closure
  have hK := hA.isCompact_closure_image_of_bounded (S := Metric.closedBall (0 : E) R)
    Metric.isBounded_closedBall
  -- x n ∈ closedBall 0 R
  have hxball : ∀ n, x n ∈ Metric.closedBall (0 : E) R := by
    intro n; rw [Metric.mem_closedBall, dist_zero_right]; exact hx n
  -- A(x n) ∈ closure(A '' closedBall 0 R)
  have hAx : ∀ n, A (x n) ∈ closure (A '' Metric.closedBall 0 R) :=
    fun n => subset_closure (Set.mem_image_of_mem A (hxball n))
  -- Sequential compactness from compactness
  have hseq : IsSeqCompact (closure (A '' Metric.closedBall 0 R)) :=
    isCompact_iff_isSeqCompact.mp hK
  obtain ⟨y, -, φ, hφ, hconv⟩ := hseq hAx
  exact ⟨y, φ, hφ, hconv⟩
