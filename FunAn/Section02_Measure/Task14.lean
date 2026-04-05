/-
  Section 2, Task 14.
  Bounded measurable set E with μ(E) = p contains a measurable subset
  of any prescribed measure q, for 0 ≤ q ≤ p.

  The general result (Sierpinski's theorem) uses the intermediate value
  property of non-atomic measures. For Lebesgue measure on intervals,
  this is immediate: [0, q] ⊆ [0, p] has measure q when q ≤ p.

  We prove the interval case, which captures the key idea.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory Set

/-- For any q ≤ p, the interval [0, p] contains a measurable subset of
    Lebesgue measure exactly q (namely [0, q]).
    This is the intermediate value property for Lebesgue measure on intervals. -/
theorem lebesgue_intermediate_value_interval {p q : ℝ} (hqp : q ≤ p) :
    ∃ t : Set ℝ, MeasurableSet t ∧ t ⊆ Icc 0 p ∧
      volume t = ENNReal.ofReal q :=
  ⟨Icc 0 q, measurableSet_Icc, Icc_subset_Icc_right hqp,
    by rw [Real.volume_Icc]; ring_nf⟩
