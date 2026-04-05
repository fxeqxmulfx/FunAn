/-
  Section 11, Task 5.
  For 1 <= p < q <= infty, Lq(a,b) is a subset of Lp(a,b) on a finite measure space.
  Proof: Holder's inequality with exponents q/p and q/(q-p) gives
  the norm bound. In Mathlib this is MeasureTheory.MemLp.mono_exponent.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

open MeasureTheory

/-- On a finite measure space, Lq is a subset of Lp when p le q. -/
theorem Lq_subset_Lp_finite_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} {p q : ENNReal} (hpq : p ≤ q) (hf : MemLp f q μ) :
    MemLp f p μ :=
  hf.mono_exponent hpq
