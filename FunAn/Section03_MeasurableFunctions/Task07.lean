/-
  Section 3, Task 07.
  Two continuous functions on [a,b] that are equal almost everywhere
  (w.r.t. Lebesgue measure) are equal everywhere.
-/
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory

/-- Two continuous functions equal a.e. w.r.t. volume on ℝ are equal. -/
theorem continuous_ae_eq_implies_eq {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume] g) : f = g :=
  (hf.ae_eq_iff_eq volume hg).mp h
