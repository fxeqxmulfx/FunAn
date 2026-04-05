/-
  Section 4, Task 4.
  If Φ has a derivative a.e. on [a,b] and Φ' is bounded, then Φ' is
  Lebesgue integrable on [a,b].

  Key ingredients:
  1. deriv f is always Lebesgue measurable (measurable_deriv)
  2. On a finite measure space, bounded + measurable ⟹ integrable
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

open MeasureTheory

/-- The derivative of any ℝ → ℝ function is measurable. -/
theorem deriv_measurable' (f : ℝ → ℝ) : Measurable (deriv f) :=
  measurable_deriv f

/-- Bounded derivative on a finite-measure space is integrable. -/
theorem deriv_integrable_of_bounded
    {f : ℝ → ℝ} {C : ℝ} (hbound : ∀ᵐ x ∂(volume : Measure ℝ), ‖deriv f x‖ ≤ C)
    {s : Set ℝ} (hfin : volume s ≠ ⊤) :
    IntegrableOn (deriv f) s volume := by
  haveI : IsFiniteMeasure (volume.restrict s) := by
    constructor; rw [Measure.restrict_apply_univ]; exact hfin.lt_top
  exact Integrable.of_bound
    (μ := volume.restrict s)
    ((measurable_deriv f).aestronglyMeasurable.restrict)
    C (ae_restrict_of_ae hbound)
