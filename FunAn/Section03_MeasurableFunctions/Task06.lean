/-
  Section 3, Task 6.
  Prove that convergence almost everywhere on a measurable set E
  implies convergence in measure on E.
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/-- Convergence a.e. implies convergence in measure on a finite measure set.
    This is `MeasureTheory.tendstoInMeasure_of_tendsto_ae` in Mathlib
    (for finite measures). -/
theorem ae_tendsto_implies_tendsto_in_measure
    {f : ℕ → α → ℝ} {g : α → ℝ}
    [MeasureTheory.IsFiniteMeasure μ]
    (hf : ∀ n, MeasureTheory.AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    MeasureTheory.TendstoInMeasure μ f Filter.atTop g :=
  MeasureTheory.tendstoInMeasure_of_tendsto_ae hf hfg
