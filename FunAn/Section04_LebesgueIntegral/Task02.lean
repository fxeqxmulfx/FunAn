/-
  Section 4, Task 2.
  Lebesgue integrability of bounded measurable f on finite measure E is
  equivalent to existence of the limit F(f) = lim Σηₖμ(Eₖ) as the partition
  mesh → 0, and ∫f = F(f).

  Part 1: bounded + a.e. strongly measurable on finite measure ⟹ integrable.
  Part 2: ∫f dμ = lim_n Σηₖ·μ(Eₖ), i.e., the Lebesgue integral is the
           limit of integrals of approximating simple functions (Lebesgue sums).
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Order.Filter.AtTopBot.Monoid
import Mathlib.Tactic

open scoped ENNReal
open MeasureTheory Filter SimpleFunc Topology

/-- Part 1: On a finite measure space, bounded + a.e. strongly measurable ⟹ integrable. -/
theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf C hbound

/-- Part 2: The Lebesgue integral equals the supremum of integrals of
    approximating simple functions: ∫⁻ f dμ = ⨆ₙ (Σηₖ·μ(Eₖ))ₙ.
    Each (eapprox f n).lintegral μ is a Lebesgue sum Σηₖ·μ(Eₖ). -/
theorem lintegral_eq_sup_simple_sums
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (eapprox f n).lintegral μ :=
  lintegral_eq_iSup_eapprox_lintegral hf

/-- The simple function Lebesgue sums converge to the integral as a limit
    (monotone sequence with supremum = integral). -/
theorem tendsto_simple_sums_lintegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    Tendsto (fun n => (eapprox f n).lintegral μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact tendsto_atTop_iSup fun n m hnm =>
    SimpleFunc.lintegral_mono (monotone_eapprox f hnm) le_rfl
