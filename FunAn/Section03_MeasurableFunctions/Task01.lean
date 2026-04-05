/-
  Section 3, Task 1.
  If f is measurable on E and E₁ is a measurable subset of E,
  then f is measurable on E₁.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Restriction of a measurable function to a measurable subset is measurable. -/
theorem measurable_restrict_of_measurable {f : α → β}
    (hf : Measurable f) {E₁ : Set α} (_hE₁ : MeasurableSet E₁) :
    Measurable (E₁.restrict f) :=
  hf.comp measurable_subtype_coe
