/-
  Section 03, Task 05.
  Question: g continuous, f Lebesgue measurable — is f∘g measurable?
  Answer: NOT necessarily (Cantor function counterexample).

  However, f∘g IS measurable when f is BOREL measurable (not just Lebesgue).
  The distinction: continuous functions preserve Borel sets but may map
  Borel sets to non-Borel Lebesgue-measurable sets.

  We formalize the positive case: Borel measurable ∘ continuous = measurable.
  The failure for Lebesgue measurability requires the Cantor function
  (a concrete construction not formalized here).
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-- f Borel measurable + g continuous ⟹ f∘g measurable.
    This FAILS when "Borel" is replaced by "Lebesgue" measurable
    (counterexample: Cantor function). -/
theorem borel_measurable_comp_continuous
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {γ : Type*} [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    {f : β → γ} (hf : Measurable f) {g : α → β} (hg : Continuous g) :
    Measurable (f ∘ g) :=
  hf.comp hg.measurable
