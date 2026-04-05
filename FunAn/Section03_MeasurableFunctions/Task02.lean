/-
  Section 3, Task 2.
  Prove that:
  a) a monotone function on [a,b] is measurable;
  b) continuous functions are measurable;
  c) the sum of two measurable functions is measurable;
  d) a function of bounded variation on [a,b] is measurable.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic

/-- (b) Continuous functions are (Borel) measurable. -/
theorem continuous_implies_measurable {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : α → β} (hf : Continuous f) : Measurable f :=
  hf.measurable

/-- (c) The sum of two measurable functions is measurable. -/
theorem measurable_add {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) :=
  hf.add hg
