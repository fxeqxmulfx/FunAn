/-
  Section 3, Task 04.
  If g is measurable and f is continuous, then f ∘ g is measurable.
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

theorem measurable_comp_continuous {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hg : Measurable g) (hf : Continuous f) : Measurable (f ∘ g) :=
  hf.measurable.comp hg
