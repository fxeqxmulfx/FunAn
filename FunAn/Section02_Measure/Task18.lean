/-
  Section 2, Task 18.
  If A is non-measurable and μ(B) = 0, then A \ B is non-measurable.
  (Here "measurable" means null-measurable w.r.t. μ.)
  Proof: If A \ B were null-measurable, then since A = (A \ B) ∪ (A ∩ B)
  and A ∩ B ⊆ B has measure 0, A would be null-measurable — contradiction.
-/
import Mathlib.MeasureTheory.Measure.NullMeasurable

open MeasureTheory Set

theorem diff_nonmeasurable_of_null {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : Set α} (hA : ¬NullMeasurableSet A μ) (hB : μ B = 0) :
    ¬NullMeasurableSet (A \ B) μ := by
  intro h
  apply hA
  have hAB : A = (A \ B) ∪ (A ∩ B) := by ext x; simp
  rw [hAB]
  exact h.union (.of_null (measure_mono_null inter_subset_right hB))
