/-
  Section 09, Task 09.
  A separable complete metric space has cardinality at most continuum.

  Proof: A nonempty Polish space X admits a continuous surjection from ℕ → ℕ
  (Baire space). Hence #X ≤ #(ℕ → ℕ) = ℵ₀^ℵ₀ = 2^ℵ₀ = 𝔠.
-/
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal

/-- A nonempty Polish space has cardinality at most continuum. -/
theorem polish_card_le_continuum
    (X : Type) [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X] :
    Cardinal.mk X ≤ Cardinal.continuum := by
  -- There exists a continuous surjection (ℕ → ℕ) → X
  obtain ⟨f, _, hf⟩ := PolishSpace.exists_nat_nat_continuous_surjective X
  calc Cardinal.mk X
      ≤ Cardinal.mk (ℕ → ℕ) := mk_le_of_surjective hf
    _ ≤ Cardinal.continuum := by
        unfold Cardinal.continuum
        simp only [mk_arrow, mk_nat, Cardinal.lift_id]
        exact Cardinal.aleph0_power_aleph0.le
