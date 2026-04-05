/-
  Section 9, Task 8.
  Prove that the power set of ℕ is uncountable.
-/
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

/-- The power set of ℕ is uncountable (Cantor's theorem). -/
theorem uncountable_powerset_nat : ¬ Countable (Set ℕ) := by
  intro h
  have h1 : Cardinal.mk (Set ℕ) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have h2 : Cardinal.aleph0 < Cardinal.mk (Set ℕ) := by
    rw [Cardinal.mk_set, Cardinal.mk_nat]
    exact Cardinal.cantor Cardinal.aleph0
  exact absurd h1 (not_le.mpr h2)
