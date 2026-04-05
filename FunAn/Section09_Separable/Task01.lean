/-
  Section 9, Task 1.
  Prove countability of the set of finite sequences with rational members.
-/
import Mathlib.Data.Rat.Denumerable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-- The set of finite rational sequences is countable. -/
theorem countable_finite_rat_sequences :
    Set.Countable (Set.univ : Set (List ℚ)) :=
  Set.countable_univ
