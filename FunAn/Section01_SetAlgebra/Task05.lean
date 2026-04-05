/-
  Section 1, Task 5.
  Show that a system of sets, closed under union and intersection,
  is not necessarily a ring (i.e., not necessarily closed under set difference).

  Counterexample: S = {∅, {1}, {1,2}, {1,2,3}} on the universe {1,2,3}.
  Closed under ∪ and ∩, but {1,2,3} \ {1,2} = {3} ∉ S.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic

open Finset

/-- The system S = {∅, {1}, {1,2}, {1,2,3}} is closed under union. -/
theorem setSystem_closedUnder_union :
    let S : Finset (Finset (Fin 3)) :=
      {∅, {0}, {0, 1}, {0, 1, 2}}
    ∀ A ∈ S, ∀ B ∈ S, A ∪ B ∈ S := by
  decide

/-- The system S is closed under intersection. -/
theorem setSystem_closedUnder_inter :
    let S : Finset (Finset (Fin 3)) :=
      {∅, {0}, {0, 1}, {0, 1, 2}}
    ∀ A ∈ S, ∀ B ∈ S, A ∩ B ∈ S := by
  decide

/-- But S is NOT closed under set difference: {0,1,2} \ {0,1} = {2} ∉ S. -/
theorem setSystem_not_closedUnder_sdiff :
    let S : Finset (Finset (Fin 3)) :=
      {∅, {0}, {0, 1}, {0, 1, 2}}
    ¬ (∀ A ∈ S, ∀ B ∈ S, A \ B ∈ S) := by
  decide
