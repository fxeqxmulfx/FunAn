/-
  Section 08, Task 04.
  Balls B[n, 1+1/(2n)] in (ℕ, ρ) are closed, nested, but have empty intersection.
  The sets {m : m ≥ n} are nested and their intersection is empty.
  This shows the nested closed balls theorem requires diam → 0.
-/
import Mathlib.Tactic

/-- The intersection ⋂ₙ {m ∈ ℕ : m ≥ n} is empty: no natural number
    is ≥ all natural numbers. -/
theorem section08_task04 : ⋂ n : ℕ, {m : ℕ | n ≤ m} = ∅ := by
  ext m
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  push Not
  exact ⟨m + 1, by omega⟩
