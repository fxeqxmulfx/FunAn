/-
  Section 9, Task 2.
  Prove countability of the set of polynomials with rational coefficients.
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Tactic

-- AddMonoidAlgebra is def-equal to Finsupp, so we transfer the Countable instance
instance : Countable (AddMonoidAlgebra ℚ ℕ) :=
  inferInstanceAs (Countable (ℕ →₀ ℚ))

/-- Polynomial ℚ is countable. -/
instance : Countable (Polynomial ℚ) := by
  have hinj : Function.Injective
      (Polynomial.toFinsupp : Polynomial ℚ → AddMonoidAlgebra ℚ ℕ) := fun a b h => by
    cases a; cases b; exact congr_arg _ h
  exact hinj.countable

/-- The set of polynomials with rational coefficients is countable. -/
theorem countable_rat_polynomials :
    Set.Countable (Set.univ : Set (Polynomial ℚ)) :=
  Set.countable_univ
