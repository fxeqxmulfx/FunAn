/-
  Section 12, Task 8.
  There exist closed subspaces M, N of a Hilbert space such that M + N
  is not closed. The abstract principle: if M + N is dense but ≠ H,
  then M + N is not closed (since closed + dense = all of H).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-- If the sum of two subspaces is dense but not the whole space,
    then the sum is not closed. -/
theorem Submodule.sum_not_isClosed_of_dense_ne_top
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M N : Submodule ℝ H)
    (hdense : Dense ((M ⊔ N : Submodule ℝ H) : Set H))
    (hne : M ⊔ N ≠ ⊤) :
    ¬IsClosed ((M ⊔ N : Submodule ℝ H) : Set H) := by
  intro hclosed
  apply hne
  have h1 : closure ((M ⊔ N : Submodule ℝ H) : Set H) = Set.univ := hdense.closure_eq
  have h2 : closure ((M ⊔ N : Submodule ℝ H) : Set H) = (M ⊔ N : Submodule ℝ H) :=
    hclosed.closure_eq
  have : (M ⊔ N : Submodule ℝ H) = ⊤ := by
    rw [Submodule.eq_top_iff']; intro x
    have : x ∈ closure ((M ⊔ N : Submodule ℝ H) : Set H) := h1 ▸ Set.mem_univ x
    rwa [h2] at this
  exact this
