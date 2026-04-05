/-
  Section 12, Task 9.
  L + M is not closed for specific closed subspaces where the angle
  between them tends to 0. Same abstract principle as Task 8:
  if L + M is dense but ≠ H, then L + M is not closed.
-/
import FunAn.Section12_HilbertSpaces.Task08
import Mathlib.Tactic

/-- L + M not closed: same principle as Task 8.
    If L⊔M is dense but ≠⊤, it cannot be closed. -/
theorem sum_subspaces_not_closed_principle
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L M : Submodule ℝ H)
    (hdense : Dense ((L ⊔ M : Submodule ℝ H) : Set H))
    (hne : L ⊔ M ≠ ⊤) :
    ¬IsClosed ((L ⊔ M : Submodule ℝ H) : Set H) :=
  Submodule.sum_not_isClosed_of_dense_ne_top L M hdense hne
