/-
  Section 12, Task 17.
  If M is dense in H, then M⊥ = {0}.
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- If M is dense in H, then M⊥ = ⊥.
    Proof: M⊥ = (closure M)⊥ = ⊤⊥ = ⊥. -/
theorem orthogonal_eq_bot_of_dense' (M : Submodule ℝ H)
    (hM : M.topologicalClosure = ⊤) :
    M.orthogonal = ⊥ := by
  rw [← Submodule.orthogonal_closure M, hM, Submodule.top_orthogonal_eq_bot]
