/-
  Section 09, Task 11.
  Non-separability of ℓ_∞ (alternative proof via uncountable 0-1 sequences).

  This is the same result as Task 06 but stated differently.
  The 0-1 indicator functions {eₛ : S ⊆ ℕ} satisfy ‖eₛ-eₜ‖_∞ = 1 for S ≠ T.
  Since 𝒫(ℕ) is uncountable, ℓ_∞ cannot be separable.
-/
import FunAn.Section09_Separable.Task06
import Mathlib.Tactic

open scoped ENNReal

/-- ℓ_∞ is not separable (via uncountable pairwise-distant family).
    Direct consequence of Task06's linfty_not_separable. -/
theorem linfty_not_separable_alt :
    ¬ TopologicalSpace.SeparableSpace (lp (fun _ : ℕ => ℝ) ⊤) := by
  intro h
  exact linfty_not_separable (TopologicalSpace.isSeparable_univ_iff.mpr h)
