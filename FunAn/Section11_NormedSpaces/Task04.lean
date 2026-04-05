/-
  Section 11, Task 4.
  Prove that ℓ^p ⊂ ℓ^q when p < q.
  (In Mathlib's convention, larger exponent means weaker condition,
   so lp E p ≤ lp E q when p ≤ q.)
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

open scoped ENNReal

/-- ℓ^p ⊆ ℓ^q when p ≤ q. -/
theorem lp_subset_lq {p q : ℝ≥0∞} (hpq : p ≤ q)
    (f : lp (fun _ : ℕ => ℝ) p) : Memℓp (↑f : ℕ → ℝ) q :=
  lp.monotone hpq f.prop
