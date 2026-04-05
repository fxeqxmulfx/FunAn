/-
  Section 9, Task 6.
  Prove that ℓ^∞ is not separable.

  Proof: For each S ⊆ ℕ, define e_S ∈ ℓ∞ by e_S(n) = 1 if n ∈ S, 0 otherwise.
  For S ≠ T, ‖e_S - e_T‖_∞ ≥ 1, so balls B(e_S, 1/3) are pairwise disjoint.
  In a separable space, pairwise disjoint open balls must be countable.
  But Set ℕ is uncountable (Cantor). Contradiction.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Bases
import Mathlib.Tactic

open scoped ENNReal
open Function

/-- ℓ^∞ is not separable. -/
theorem linfty_not_separable :
    ¬ TopologicalSpace.IsSeparable (Set.univ : Set (lp (fun _ : ℕ => ℝ) ⊤)) := by
  rw [TopologicalSpace.isSeparable_univ_iff]
  intro hsep
  -- Construct indicator elements in ℓ∞
  have hmem : ∀ S : Set ℕ, Memℓp (S.indicator (fun _ => (1 : ℝ))) ⊤ := by
    intro S; apply memℓp_infty; use 1; rintro _ ⟨i, rfl⟩
    exact norm_indicator_le_norm_self (fun _ => (1 : ℝ)) i |>.trans (by norm_num)
  set e : Set ℕ → lp (fun _ : ℕ => ℝ) ⊤ := fun S => ⟨S.indicator (fun _ => 1), hmem S⟩
  -- For S ≠ T, dist(e S, e T) ≥ 1
  have hdist : ∀ S T : Set ℕ, S ≠ T → 1 ≤ dist (e S) (e T) := by
    intro S T hST
    rw [dist_eq_norm, lp.norm_eq_ciSup]
    simp only [Ne, Set.ext_iff, not_forall] at hST
    obtain ⟨n, hn⟩ := hST
    apply le_ciSup_of_le (lp.memℓp (e S - e T)) n
    simp only [lp.coeFn_sub, Pi.sub_apply, e]
    rw [not_iff] at hn
    rcases Classical.em (n ∈ S) with hS | hS <;> simp_all
  -- The balls B(e S, 1/3) are pairwise disjoint nonempty open sets
  have hpw : Pairwise (Disjoint on fun S => Metric.ball (e S) (1/3 : ℝ)) := by
    intro S T hST; apply Metric.ball_disjoint_ball; linarith [hdist S T hST]
  -- By separability, the index set must be countable
  have hcount : Countable (Set ℕ) :=
    hpw.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
      (fun S => ⟨e S, Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/3)⟩)
  -- But Set ℕ is uncountable (Cantor's theorem)
  have h1 : Cardinal.mk (Set ℕ) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [Cardinal.mk_set] at h1
  simp only [Cardinal.aleph0, Cardinal.lift_id] at h1
  exact (Cardinal.cantor (Cardinal.mk ℕ)).2 h1
