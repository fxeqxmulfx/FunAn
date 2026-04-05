/-
  Section 19, Task 02.
  Examples of operator convergence types:
  (a) Uniform convergence: Aₙ = (1/n)·Id → 0 uniformly (‖Aₙ‖ = 1/n → 0).
  (b) Strong not uniform: Pₙ = projection onto span{e₁,...,eₙ} → Id strongly
      but not uniformly (‖Pₙ - Id‖ = 1 for all n).
  (c) Weak not strong: the basis vectors eₙ converge weakly to 0
      (coordinatewise) but not strongly (‖eₙ‖ = 1).

  We prove (c) via the ℓ² basis from Task04.
  For (a), we prove the abstract principle: scalar multiples cₙ·Id → 0
  iff cₙ → 0.
-/
import FunAn.Section19_OperatorConvergence.Task04
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

open Filter

/-- (a) Scalar multiples cₙ → 0 gives uniform operator convergence cₙ·Id → 0. -/
theorem uniform_convergence_example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℕ → ℝ} (hc : Tendsto c atTop (nhds 0)) :
    Tendsto (fun n => c n • ContinuousLinearMap.id ℝ E) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc ε hε
  exact ⟨N, fun n hn => by
    simp only [dist_zero_right]
    calc ‖c n • ContinuousLinearMap.id ℝ E‖
        = |c n| * ‖ContinuousLinearMap.id ℝ E‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |c n| * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = |c n| := mul_one _
      _ < ε := by
          have := hN n hn; rwa [dist_zero_right, Real.norm_eq_abs] at this⟩

/-- (c) Weak convergence without strong: eₙ in ℓ² (from Task04).
    eₙ does not converge strongly to 0 since ‖eₙ‖ = 1. -/
theorem weak_not_strong_example :
    ¬Tendsto (fun n => lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ)) atTop (nhds 0) :=
  l2_single_not_tendsto_zero
