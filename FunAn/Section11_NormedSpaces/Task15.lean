/-
  Section 11, Task 15.
  M = {x ∈ ℓ¹ : ‖x‖₂ ≤ 1} is not closed in ℓ².

  Proof: ℓ¹ ⊊ ℓ² — the harmonic sequence x(n) = 1/(n+1) is in ℓ²
  (since Σ 1/n² converges) but not in ℓ¹ (since Σ 1/n diverges).
  Its truncations are finitely supported (hence in ℓ¹ ∩ closedBall)
  and converge to x in ℓ², so M is not closed.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open scoped ENNReal

private lemma summable_harmonic_sq : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1))^2) := by
  have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ) < 2)
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2:ℝ)) 1).mpr h
  exact (show Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2:ℝ)) by simpa using this).congr
    (fun n => by simp [one_div, inv_pow])

private lemma not_summable_harmonic : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro h
  rw [show (fun n : ℕ => 1 / ((n : ℝ) + 1)) = (fun n : ℕ => 1 / (n : ℝ)) ∘ (· + 1) from by
    ext n; simp] at h
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h)

private lemma harmonic_memℓp2 : Memℓp (fun n : ℕ => 1 / ((n : ℝ) + 1)) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0:ℝ) < (2 : ℝ≥0∞).toReal)]
  exact summable_harmonic_sq.congr (fun n => by simp [Real.norm_eq_abs])

private lemma harmonic_not_memℓp1 : ¬ Memℓp (fun n : ℕ => 1 / ((n : ℝ) + 1)) 1 := by
  rw [memℓp_gen_iff (by norm_num : (0:ℝ) < (1 : ℝ≥0∞).toReal)]
  intro h
  exact not_summable_harmonic (h.congr (fun n => by
    simp only [Real.norm_eq_abs, ENNReal.toReal_one]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((n:ℝ) + 1)), Real.rpow_one]))

/-- The set M = {x ∈ ℓ² | x ∈ ℓ¹} is not closed in ℓ²: there exists
    a sequence in ℓ² \ ℓ¹ (the harmonic sequence 1/(n+1)).
    Its finite truncations lie in M and converge to it in ℓ². -/
theorem section11_task15 :
    ∃ f : ℕ → ℝ, Memℓp f 2 ∧ ¬ Memℓp f 1 :=
  ⟨_, harmonic_memℓp2, harmonic_not_memℓp1⟩
