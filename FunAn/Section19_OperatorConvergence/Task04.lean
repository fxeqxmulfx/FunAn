/-
  Section 19, Task 04.
  Aₙ → 0 strongly does NOT imply Aₙ* → 0 strongly.

  Witness: eₙ = lp.single 2 n 1 in ℓ². The sequence (eₙ) converges
  weakly to 0 (⟨eₙ, y⟩ = yₙ → 0 for any y ∈ ℓ²) but ‖eₙ‖ = 1 ↛ 0.
  Applied to rank-1 operators Aₙx = ⟨x,eₙ⟩e₁: Aₙ→0 strongly but
  Aₙ*y = ⟨y,e₁⟩eₙ does NOT converge strongly (‖Aₙ*e₁‖ = 1).
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

open scoped InnerProductSpace ENNReal
open Filter

/-- Standard basis vectors eₙ in ℓ² do not converge strongly to 0. -/
theorem l2_single_not_tendsto_zero :
    let e : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun n => lp.single 2 n (1 : ℝ)
    ¬Tendsto e atTop (nhds 0) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  intro e h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h 1 one_pos
  have h2 := hN N le_rfl
  simp only [e, dist_zero_right, lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2),
    norm_one] at h2
  linarith

/-- But for any fixed y ∈ ℓ², ⟨eₙ, y⟩ → 0
    (coordinates of a square-summable sequence tend to 0). -/
theorem l2_coord_tendsto_zero (y : lp (fun _ : ℕ => ℝ) 2) :
    Tendsto (fun n => (y : ℕ → ℝ) n) atTop (nhds 0) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- ‖y‖² = Σ (y k)², which converges, so tail → 0
  have hsq : Summable (fun k => (y k : ℝ) ^ 2) := by
    have := (lp.memℓp y).summable (show 0 < (2:ℝ≥0∞).toReal by norm_num)
    exact this.congr fun k => by simp [ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
  have htail := hsq.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail (ε ^ 2) (by positivity)
  exact ⟨N, fun n hn => by
    have h1 := hN n hn
    simp only [dist_zero_right, Real.norm_eq_abs] at h1
    rw [dist_zero_right, Real.norm_eq_abs]
    by_contra h2; push_neg at h2
    have h3 : ε ^ 2 ≤ ((y : ℕ → ℝ) n) ^ 2 := by nlinarith [sq_abs ((y : ℕ → ℝ) n)]
    have h4 : |((y : ℕ → ℝ) n) ^ 2| = ((y : ℕ → ℝ) n) ^ 2 := abs_of_nonneg (sq_nonneg _)
    linarith⟩
