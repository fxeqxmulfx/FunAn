/-
  Section 19, Task 03.
  Left shift Sₙ on ℓ²: (Sₙx)ₖ = x_{k+n}.
  Key property: Sₙ → 0 strongly.

  Proof ingredient: for x ∈ ℓ², each coordinate x_k → 0 as k → ∞
  (from Task04: l2_coord_tendsto_zero). The shift (Sₙx)ₖ = x_{k+n}
  has the same coordinates shifted, so each coordinate → 0.

  We also note: Sₙ has ‖Sₙ‖ ≤ 1 (it's a contraction), and
  Sₙ*Sₙ = Id (right shift composed with left shift is identity on ℓ²).
-/
import FunAn.Section19_OperatorConvergence.Task04
import Mathlib.Tactic

open scoped ENNReal
open Filter

/-- Each coordinate of x ∈ ℓ² tends to 0.
    The left shift Sₙ maps x to (x_{n}, x_{n+1}, ...),
    so (Sₙx)_0 = x_n → 0 for any fixed coordinate. -/
theorem l2_shifted_coord_tendsto_zero
    (x : lp (fun _ : ℕ => ℝ) 2) (k : ℕ) :
    Tendsto (fun n => (x : ℕ → ℝ) (k + n)) atTop (nhds 0) := by
  have h := l2_coord_tendsto_zero x
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN (k + n) (by omega)⟩
