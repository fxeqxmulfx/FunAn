/-
  Section 5, Task 9.
  |∫ₐᵇ f dΦ| ≤ sup_{[a,b]} |f(x)| · Var_[a,b](Φ).

  For a monotone right-continuous Φ (StieltjesFunction) and bounded f:
  ‖∫_{(a,b]} f dμ_Φ‖ ≤ C · (Φ(b) - Φ(a)),
  where C bounds ‖f‖ on (a,b] and Φ(b)-Φ(a) = μ_Φ((a,b]) = Var(Φ,[a,b])
  for monotone Φ.
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

open MeasureTheory

/-- |∫f dΦ| ≤ sup|f| · Var(Φ) for Stieltjes integrals.
    For monotone Φ, Var(Φ,[a,b]) = Φ(b) - Φ(a) = μ_Φ((a,b]). -/
theorem stieltjes_integral_norm_le_sup_mul_var
    {a b : ℝ} (hab : a ≤ b) (Φ : StieltjesFunction ℝ)
    {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x ∈ Set.Ioc a b, ‖f x‖ ≤ C) :
    ‖∫ x in Set.Ioc a b, f x ∂Φ.measure‖ ≤ C * (Φ b - Φ a) := by
  have hfin : Φ.measure (Set.Ioc a b) < ⊤ := by
    rw [Φ.measure_Ioc]; exact ENNReal.ofReal_lt_top
  calc ‖∫ x in Set.Ioc a b, f x ∂Φ.measure‖
      ≤ C * Φ.measure.real (Set.Ioc a b) :=
        norm_setIntegral_le_of_norm_le_const hfin hf
    _ = C * (Φ b - Φ a) := by
        congr 1
        simp [Measure.real, Φ.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (Φ.mono hab))]
