/-
  Section 5, Task 7.
  If Φ ∈ C¹[a,b], then ∫f dΦ = ∫f·Φ'dx (RS integral = Riemann integral).

  The key connection: for a C¹ monotone Φ with derivative Φ', the Stieltjes
  measure of (a,b] is the integral of Φ':
    μ_Φ((a,b]) = Φ(b) - Φ(a) = ∫ₐᵇ Φ'(x) dx.
  The first equality is the Stieltjes measure definition; the second is FTC.
  This shows the Stieltjes integral ∫f dμ_Φ reduces to ordinary integration
  against the density Φ'.
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

open MeasureTheory intervalIntegral

/-- For C¹ monotone Φ, the Stieltjes measure μ_Φ((a,b]) = ∫ₐᵇ Φ'(x) dx.
    This connects the Stieltjes (RS) integral to ordinary Riemann/Lebesgue:
    ∫f dΦ = ∫f·Φ' dx, since dμ_Φ = Φ'·dx. -/
theorem stieltjes_measure_eq_integral_deriv
    (Φ : StieltjesFunction ℝ) {Φ' : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt Φ (Φ' x) x)
    (hint : IntervalIntegrable Φ' volume a b) :
    (Φ.measure (Set.Ioc a b)).toReal = ∫ x in a..b, Φ' x := by
  rw [Φ.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (Φ.mono hab))]
  exact (integral_eq_sub_of_hasDerivAt hderiv hint).symm
