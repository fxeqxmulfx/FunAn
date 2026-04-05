/-
  Section 5, Task 10.
  The RS integral of a continuous function does not depend on the
  values of the integrator Φ at finitely many interior points.

  In the Stieltjes framework, this is automatic: a StieltjesFunction
  is right-continuous, so its measure μ_Φ((a,b]) = Φ(b) - Φ(a) depends
  only on Φ's values, which equal its right limits. The integral
  ∫f dμ_Φ is determined by the measure, hence by right limits of Φ.

  Concretely: modifying f at a finite (hence null) set doesn't change
  the integral w.r.t. any atomless measure. For a continuous integrator Φ,
  μ_Φ has no atoms (μ_Φ({c}) = Φ(c) - Φ(c−) = 0), so finite sets are null.
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

/-- For a continuous monotone Φ, the Stieltjes measure has no atoms:
    μ_Φ({c}) = 0 when Φ is continuous (left limit = value). -/
theorem stieltjes_no_atom_of_continuous (Φ : StieltjesFunction ℝ)
    (hΦ : Continuous (Φ : ℝ → ℝ)) (c : ℝ) :
    Φ.measure {c} = 0 := by
  rw [Φ.measure_singleton]
  have : Function.leftLim (Φ : ℝ → ℝ) c = Φ c :=
    (hΦ.continuousAt.continuousWithinAt).leftLim_eq
  simp [this]

/-- If f = g a.e. with respect to μ, then ∫f dμ = ∫g dμ.
    For a continuous integrator Φ, singletons are null, so modifying
    the integrand at finitely many interior points doesn't change ∫f dμ_Φ. -/
theorem integral_eq_of_ae_eq_stieltjes
    {Φ : StieltjesFunction ℝ}
    {f g : ℝ → ℝ} (h : f =ᵐ[Φ.measure] g) :
    ∫ x, f x ∂Φ.measure = ∫ x, g x ∂Φ.measure :=
  integral_congr_ae h
