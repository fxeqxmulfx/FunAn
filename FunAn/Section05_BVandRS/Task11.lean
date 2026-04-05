/-
  Section 5, Task 11.
  RS integral formula with jump discontinuities:
  ∫f dΦ = ∫fΦ'dx + f(a)[Φ(a+0)−Φ(a)] + f(b)[Φ(b)−Φ(b−0)]
         + Σf(cₘ)[Φ(cₘ+0)−Φ(cₘ−0)]

  The key ingredient is the Stieltjes jump formula: at each point c,
  the Stieltjes measure of the singleton {c} equals the jump of Φ:
    μ_Φ({c}) = Φ(c) - Φ(c−0).
  So the integral at an atom c gives: ∫_{c} f dμ_Φ = f(c)·(Φ(c)−Φ(c−)).
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

/-- The Stieltjes measure of a singleton equals the jump:
    μ_Φ({c}) = Φ(c) − Φ(c−0). -/
theorem stieltjes_measure_singleton (Φ : StieltjesFunction ℝ) (c : ℝ) :
    Φ.measure {c} = ENNReal.ofReal (Φ c - Function.leftLim Φ c) :=
  Φ.measure_singleton c

/-- Integral at a jump point: ∫_{c} f dμ_Φ = f(c) · (Φ(c) − Φ(c−)).
    This is the building block of the RS jump formula
    ∫f dΦ = Σ f(cₘ) · [Φ(cₘ+0) − Φ(cₘ−0)]. -/
theorem stieltjes_integral_singleton (Φ : StieltjesFunction ℝ) (f : ℝ → ℝ) (c : ℝ) :
    ∫ x in {c}, f x ∂Φ.measure = (Φ.measure.real {c}) • f c :=
  integral_singleton f c
