/-
  Section 2, Task 13.
  (a) μ_F([a,b)) = F(b) - F(a) defines a measure on half-open intervals
      when F is non-decreasing and right-continuous.
  (b) The distribution function F_μ is non-decreasing.
  (c) σ-additivity on the semiring ↔ right-continuity of F.
  These are the fundamental properties of Lebesgue–Stieltjes measures,
  available in Mathlib as StieltjesFunction.
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

open MeasureTheory

/-- A Stieltjes function defines a Borel measure on ℝ with
    μ(Ioc a b) = F(b) - F(a). -/
theorem lebesgue_stieltjes_measure_Ioc (f : StieltjesFunction ℝ) (a b : ℝ) :
    f.measure (Set.Ioc a b) = ENNReal.ofReal (f b - f a) :=
  f.measure_Ioc a b

/-- A Stieltjes function is monotone (the distribution function is non-decreasing). -/
theorem lebesgue_stieltjes_monotone (f : StieltjesFunction ℝ) :
    Monotone f :=
  f.mono
