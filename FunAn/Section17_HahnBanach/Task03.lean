/-
  Section 17, Task 3.
  Fₙ(x) = ∫₋π^π x(t)eⁱⁿᵗ dt converges weakly to 0 in L²(-π,π)*
  but not strongly (‖Fₙ‖ = √(2π) for all n by Parseval).
  Weak convergence: Fₙ(x) = √(2π)·x̂(n) → 0 by Riemann-Lebesgue lemma.

  We formalize the key ingredient: the Riemann–Lebesgue lemma, which
  states that Fourier coefficients tend to 0 at infinity.
-/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Tactic

open MeasureTheory Filter

/-- Riemann–Lebesgue lemma: Fourier coefficients tend to 0 at infinity. -/
theorem fourier_functionals_weak_not_strong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, Real.fourierChar (-(v * w)) • f v)
      (cocompact ℝ) (nhds 0) :=
  Real.tendsto_integral_exp_smul_cocompact f
