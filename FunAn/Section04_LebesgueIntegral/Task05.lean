/-
  Section 04, Task 05.
  Question: Does ∫fₙdμ → 0 imply fₙ → 0 a.e.?
  Answer: NO (typewriter counterexample).

  The positive direction IS true with extra hypotheses:
  Dominated convergence: fₙ→f a.e. + |fₙ|≤g integrable ⟹ ∫fₙ→∫f.
  We formalize this and note the converse fails.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open MeasureTheory Filter

/-- Dominated convergence theorem: the positive direction.
    fₙ → f a.e. + dominated ⟹ ∫fₙ → ∫f.
    The CONVERSE fails: ∫fₙ → 0 does NOT imply fₙ → 0 a.e.
    (counterexample: typewriter sequence on [0,1]). -/
theorem dominated_convergence_positive_direction
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {bound : α → ℝ}
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : Integrable bound μ)
    (h_dom : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hF_meas hbound h_dom h_lim
