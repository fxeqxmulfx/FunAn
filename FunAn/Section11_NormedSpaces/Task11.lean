/-
  Section 11, Task 11.
  Riesz's lemma: For a closed proper subspace F of a normed space E,
  for any r < 1, there exists x₀ with ‖x₀‖ = 1 and dist(x₀, F) ≥ r.
-/
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Tactic

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Riesz's lemma from Mathlib. -/
theorem riesz_lemma_statement (F : Subspace 𝕜 E) (hFc : IsClosed (F : Set E))
    (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ :=
  riesz_lemma hFc hF hr
