/-
  Section 11, Task 13.
  Show that α = 1 in Riesz's lemma cannot be achieved in general,
  but CAN be achieved in Hilbert spaces (best approximation theorem).

  In a Hilbert space, the orthogonal projection gives the closest point,
  so dist(x, F) is attained and Riesz's lemma holds with α = 1.
  In general normed spaces (e.g. C[-1,1]), the infimum may not be
  attained, so α = 1 fails.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Tactic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In a Hilbert space, closest point to a complete convex set exists
    (best approximation). This is why α = 1 works in Hilbert. -/
theorem best_approximation_hilbert
    {K : Set E} (hne : K.Nonempty) (hK : IsComplete K) (hconv : Convex ℝ K) (u : E) :
    ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - ↑w‖ :=
  exists_norm_eq_iInf_of_complete_convex hne hK hconv u

/-- In a Hilbert space, closest point to a complete subspace exists. -/
theorem best_approximation_subspace
    (K : Submodule ℝ E) (hK : IsComplete (K : Set E)) (u : E) :
    ∃ v ∈ (K : Set E), ‖u - v‖ = ⨅ w : (K : Set E), ‖u - ↑w‖ :=
  K.exists_norm_eq_iInf_of_complete_subspace hK u

/-- Riesz's lemma with α < 1 (the general version — α = 1 not always possible). -/
theorem riesz_lemma_alpha_lt_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : Subspace ℝ F} (hYc : IsClosed (Y : Set F)) (hY : ∃ x : F, x ∉ Y)
    {α : ℝ} (hα : α < 1) :
    ∃ x : F, x ∉ Y ∧ ∀ y ∈ (Y : Set F), α * ‖x‖ ≤ ‖x - y‖ :=
  riesz_lemma hYc hY hα
