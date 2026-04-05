/-
  Section 13, Task 04.
  F(x) = x'(0) + x(0) is continuous in C¹ norm but not C⁰ norm.

  Abstract principle: a functional bounded by one norm may be unbounded
  w.r.t. a weaker norm. Specifically, if ‖F(x)‖ ≤ C·‖x‖₁ for all x
  but there exist xₙ with ‖xₙ‖₂ → 0 and F(xₙ) ↛ 0, then F is
  continuous in ‖·‖₁ but not in ‖·‖₂.
-/
import Mathlib.Tactic

/-- A linear functional bounded w.r.t. one norm need not be bounded w.r.t. another.
    If there exists a sequence with ‖xₙ‖₂ → 0 but |F(xₙ)| ≥ c > 0,
    then F is not continuous w.r.t. ‖·‖₂. -/
theorem not_continuous_of_unbounded_seq
    {E : Type*} [AddCommGroup E]
    {τ : TopologicalSpace E}
    {F : E → ℝ}
    {x : ℕ → E} (hx : Filter.Tendsto x Filter.atTop (nhds 0))
    {c : ℝ} (hc : 0 < c) (hF : ∀ n, c ≤ |F (x n)|)
    (hF0 : F 0 = 0) :
    ¬Continuous F := by
  intro hcont
  have := (hcont.tendsto 0).comp hx
  simp only [Function.comp_def, hF0] at this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp this) c hc
  have := hN N le_rfl
  simp [Real.dist_eq] at this
  linarith [hF N]
