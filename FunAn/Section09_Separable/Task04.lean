/-
  Section 09, Task 04.
  B (finite sequences) is nowhere dense in ℓᵖ.

  Each Bₙ = {x ∈ ℓᵖ : xₖ = 0 for k > n} is a closed proper subspace.
  A proper closed submodule of a topological vector space has empty interior,
  hence is nowhere dense. This is the abstract content behind the result.

  In Mathlib: Submodule.eq_top_of_nonempty_interior' shows that the only
  submodule with nonempty interior is ⊤.
-/
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

open scoped Topology

/-- A proper submodule of a topological module (over a nontrivially normed field)
    has empty interior, hence is nowhere dense. -/
theorem section09_task04
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    (s : Submodule 𝕜 E) (hs : s ≠ ⊤) :
    interior (s : Set E) = ∅ := by
  haveI : Filter.NeBot (𝓝[{x : 𝕜 | IsUnit x}] (0 : 𝕜)) :=
    NormedField.nhdsWithin_isUnit_neBot
  by_contra h
  apply hs
  apply s.eq_top_of_nonempty_interior'
  exact Set.nonempty_iff_ne_empty.mpr h
