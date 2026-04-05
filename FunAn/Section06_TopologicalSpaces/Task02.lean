/-
  Section 6, Task 2.
  The induced topology is the weakest topology making f continuous.
  In Mathlib, τ₁ ≤ τ₂ means τ₁ is finer (more open sets).
  So "τ is weakest" means: for all τ' making f continuous, τ' ≤ τ is FALSE;
  rather τ ≤ τ' ... no: weakest = fewest open sets = every other has MORE = τ' ≤ τ.
  Actually: τ₁ ≤ τ₂ means IsOpen[τ₂] s → IsOpen[τ₁] s, so ≤ = "finer".
  Weakest = coarsest = least finer = ∀ τ', continuous → τ' ≤ τ? No...

  In Mathlib: continuous_iff_le_induced : @Continuous X Y τ' τY f ↔ τ' ≤ induced f τY
  This says: f is continuous from τ' iff τ' is finer than induced.
  So induced is the COARSEST making f continuous, and any τ' making f continuous
  is at least as fine: τ' ≤ induced. But ≤ means "finer", so this is exactly right.
-/
import Mathlib.Topology.Order
import Mathlib.Tactic

/-- The induced topology is the weakest (coarsest) topology making f continuous.
    Any topology τ' making f continuous is finer: τ' ≤ induced f τY. -/
theorem exists_weakest_topology_continuous {X Y : Type*} [τY : TopologicalSpace Y]
    (f : X → Y) :
    ∃ (τ : TopologicalSpace X),
      @Continuous X Y τ τY f ∧
      ∀ (τ' : TopologicalSpace X), @Continuous X Y τ' τY f → τ' ≤ τ :=
  ⟨TopologicalSpace.induced f τY, continuous_induced_dom,
    fun _ hf' => continuous_iff_le_induced.mp hf'⟩
