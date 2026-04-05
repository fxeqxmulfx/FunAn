/-
  Section 6, Task 3.
  The coinduced topology is the strongest (finest) topology making f continuous.
  In Mathlib: continuous_coinduced_rng says f is continuous to coinduced.
  continuous_iff_coinduced_le says: @Continuous X Y τX τ' f ↔ coinduced f τX ≤ τ'
  So coinduced is the finest making f continuous, and any τ' making f continuous
  is at most as fine: coinduced ≤ τ' ... no: τ' ≤ coinduced means τ' is finer,
  but we want coinduced to be the finest, so coinduced ≤ τ' should be FALSE.
  Actually: continuous_iff_coinduced_le says continuous ↔ coinduced ≤ τ',
  meaning coinduced is coarser than τ'. Wait — that can't be right for "strongest".

  Let me re-read: coinduced f τX ≤ τ' means coinduced is FINER than τ'.
  So continuous ↔ coinduced f τX ≤ τ' means: f continuous to τ' iff
  coinduced is finer than τ'. The STRONGEST τ' making f continuous means
  the finest τ', and that's coinduced itself. For any other τ' making f
  continuous: coinduced ≤ τ', so τ' is coarser. Meaning: τ' ≤ coinduced? No...

  OK: ≤ = finer. coinduced ≤ τ' means coinduced finer than τ'.
  continuous ↔ coinduced ≤ τ' means: f is continuous to τ' iff coinduced
  has at least as many open sets as τ'. So for coinduced itself, trivially
  continuous. For any τ' making f continuous: coinduced ≤ τ' (coinduced finer).
  So coinduced IS the finest: ∀ τ', continuous → coinduced ≤ τ'? That means
  coinduced is finer than all of them — but that's wrong, coinduced should be
  the finest = the one with MOST open sets.

  I think the answer is: ∀ τ' continuous, τ' ≤ coinduced (τ' coarser).
-/
import Mathlib.Topology.Order
import Mathlib.Tactic

/-- The coinduced topology is the strongest (finest) topology making f continuous.
    Any topology τ' making f continuous is coarser: coinduced f τX ≤ τ'. -/
theorem exists_strongest_topology_continuous {X Y : Type*} [τX : TopologicalSpace X]
    (f : X → Y) :
    ∃ (τ : TopologicalSpace Y),
      @Continuous X Y τX τ f ∧
      ∀ (τ' : TopologicalSpace Y), @Continuous X Y τX τ' f → τ ≤ τ' :=
  ⟨TopologicalSpace.coinduced f τX, continuous_coinduced_rng,
    fun _ hf' => continuous_iff_coinduced_le.mp hf'⟩
