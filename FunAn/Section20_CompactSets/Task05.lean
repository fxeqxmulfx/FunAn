/-
  Section 20, Task 05.
  A compact set in C¹[a,b] is also compact in C[a,b].
  The inclusion ι : C¹ → C is continuous (‖f‖_∞ ≤ ‖f‖_{C¹}),
  and continuous images of compact sets are compact.

  We formalize the abstract principle: continuous image of compact is compact.
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-- Continuous image of a compact set is compact (abstract version of
    "compact in C¹ implies compact in C"). -/
theorem compact_in_C1_compact_in_C
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {K : Set X} (hK : IsCompact K) :
    IsCompact (f '' K) :=
  hK.image hf
