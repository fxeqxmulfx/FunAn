/-
  Section 20, Task 3.
  Sets of integral transforms are compact in C[a,b] by Arzelà-Ascoli:
  equicontinuous + pointwise compact ⟹ compact in C(X, α).

  Applied to integral transforms: the image of a bounded set under an
  integral operator is equicontinuous (by uniform continuity of the kernel)
  and uniformly bounded, hence has compact closure in C[a,b].
-/
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Tactic

/-- Arzelà-Ascoli theorem: an equicontinuous set with pointwise compact
    image is compact in C(X, α). This is the key tool for proving
    integral transform sets are compact in C[a,b]. -/
theorem arzela_ascoli_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {α : Type*} [UniformSpace α] [T2Space α]
    (S : Set C(X, α))
    (hpw : IsCompact (ContinuousMap.toFun '' S))
    (heq : Equicontinuous ((↑) : S → X → α)) :
    IsCompact S :=
  ArzelaAscoli.isCompact_of_equicontinuous S hpw heq
