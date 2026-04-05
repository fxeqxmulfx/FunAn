/-
  Section 1, Task 8.
  Prove that [α, β] cannot be represented as the union of two non-empty,
  disjoint, closed sets. (Connectedness of [a,b].)
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Set in
/-- [a, b] is connected: not the union of two non-empty disjoint closed subsets. -/
theorem Icc_not_union_two_disjoint_closed (a b : ℝ) (hab : a ≤ b) :
    ¬ ∃ (S T : Set ℝ), IsClosed S ∧ IsClosed T ∧
      S.Nonempty ∧ T.Nonempty ∧ Disjoint S T ∧
      Icc a b = S ∪ T := by
  intro ⟨S, T, hSc, hTc, ⟨s, hs⟩, ⟨t, ht⟩, hST, hU⟩
  have hpc := isPreconnected_Icc (a := a) (b := b)
  rw [isPreconnected_closed_iff] at hpc
  -- S and T cover Icc a b
  have hcover : Icc a b ⊆ S ∪ T := hU ▸ Subset.rfl
  -- Both intersect Icc a b
  have hSne : (Icc a b ∩ S).Nonempty := by
    exact ⟨s, (hU ▸ mem_union_left T hs : s ∈ Icc a b), hs⟩
  have hTne : (Icc a b ∩ T).Nonempty := by
    exact ⟨t, (hU ▸ mem_union_right S ht : t ∈ Icc a b), ht⟩
  -- By preconnectedness, Icc a b ∩ (S ∩ T) is nonempty
  have h := hpc S T hSc hTc hcover hSne hTne
  -- But S ∩ T = ∅ since they're disjoint
  rw [hST.inter_eq] at h
  exact h.ne_empty (inter_empty _)
