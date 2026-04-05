/-
  Section 1, Task 6.
  Prove that the direct product of semirings of sets is a semiring of sets.

  If S₁ on X₁ and S₂ on X₂ are semirings of sets (contain ∅, closed under ∩,
  and A \ B decomposes as a finite disjoint union), then
  Prod = {A ×ˢ B : A ∈ S₁, B ∈ S₂} is a semiring of sets on X₁ × X₂.
-/
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic

open MeasureTheory Set Finset

/-- The direct product of two set semirings is a set semiring. -/
theorem prod_isSetSemiring
    {α β : Type*} {S₁ : Set (Set α)} {S₂ : Set (Set β)}
    (h₁ : IsSetSemiring S₁) (h₂ : IsSetSemiring S₂) :
    IsSetSemiring {C : Set (α × β) | ∃ A ∈ S₁, ∃ B ∈ S₂, C = A ×ˢ B} where
  empty_mem := ⟨∅, h₁.empty_mem, ∅, h₂.empty_mem, by simp⟩
  inter_mem := by
    rintro _ ⟨A₁, hA₁, A₂, hA₂, rfl⟩ _ ⟨B₁, hB₁, B₂, hB₂, rfl⟩
    exact ⟨A₁ ∩ B₁, h₁.inter_mem A₁ hA₁ B₁ hB₁, A₂ ∩ B₂, h₂.inter_mem A₂ hA₂ B₂ hB₂,
           Set.prod_inter_prod⟩
  diff_eq_sUnion' := by
    classical
    rintro _ ⟨A₁, hA₁, A₂, hA₂, rfl⟩ _ ⟨B₁, hB₁, B₂, hB₂, rfl⟩
    obtain ⟨I₂, hI₂C, hI₂d, hI₂eq⟩ := h₂.diff_eq_sUnion' A₂ hA₂ B₂ hB₂
    obtain ⟨I₁, hI₁C, hI₁d, hI₁eq⟩ := h₁.diff_eq_sUnion' A₁ hA₁ B₁ hB₁
    let J₂ : Finset (Set (α × β)) := I₂.image (A₁ ×ˢ ·)
    let J₁ : Finset (Set (α × β)) := I₁.image (· ×ˢ (A₂ ∩ B₂))
    refine ⟨J₂ ∪ J₁, ?subset, ?disj, ?eq⟩
    case subset =>
      intro C hC
      simp only [J₁, J₂, coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image] at hC
      rcases hC with ⟨b, hb, rfl⟩ | ⟨a, ha, rfl⟩
      · exact ⟨A₁, hA₁, b, hI₂C hb, rfl⟩
      · exact ⟨a, hI₁C ha, A₂ ∩ B₂, h₂.inter_mem A₂ hA₂ B₂ hB₂, rfl⟩
    case disj =>
      rw [Finset.coe_union, pairwiseDisjoint_union]
      refine ⟨?_, ?_, ?_⟩
      · -- J₂ pairwise disjoint
        intro x hx y hy hne
        simp only [J₂, Finset.mem_coe, Finset.mem_image] at hx hy
        obtain ⟨b₁, hb₁, rfl⟩ := hx
        obtain ⟨b₂, hb₂, rfl⟩ := hy
        show Disjoint (A₁ ×ˢ b₁) (A₁ ×ˢ b₂)
        exact (Set.disjoint_prod.mpr (Or.inr (hI₂d hb₁ hb₂ (fun h => hne (by rw [h])))))
      · -- J₁ pairwise disjoint
        intro x hx y hy hne
        simp only [J₁, Finset.mem_coe, Finset.mem_image] at hx hy
        obtain ⟨a₁, ha₁, rfl⟩ := hx
        obtain ⟨a₂, ha₂, rfl⟩ := hy
        show Disjoint (a₁ ×ˢ (A₂ ∩ B₂)) (a₂ ×ˢ (A₂ ∩ B₂))
        exact (Set.disjoint_prod.mpr (Or.inl (hI₁d ha₁ ha₂ (fun h => hne (by rw [h])))))
      · -- Cross disjointness
        intro x hx y hy _
        simp only [J₂, J₁, Finset.mem_coe, Finset.mem_image] at hx hy
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨a, ha, rfl⟩ := hy
        show Disjoint (A₁ ×ˢ b) (a ×ˢ (A₂ ∩ B₂))
        apply Set.disjoint_prod.mpr
        right
        have hb_sub : b ⊆ A₂ \ B₂ := hI₂eq ▸ Set.subset_sUnion_of_mem (show b ∈ (↑I₂ : Set _) from hb)
        exact disjoint_sdiff_left.mono_right Set.inter_subset_right |>.mono_left hb_sub
    case eq =>
      have decomp : A₁ ×ˢ A₂ \ B₁ ×ˢ B₂ = A₁ ×ˢ (A₂ \ B₂) ∪ (A₁ \ B₁) ×ˢ (A₂ ∩ B₂) := by
        ext ⟨x, y⟩
        simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
        constructor
        · rintro ⟨⟨hx, hy⟩, hxy⟩
          by_cases hyB : y ∈ B₂
          · right; exact ⟨⟨hx, fun hxB => hxy ⟨hxB, hyB⟩⟩, hy, hyB⟩
          · left; exact ⟨hx, hy, hyB⟩
        · rintro (⟨hx, hy, hyB⟩ | ⟨⟨hx, hxB⟩, hy, hyB⟩)
          · exact ⟨⟨hx, hy⟩, fun ⟨_, hyB'⟩ => hyB hyB'⟩
          · exact ⟨⟨hx, hy⟩, fun ⟨hxB', _⟩ => hxB hxB'⟩
      have eq₂ : A₁ ×ˢ (A₂ \ B₂) = ⋃₀ ↑J₂ := by
        simp only [J₂, Finset.coe_image, Set.sUnion_image]
        rw [hI₂eq, Set.sUnion_eq_biUnion, Set.prod_iUnion₂]
      have eq₁ : (A₁ \ B₁) ×ˢ (A₂ ∩ B₂) = ⋃₀ ↑J₁ := by
        simp only [J₁, Finset.coe_image, Set.sUnion_image]
        rw [hI₁eq, Set.sUnion_eq_biUnion, Set.iUnion₂_prod_const]
      rw [decomp, eq₂, eq₁, ← Set.sUnion_union, ← Finset.coe_union]
