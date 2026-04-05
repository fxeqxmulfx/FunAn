/-
  Section 1, Task 10.
  The Cantor set consists of points in [0,1] whose ternary expansion
  uses only digits 0 and 2 (no digit 1).

  Mathlib has `cantorSet` and `cantorSetEquivNatToBool` which establishes
  the bijection between the Cantor set and {0,2}^ℕ ≅ Bool^ℕ.
  The characterization via ternary digits is encoded in
  `ofDigits_zero_two_sequence_mem_cantorSet`.
-/
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Tactic

/-- Points of the Cantor set are exactly those with ternary digits in {0,2}.
    This is witnessed by the homeomorphism cantorSetHomeomorphNatToBool. -/
theorem cantor_set_ternary_characterization :
    Nonempty (cantorSet ≃ₜ (ℕ → Bool)) :=
  ⟨cantorSetHomeomorphNatToBool⟩
