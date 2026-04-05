/-
  Section 1, Task 12.
  Prove that the Cantor set has the cardinality of the continuum.

  Proof: Mathlib provides `cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (ℕ → Bool)`,
  so #cantorSet = #(ℕ → Bool) = 2^ℵ₀ = continuum.
-/
import Mathlib.Topology.Instances.CantorSet
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-- The Cantor set has the cardinality of the continuum. -/
theorem cantor_set_card_eq_continuum :
    Cardinal.mk cantorSet = Cardinal.continuum := by
  -- cantorSet ≃ₜ (ℕ → Bool) gives an equivalence
  rw [Cardinal.mk_congr cantorSetHomeomorphNatToBool.toEquiv]
  -- #(ℕ → Bool) = 2^ℵ₀ = continuum
  rw [Cardinal.continuum, Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.lift_ofNat,
      Cardinal.lift_id, Cardinal.aleph0]
  simp [Cardinal.lift_id]
