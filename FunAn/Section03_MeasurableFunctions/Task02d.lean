/-
  Section 3, Task 02d.
  A function of bounded variation on [a,b] is Lebesgue measurable.
  Proof: BV = difference of two monotone (Jordan decomposition), each monotone
  function is measurable, and the difference of measurable functions is measurable.
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-- A function of bounded variation on [a,b] is measurable on [a,b].
    The restriction to the subtype Set.Icc a b is measurable. -/
theorem bv_function_measurable_on {a b : ℝ} {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc a b)) :
    Measurable (Set.restrict (Set.Icc a b) f) := by
  -- Jordan decomposition: f = p - q with p, q monotone on [a,b]
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  -- Monotone on [a,b] → restriction to subtype is monotone → measurable
  have hp_meas : Measurable (Set.restrict (Set.Icc a b) p) :=
    (show Monotone (Set.restrict (Set.Icc a b) p) from
      fun ⟨_, hx⟩ ⟨_, hy⟩ hle => hp hx hy hle).measurable
  have hq_meas : Measurable (Set.restrict (Set.Icc a b) q) :=
    (show Monotone (Set.restrict (Set.Icc a b) q) from
      fun ⟨_, hx⟩ ⟨_, hy⟩ hle => hq hx hy hle).measurable
  -- f = p - q on [a,b], so restrict f = restrict p - restrict q
  convert hp_meas.sub hq_meas using 1
  ext ⟨x, _⟩
  simp [Set.restrict, hpq]
