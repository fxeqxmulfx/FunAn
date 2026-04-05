/-
  Section 7, Task 6.
  Prove continuity of the function f(x) = ρ(x, A).
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

variable {X : Type*} [PseudoMetricSpace X]

/-- The distance function to a set is continuous (in fact, 1-Lipschitz). -/
theorem continuous_infDist_to_set (A : Set X) :
    Continuous (fun x => Metric.infDist x A) :=
  Metric.continuous_infDist_pt A
