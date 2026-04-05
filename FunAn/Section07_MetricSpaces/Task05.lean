/-
  Section 7, Task 5.
  Prove that ρ(x, A) = 0 if and only if x ∈ closure(A).
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

variable {X : Type*} [PseudoMetricSpace X]

/-- ρ(x, A) = 0 iff x ∈ closure(A), for nonempty A. -/
theorem dist_to_set_zero_iff_mem_closure (A : Set X) (hA : A.Nonempty) (x : X) :
    Metric.infDist x A = 0 ↔ x ∈ closure A :=
  (Metric.mem_closure_iff_infDist_zero hA).symm
