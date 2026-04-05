/-
  Section 7, Task 7.
  Prove that M = {x : ρ(x, A) < ε} is open and N = {x : ρ(x, A) ≤ ε} is closed.
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

variable {X : Type*} [PseudoMetricSpace X]

/-- {x : ρ(x, A) < ε} is open. -/
theorem isOpen_infDist_lt (A : Set X) (ε : ℝ) :
    IsOpen {x | Metric.infDist x A < ε} :=
  isOpen_lt (Metric.continuous_infDist_pt A) continuous_const

/-- {x : ρ(x, A) ≤ ε} is closed. -/
theorem isClosed_infDist_le (A : Set X) (ε : ℝ) :
    IsClosed {x | Metric.infDist x A ≤ ε} :=
  isClosed_le (Metric.continuous_infDist_pt A) continuous_const
