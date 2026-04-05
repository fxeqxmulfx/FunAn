/-
  Section 7, Task 4.
  Prove the quadrilateral inequality:
    |ρ(x, z) - ρ(y, t)| ≤ ρ(x, y) + ρ(z, t)
  for any four points x, y, z, t of a metric space.
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

variable {X : Type*} [MetricSpace X]

/-- The quadrilateral inequality in a metric space. -/
theorem quadrilateral_inequality (x y z t : X) :
    |dist x z - dist y t| ≤ dist x y + dist z t := by
  have h1 : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  have h2 : dist y z ≤ dist y t + dist t z := dist_triangle y t z
  have h3 : dist y t ≤ dist y x + dist x t := dist_triangle y x t
  have h4 : dist x t ≤ dist x z + dist z t := dist_triangle x z t
  rw [abs_le]
  constructor
  · linarith [dist_comm z t, dist_comm y x]
  · linarith [dist_comm y z, dist_comm t z]
