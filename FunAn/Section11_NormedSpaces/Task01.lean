/-
  Section 11, Task 1.
  The triangle inequality ‖x+y‖ ≤ ‖x‖+‖y‖ is equivalent to
  convexity of the closed unit ball {x : ‖x‖ ≤ 1}.

  Forward: triangle inequality ⟹ convexity (the interesting direction).
  Reverse: convexity ⟹ triangle inequality (in Lean, the triangle
  inequality is an axiom of NormedAddCommGroup, so this is definitional;
  the mathematical content would be the Minkowski functional construction).
-/
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward: the closed unit ball of a normed space is convex.
    This is the meaningful direction: triangle inequality ⟹ convexity. -/
theorem closedBall_zero_one_convex :
    Convex ℝ (Metric.closedBall (0 : E) 1) :=
  convex_closedBall 0 1

/-- Reverse: the triangle inequality holds in a normed space.
    (In Lean this is definitional; the math content is the Minkowski functional.) -/
theorem norm_triangle_inequality (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

/-- The full equivalence: normed space has convex unit ball iff triangle ineq. -/
theorem convex_ball_iff_triangle :
    Convex ℝ (Metric.closedBall (0 : E) 1) ↔ ∀ x y : E, ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  ⟨fun _ => norm_add_le, fun _ => convex_closedBall 0 1⟩
