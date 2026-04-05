/-
  Section 15, Task 3.
  The differentiation operator d/dt : C¹[0,1] → C[0,1] has a right inverse
  (integration) but no left inverse (not injective: constants map to 0).

  We formalize the abstract principle: a non-injective function has no
  left inverse, while a surjective function has a right inverse.
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-- A non-injective function has no left inverse.
    (Applied to d/dt: constant functions map to 0, so d/dt is not injective.) -/
theorem differentiation_no_left_inverse
    {α β : Type*} {f : α → β} (hf : ¬Function.Injective f) :
    ¬Function.HasLeftInverse f :=
  fun ⟨_, hg⟩ => hf hg.injective

/-- A surjective function has a right inverse (requires choice).
    (Applied to d/dt: the fundamental theorem of calculus gives
    a right inverse via integration.) -/
theorem differentiation_has_right_inverse
    {α β : Type*} {f : α → β} (hf : Function.Surjective f) :
    Function.HasRightInverse f :=
  hf.hasRightInverse
