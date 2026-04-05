/-
  Section 3, Task 09.
  a) If f is measurable (complex-valued), then |f| is measurable.
  b) A complex function is measurable iff its real and imaginary parts are.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

variable {α : Type*} [MeasurableSpace α]

/-- The norm of a measurable complex function is measurable. -/
theorem measurable_norm_of_complex_measurable {f : α → ℂ} (hf : Measurable f) :
    Measurable (fun x => ‖f x‖) :=
  hf.norm

/-- Re and Im of a measurable complex function are measurable. -/
theorem measurable_re_im_of_complex_measurable {f : α → ℂ} (hf : Measurable f) :
    Measurable (fun x => (f x).re) ∧ Measurable (fun x => (f x).im) :=
  ⟨Complex.continuous_re.measurable.comp hf, Complex.continuous_im.measurable.comp hf⟩
