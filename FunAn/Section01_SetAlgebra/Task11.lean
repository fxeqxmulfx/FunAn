/-
  Section 1, Task 11.
  The intervals [a,b), [a,b], (a,b] all belong to the Borel σ-algebra on ℝ.
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

theorem Ico_measurableSet (a b : ℝ) : MeasurableSet (Set.Ico a b) :=
  measurableSet_Ico

theorem Icc_measurableSet (a b : ℝ) : MeasurableSet (Set.Icc a b) :=
  measurableSet_Icc

theorem Ioc_measurableSet (a b : ℝ) : MeasurableSet (Set.Ioc a b) :=
  measurableSet_Ioc
