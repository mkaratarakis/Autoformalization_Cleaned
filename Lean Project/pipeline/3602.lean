import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal
open Cardinal

example {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum.{v, u}, lift_lt]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/- ACTUAL PROOF OF Cardinal.continuum_lt_lift -/

example {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum.{v, u}, lift_lt]