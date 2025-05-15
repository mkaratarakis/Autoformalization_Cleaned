import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal
open Cardinal

example : lift.{v} 𝔠 = 𝔠 := by
  rw [continuum]
  rw [Cardinal.lift_power]
  rw [Cardinal.lift_aleph0]
  rfl

/- ACTUAL PROOF OF Cardinal.lift_continuum -/

example : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0, lift_two_power, lift_aleph0, two_power_aleph0]