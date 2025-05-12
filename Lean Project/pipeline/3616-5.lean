import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal
open Cardinal

example : lift.{v} 𝔠 = 𝔠 := by
  rw [continuum]
  simp only [two_power_aleph0]
  rw [lift_id' (𝔠 : Cardinal.{max v u_1})]
  rfl

/- ACTUAL PROOF OF Cardinal.lift_continuum -/

example : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0, lift_two_power, lift_aleph0, two_power_aleph0]