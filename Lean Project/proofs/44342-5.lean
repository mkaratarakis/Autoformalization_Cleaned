import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : a = natAbs a := by
  cases h' : a
  · simp [natAbs]
  · exfalso
    exact not_le_of_gt h h'

/- ACTUAL PROOF OF Int.eq_natAbs_of_zero_le -/

example {a : Int} (h : 0 ≤ a) : a = natAbs a := by
  let ⟨n, e⟩ := eq_ofNat_of_zero_le h
  rw [e]; rfl