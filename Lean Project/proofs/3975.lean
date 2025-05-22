import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  -- Convert the assumption using the theorem dvd_iff_mod_eq_zero
  have h' : b % a ≠ 0 := by
    intro h''
    apply h
    rwa [dvd_iff_mod_eq_zero]

  -- Use the theorem pos_iff_ne_zero to conclude 0 < b % a
  exact Nat.pos_of_ne_zero h'

/- ACTUAL PROOF OF Nat.emod_pos_of_not_dvd -/

example {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h