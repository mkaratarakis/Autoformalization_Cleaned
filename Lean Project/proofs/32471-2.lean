import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  apply Iff.intro
  · intro h
    rw [h]
    exact dvd_iff_mod_eq_zero.mp H'
  · intro h
    rw [h]
    rw [Nat.mul_div_cancel_left _ _ H]
    apply Nat.div_eq_of_eq_mul
    exact dvd_iff_mod_eq_zero.mp H'

/- ACTUAL PROOF OF Nat.div_eq_iff_eq_mul_left -/

example {a b c : Nat} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  rw [Nat.mul_comm]; exact Nat.div_eq_iff_eq_mul_right H H'