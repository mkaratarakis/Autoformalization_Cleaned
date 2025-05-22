import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) :
    a = b * c := by
  rw [←H2]
  exact (Nat.mul_div_cancel_left _ _).symm

/- ACTUAL PROOF OF Nat.eq_mul_of_div_eq_right -/

example {a b c : Nat} (H1 : b ∣ a) (H2 : a / b = c) :
    a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]