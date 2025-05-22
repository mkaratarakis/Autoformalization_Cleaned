import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul k (m * n) (Nat.pos_of_ne_zero (Nat.ne_of_gt H))]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.ne_of_gt H))]

/- ACTUAL PROOF OF Nat.mul_div_mul_left -/

example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]