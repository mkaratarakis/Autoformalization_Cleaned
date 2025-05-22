import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul k (m * n) (Nat.mul_ne_zero H _)]
  rw [Nat.mul_div_cancel_left _ H]

/- ACTUAL PROOF OF Nat.mul_div_mul_left -/

example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]