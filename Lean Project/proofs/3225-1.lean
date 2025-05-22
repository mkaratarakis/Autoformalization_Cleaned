import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {m : Nat} (n k : Nat) (H : 0 < m) :
    n * m / (k * m) = n / k := by

  rw [mul_comm n m, mul_comm k m]
  apply Nat.div_cancel_left
  exact H

/- ACTUAL PROOF OF Nat.mul_div_mul_right -/

example {m : Nat} (n k : Nat) (H : 0 < m) :
    n * m / (k * m) = n / k := by
  rw [Nat.mul_comm, Nat.mul_comm k, Nat.mul_div_mul_left _ _ H]