import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← div_mul_div_cancel (m * n) m (ne_of_gt H)]
  rw [mul_comm m k]
  rw [mul_div_cancel_left _ (ne_of_gt H)]

/- ACTUAL PROOF OF Nat.mul_div_mul_left -/

example {m : Nat} (n k : Nat) (H : 0 < m) :
    m * n / (m * k) = n / k := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]