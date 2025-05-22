import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  constructor
  · intro h
    have h1 : x < k * (x / k + 1) := Nat.div_add_one_le x k
    have h2 : k * (x / k + 1) ≤ y * k := Nat.mul_le_mul_left k (Nat.succ_le_of_lt h)
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2)
  · intro h
    have h1 : x < y * k := h
    have h2 : x / k < y := Nat.div_lt_of_lt_mul h Hk
    exact h2

/- ACTUAL PROOF OF Nat.div_lt_iff_lt_mul -/

example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)