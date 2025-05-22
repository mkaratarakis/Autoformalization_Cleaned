import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  constructor
  · intro h
    have h1 : x < k * (x / k + 1) := Nat.div_mul_le_self x k
    have h2 : x / k + 1 ≤ y := Nat.succ_le_of_lt h
    have h3 : k * (x / k + 1) ≤ k * y := Nat.mul_le_mul_left k h2
    exact lt_of_lt_of_le h1 (le_trans h3)
  · intro h
    have h1 : k * (x / k) ≤ x := Nat.div_mul_le_self x k
    have h2 : k * (x / k) < k * y := lt_of_lt_of_le h h1
    exact Nat.div_lt_iff_lt_mul Hk

/- ACTUAL PROOF OF Nat.div_lt_iff_lt_mul -/

example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)