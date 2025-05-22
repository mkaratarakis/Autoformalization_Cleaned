import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  constructor
  · intro h
    calc
      x = k * (x / k) + x % k := (Nat.div_add_mod x k).symm
      _ ≤ k * (x / k) + (k - 1) := by simp [Nat.mod_lt x Hk]
      _ < k * (x / k) + k := by linarith
      _ = k * (x / k + 1) := by rfl
      _ ≤ k * y := Nat.mul_le_mul_left k (Nat.succ_le_of_lt h)
      _ < k * y + 1 := by linarith
      _ ≤ y * k := by
        apply Nat.le_mul_of_pos_right
        exact Nat.pos_of_ne_zero (Ne.symm (Nat.ne_of_lt Hk))
    exact lt_of_le_of_lt this (Nat.mul_lt_mul_of_pos_left y (Nat.pos_of_ne_zero (Ne.symm (Nat.ne_of_lt Hk))))
  · intro h
    apply Nat.div_lt_iff_lt_mul
    · exact h
    · exact Hk

/- ACTUAL PROOF OF Nat.div_lt_iff_lt_mul -/

example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)