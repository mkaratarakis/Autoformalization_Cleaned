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
      _ < k * y := by linarith
  · intro h
    apply Nat.div_lt_iff_lt_mul
    · exact h
    · exact Hk

/- ACTUAL PROOF OF Nat.div_lt_iff_lt_mul -/

example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)