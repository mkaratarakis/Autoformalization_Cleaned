import Init.Data.Nat.Linear
import Init.Data.Nat.Power2

open Nat



example (h : isPowerOfTwo n) : n > 0 := by
  have ⟨k, h⟩ := h
  rw [h]
  apply Nat.pos_pow_of_pos
  decide