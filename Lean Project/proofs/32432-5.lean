import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  constructor
  · intro h
    apply And.intro
    · apply Nat.lt_of_le_of_lt
      · apply Nat.le_max_left
      · exact h
    · apply Nat.lt_of_le_of_lt
      · apply Nat.le_max_right
      · exact h
  · intro h
    apply Nat.lt_of_lt_of_le
    · apply Nat.max_lt
      · exact h.left
      · exact h.right
    · exact Nat.le_refl c

/- ACTUAL PROOF OF Nat.max_lt -/

example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.succ_max_succ a b]; exact Nat.max_le