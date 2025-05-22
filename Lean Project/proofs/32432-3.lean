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
    · apply lt_of_lt_of_le h
      apply le_max_left
    · apply lt_of_lt_of_le h
      apply le_max_right
  · intro h
    apply lt_of_le_of_lt
    · apply max_le
      assumption
      assumption
    · cases h
      assumption

/- ACTUAL PROOF OF Nat.max_lt -/

example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.succ_max_succ a b]; exact Nat.max_le