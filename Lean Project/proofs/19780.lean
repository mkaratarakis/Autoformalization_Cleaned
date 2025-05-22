import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example (a b : Nat) :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by

rw [compare_def_lt]

split

· next hlt => simp [Nat.le_of_lt hlt, Nat.not_le.2 hlt]

· next hge =>

split

· next hgt => simp [Nat.le_of_lt hgt, Nat.not_le.2 hgt]

· next hle => simp [Nat.not_lt.1 hge, Nat.not_lt.1 hle]

/- ACTUAL PROOF OF Nat.compare_def_le -/

example (a b : Nat) :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by
  rw [compare_def_lt]
  split
  · next hlt => simp [Nat.le_of_lt hlt, Nat.not_le.2 hlt]
  · next hge =>
    split
    · next hgt => simp [Nat.le_of_lt hgt, Nat.not_le.2 hgt]
    · next hle => simp [Nat.not_lt.1 hge, Nat.not_lt.1 hle]