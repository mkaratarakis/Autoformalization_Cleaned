import Init.Data.Nat.Linear
import Init.Data.Nat.Log2

open Nat



example (n : Nat) : Nat.log2 n ≤ n := by
  unfold Nat.log2; split
  · next h =>
    have := log2_le_self (n / 2)
    exact Nat.lt_of_le_of_lt this (Nat.div_lt_self (Nat.le_of_lt h) (by decide))
  · apply Nat.zero_le
decreasing_by exact Nat.log2_terminates _ ‹_›