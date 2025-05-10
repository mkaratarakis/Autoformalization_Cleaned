import Init.ByCases
import Init.Data.Nat.MinMax

open Nat



example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]