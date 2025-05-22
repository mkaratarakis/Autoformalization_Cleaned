import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat



example {a b : Nat} : compare a b = .gt ↔ b < a := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.le_of_lt, *]