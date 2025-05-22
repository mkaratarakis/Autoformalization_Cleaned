import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat



example {a b : Nat} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [compare_def_le]; (repeat' split) <;> simp [*]