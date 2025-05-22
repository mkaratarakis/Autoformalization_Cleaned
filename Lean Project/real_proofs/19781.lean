import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat



example {a b : Nat} : compare a b ≠ .lt ↔ b ≤ a := by
  rw [compare_def_le]; (repeat' split) <;> simp [Nat.le_of_not_le, *]