import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat



example {a b : Nat} : compare a b = .eq ↔ a = b := by
  rw [compare_def_lt]; (repeat' split) <;> simp [Nat.ne_of_lt, Nat.ne_of_gt, *]
  next hlt hgt => exact Nat.le_antisymm (Nat.not_lt.1 hgt) (Nat.not_lt.1 hlt)