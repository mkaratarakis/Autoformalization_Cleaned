import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {a : α} {b : β} {n : Nat} :
    zip (replicate n a) (replicate n b) = replicate n (a, b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]