import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {a : α} {b : β} {m n : Nat} :
    zip (replicate m a) (replicate n b) = replicate (min m n) (a, b) := by
  rw [zip_eq_zip_take_min]
  simp