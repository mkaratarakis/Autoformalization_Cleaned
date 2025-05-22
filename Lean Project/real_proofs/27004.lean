import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {n : Nat} {a : α} {b : β} :
    unzip (replicate n (a, b)) = (replicate n a, replicate n b) := by
  ext1 <;> simp