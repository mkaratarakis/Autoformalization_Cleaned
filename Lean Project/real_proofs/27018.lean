import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWithAll]
  split <;> simp_all