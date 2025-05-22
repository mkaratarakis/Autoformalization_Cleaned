import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]