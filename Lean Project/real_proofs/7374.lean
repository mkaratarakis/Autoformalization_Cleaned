import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  simp [getElem_take']