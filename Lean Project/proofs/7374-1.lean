import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  rw [get_take]
  exact get_of_lt_length (L.take j) i
example {L : List α} {j i : Nat} : get (L.take j) i = get L i := by
  rw [get_take]
  exact get_of_lt_length (L.take j) i

/- ACTUAL PROOF OF List.get_take' -/

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  simp [getElem_take']