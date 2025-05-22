import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  induction L with
  | nil => simp
  | hd::tl =>
    simp only [take, get, Fin.cons_val_zero, Fin.cons_val_succ, length_take, length_cons]
    split_ifs with h
    · simp
    · apply get_cons_succ
      simp only [Fin.cons_val_succ]
      apply ih

/- ACTUAL PROOF OF List.get_take' -/

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  simp [getElem_take']