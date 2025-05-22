import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (l : List α) (m n : Nat) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  rw [take_add]
  simp only [length_take, min_eq_left]
  rw [add_tsub_assoc_of_le]
  apply le_tsub_of_add_le_right
  exact le_self_add

/- ACTUAL PROOF OF List.take_add -/

example (l : List α) (m n : Nat) : l.take (m + n) = l.take m ++ (l.drop m).take n := by
  suffices take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l) by
    rw [take_append_drop] at this
    assumption
  rw [take_append_eq_append_take, take_of_length_le, append_right_inj]
  · simp only [take_eq_take, length_take, length_drop]
    omega
  apply Nat.le_trans (m := m)
  · apply length_take_le
  · apply Nat.le_add_right