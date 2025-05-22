import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (L : List α) {i j : Nat} (h : i + j < L.length) : j < (L.drop i).length := by
  have A : i < L.length := Nat.lt_of_le_of_lt (Nat.le.intro rfl) h
  rw [(take_append_drop i L).symm] at h
  simpa only [Nat.le_of_lt A, Nat.min_eq_left, Nat.add_lt_add_iff_left, length_take,
    length_append] using h