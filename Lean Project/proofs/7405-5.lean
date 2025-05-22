import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {n : Nat} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take (n - 1) := by
  have h1 : (l.take n).length = n := by
    rw [length_take]
    apply min_eq_left
    exact h
  have h2 : (l.take n).take (n - 1) = l.take (n - 1) := by
    rw [take_take]
    simp
    apply min_eq_left
    exact Nat.sub_lt h zero_lt_succ
  rw [dropLast_eq_take]
  simp [h1]
  exact h2

/- ACTUAL PROOF OF List.dropLast_take -/

example {n : Nat} {l : List α} (h : n < l.length) :
    (l.take n).dropLast = l.take (n - 1) := by
  simp only [dropLast_eq_take, length_take, Nat.le_of_lt h, Nat.min_eq_left, take_take, sub_le]