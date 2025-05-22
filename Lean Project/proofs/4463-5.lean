import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example [Min α] {n : Nat} {a : α} (w : min a a = a) (h : 0 < n) :
    (replicate n a).min? = some a := by
  rw [replicate.eq_def]
  cases n with
  | zero =>
    exfalso
    exact Nat.not_lt_zero 0 h
  | succ n =>
    rw [min?_cons]
    rw [min_eq_left w]
    rw [min?_replicate (Nat.succ_ne_zero n) w]
    exact some a

/- ACTUAL PROOF OF List.minimum?_replicate_of_pos -/

example [Min α] {n : Nat} {a : α} (w : min a a = a) (h : 0 < n) :
    (replicate n a).minimum? = some a := by
  simp [minimum?_replicate, Nat.ne_of_gt h, w]