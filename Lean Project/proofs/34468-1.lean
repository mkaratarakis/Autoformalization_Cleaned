import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} {a : α} :
    (l.drop n).set m a = (l.set (n + m) a).drop n := by
  rw [drop_set]
  split
  · intro h
    exact False.elim (Nat.not_lt_of_ge (Nat.le_add_right n m) h)
  · rw [tsub_add_cancel_of_le (Nat.le_add_right n m)]

/- ACTUAL PROOF OF List.set_drop -/

example {l : List α} {n m : Nat} {a : α} :
    (l.drop n).set m a = (l.set (n + m) a).drop n := by
  rw [drop_set, if_neg, add_sub_self_left n m]
  exact (Nat.not_lt).2 (le_add_right n m)