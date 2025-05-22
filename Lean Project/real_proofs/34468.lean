import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} {n m : Nat} {a : α} :
    (l.drop n).set m a = (l.set (n + m) a).drop n := by
  rw [drop_set, if_neg, add_sub_self_left n m]
  exact (Nat.not_lt).2 (le_add_right n m)