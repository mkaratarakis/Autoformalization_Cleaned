import Init.Data.List.Lemmas
import Init.Data.List.MinMax

open List
open Nat

example [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).max? = some a := by
  cases n with
  | zero =>
    exfalso
    apply Nat.not_lt_zero
  | succ k =>
    rw [replicate_succ]
    rw [max?_cons_of_max (le_max_of_le_right le_rfl) (Nat.succ_ne_zero _)]
    rw [w]
    exact max?_singleton.symm

/- ACTUAL PROOF OF List.maximum?_replicate_of_pos -/

example [Max α] {n : Nat} {a : α} (w : max a a = a) (h : 0 < n) :
    (replicate n a).maximum? = some a := by
  simp [maximum?_replicate, Nat.ne_of_gt h, w]