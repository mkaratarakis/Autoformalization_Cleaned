import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example {n : Nat} {a : α} (h : ¬p a) :
    (replicate n a).eraseP p = replicate n a := by
  unfold eraseP
  simp [replicate]
  induction n with
  | zero => simp
  | succ n ih =>
    simp [replicate, eraseP]
    apply ih

/- ACTUAL PROOF OF List.eraseP_replicate_of_neg -/

example {n : Nat} {a : α} (h : ¬p a) :
    (replicate n a).eraseP p = replicate n a := by
  rw [eraseP_of_forall_not (by simp_all)]