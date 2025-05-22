import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example {n : Nat} {a : α} (h : p a) :
    (replicate n a).eraseP p = replicate (n - 1) a := by
  cases n with
  | zero =>
    simp [replicate, eraseP]
  | succ n' =>
    simp [replicate, eraseP, h]
    apply congrArg
    simp [replicate, eraseP]

/- ACTUAL PROOF OF List.eraseP_replicate_of_pos -/

example {n : Nat} {a : α} (h : p a) :
    (replicate n a).eraseP p = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ, h]