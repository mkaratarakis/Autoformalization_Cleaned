import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example {l : List α} {k : Nat} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  induction l generalizing k with
  | nil => simp_all
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k => simp_all [eraseIdx_cons_succ, Nat.succ_lt_succ_iff]