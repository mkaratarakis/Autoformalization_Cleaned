import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  cases n with
  | zero =>
    rfl
  | succ k =>
    simp [replicate, erase]

/- ACTUAL PROOF OF List.erase_replicate_self -/

example [LawfulBEq α] {a : α} :
    (replicate n a).erase a = replicate (n - 1) a := by
  cases n <;> simp [replicate_succ]