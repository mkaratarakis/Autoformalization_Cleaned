import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}


example (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]