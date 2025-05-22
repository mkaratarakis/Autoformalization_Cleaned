import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil =>
    simp [nil_append, Nat.zero_add]
  | cons a as ih =>
    simp only [cons_append, ih, length, Nat.add_succ]

/- ACTUAL PROOF OF List.length_append -/

example (as bs : List α) : (as ++ bs).length = as.length + bs.length := by
  induction as with
  | nil => simp
  | cons _ as ih => simp [ih, Nat.succ_add]