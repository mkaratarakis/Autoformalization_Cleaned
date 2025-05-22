import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example (as : List α) : as ++ [] = as := by
  induction as <;> simp [List.append, ih]

/- ACTUAL PROOF OF List.append_nil -/

example (as : List α) : as ++ [] = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp_all only [HAppend.hAppend, Append.append, List.append]