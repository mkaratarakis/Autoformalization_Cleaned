import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}


example (as : List α) (a : α) : as.concat a = as ++ [a] := by
  induction as <;> simp [concat, *]