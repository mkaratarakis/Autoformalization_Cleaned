import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}


example (as : List α) (a : α) : (concat as a).length = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons _ xs ih => simp [concat, ih]