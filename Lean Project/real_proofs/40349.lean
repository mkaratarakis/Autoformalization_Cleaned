import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}


example [BEq α] : isSuffixOf ([] : List α) l = true := by
  simp [isSuffixOf]