import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example [BEq α] : isPrefixOf ([] : List α) l = true := by
  unfold isPrefixOf
  simp

/- ACTUAL PROOF OF List.isPrefixOf_nil_left -/

example [BEq α] : isPrefixOf ([] : List α) l = true := by
  simp [isPrefixOf]