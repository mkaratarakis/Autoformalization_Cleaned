import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example [BEq α] : isSuffixOf ([] : List α) l = true := by
  unfold isSuffixOf
  simp
  apply exists.intro
  exact l
  simp

/- ACTUAL PROOF OF List.isSuffixOf_nil_left -/

example [BEq α] : isSuffixOf ([] : List α) l = true := by
  simp [isSuffixOf]