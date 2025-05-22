import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example (a b l) : @getLastD α (b::l) a = getLastD l b := by
  cases l <;> simp [getLastD]

/- ACTUAL PROOF OF List.getLastD_cons -/

example (a b l) : @getLastD α (b::l) a = getLastD l b := by
  cases l <;> rfl