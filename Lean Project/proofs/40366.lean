import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example : ([] : List α).drop i = [] := by
  cases i with
  | zero =>
    simp [drop]
  | succ n =>
    simp [drop]

/- ACTUAL PROOF OF List.drop_nil -/

example : ([] : List α).drop i = [] := by
  cases i <;> rfl