import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}
variable (R : α → α → Prop)
variable {R}

example : zip (l : List α) ([] : List β)  = [] := by
  rw [zip]
  rw [zipWith]
  rfl

/- ACTUAL PROOF OF List.zip_nil_right -/

example : zip (l : List α) ([] : List β)  = [] := by
  simp [zip, zipWith]