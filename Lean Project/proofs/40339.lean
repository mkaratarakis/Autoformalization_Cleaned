import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  rw [append_cons, append_assoc]
  rfl

/- ACTUAL PROOF OF List.append_cons -/

example (as : List α) (b : α) (bs : List α) : as ++ b :: bs = as ++ [b] ++ bs := by
  simp