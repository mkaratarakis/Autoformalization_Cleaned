import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example {b : α} {bs : List α} (as : List α) : b ∈ bs → b ∈ as ++ bs := by
  intro h
  induction as with
  | nil =>
    simp
    exact h
  | cons head tail ih =>
    simp
    right
    apply Or.inr
    exact h

/- ACTUAL PROOF OF List.mem_append_of_mem_right -/

example {b : α} {bs : List α} (as : List α) : b ∈ bs → b ∈ as ++ bs := by
  intro h
  induction as with
  | nil  => simp [h]
  | cons => apply Mem.tail; assumption