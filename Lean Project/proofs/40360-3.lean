import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}
variable (R : α → α → Prop)
variable {R}

example [BEq α] (a b : α) (l : List α) :
    (b :: l).erase a = if b == a then l else b :: l.erase a := by
  unfold erase
  cases h : Decidable (b == a)
  . rw [dif_pos h]
    rfl
  . rw [dif_neg h]
    rfl

/- ACTUAL PROOF OF List.erase_cons -/

example [BEq α] (a b : α) (l : List α) :
    (b :: l).erase a = if b == a then l else b :: l.erase a := by
  simp only [List.erase]; split <;> simp_all