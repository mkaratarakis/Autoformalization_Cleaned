import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by
  rw [isPrefixOf_cons₂]
  rw [and_eq_true_eq]
  rw [LawfulBEq.eq_iff]

/- ACTUAL PROOF OF List.isPrefixOf_cons₂_self -/

example [LawfulBEq α] {a : α} :
    isPrefixOf (a::as) (a::bs) = isPrefixOf as bs := by
  simp [isPrefixOf_cons₂]