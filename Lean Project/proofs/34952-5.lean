import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Sublist
open Nat
variable [BEq α]
variable [BEq α]

example (p : α → Bool) {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ := by
  induction s
  case slnil => simp
  case cons s ih =>
    cases l₂
    case nil => simp
    case cons h t =>
      by_cases hp : p h
      case pos =>
        apply Sublist.cons
        constructor
        · exact hp
        · apply ih
          constructor
      case neg =>
        apply ih

/- ACTUAL PROOF OF List.Sublist.filter -/

example (p : α → Bool) {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ := by
  rw [← filterMap_eq_filter]; apply s.filterMap