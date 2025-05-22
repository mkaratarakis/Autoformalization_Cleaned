import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Sublist
open Nat
variable [BEq α]
variable [BEq α]

example (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | slnil => exact Sublist.slnil
  | cons a l₁ l₂ s ih =>
    simp only [map]
    exact Sublist.cons (f a) (ih : _ <+ _)
  | cons₂ a b l₁ l₂ s ih =>
    simp only [map]
    exact Sublist.cons₂ (f a) (f b) (ih : _ <+ _)

/- ACTUAL PROOF OF List.Sublist.map -/

example (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | slnil => simp
  | cons a s ih =>
    simpa using cons (f a) ih
  | cons₂ a s ih =>
    simpa using cons₂ (f a) ih