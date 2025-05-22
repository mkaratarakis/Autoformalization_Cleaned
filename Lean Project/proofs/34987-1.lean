import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Sublist
open Nat
variable [BEq α]
variable [BEq α]

example (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | base => exact Sublist.base
  | head r s ih =>
    simp only [map]
    exact Sublist.head (map f r) (ih (s : _ <+ _))
  | tail s ih =>
    simp only [map]
    exact Sublist.tail ih
  | cons a l₁ l₂ l₃ s ih =>
    simp only [map]
    exact Sublist.cons (f a) (map f l₁) (map f l₂) ih

/- ACTUAL PROOF OF List.Sublist.map -/

example (f : α → β) {l₁ l₂} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ := by
  induction s with
  | slnil => simp
  | cons a s ih =>
    simpa using cons (f a) ih
  | cons₂ a s ih =>
    simpa using cons₂ (f a) ih