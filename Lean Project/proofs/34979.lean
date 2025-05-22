import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]

example {L : List α} (h : 0 < L.length) : isPrefixOf L [] = false := by
  cases L with
  | nil =>
    -- Case 1: L is the empty list
    exfalso
    apply Nat.not_lt_zero
    assumption
  | cons head tail =>
    -- Case 2: L is a non-empty list
    simp [isPrefixOf]
    rfl

/- ACTUAL PROOF OF List.isPrefixOf_length_pos_nil -/

example {L : List α} (h : 0 < L.length) : isPrefixOf L [] = false := by
  cases L <;> simp_all [isPrefixOf]