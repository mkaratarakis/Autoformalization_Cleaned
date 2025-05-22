import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  rw [map_map]
  apply congr_arg
  ext1 x
  rw [sub_add_cancel]

/- ACTUAL PROOF OF List.map_sub_range' -/

example (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left