import Init.Classical
import Init.Data.Ord
import Init.Data.Nat.Compare

open Nat


example (a b : Nat) :
    compare a b = if a < b then .lt else if b < a then .gt else .eq := by
  by_cases h : a < b
  · exact if_pos h
  rw [if_neg h]
  by_cases h' : a = b
  · rw [h']
    exact if_pos rfl
  · rw [if_neg h']
    exact if_neg h'

/- ACTUAL PROOF OF Nat.compare_def_lt -/

example (a b : Nat) :
    compare a b = if a < b then .lt else if b < a then .gt else .eq := by
  simp only [compare, compareOfLessAndEq]
  split
  · rfl
  · next h =>
    match Nat.lt_or_eq_of_le (Nat.not_lt.1 h) with
    | .inl h => simp [h, Nat.ne_of_gt h]
    | .inr rfl => simp