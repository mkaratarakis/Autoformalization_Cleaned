import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example {l : List α} {k : Nat} (h : length l ≤ k) : eraseIdx l k = l := by
  rw [eraseIdx_eq_self]
  exact h

/- ACTUAL PROOF OF List.eraseIdx_of_length_le -/

example {l : List α} {k : Nat} (h : length l ≤ k) : eraseIdx l k = l := by
  rw [eraseIdx_eq_self.2 h]