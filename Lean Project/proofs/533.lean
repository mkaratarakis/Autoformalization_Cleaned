import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example (l : List α) : eraseIdx l 0 = tail l := by
 cases l with
 | nil =>
   rfl
 | cons head tail =>
   rfl

/- ACTUAL PROOF OF List.eraseIdx_zero -/

example (l : List α) : eraseIdx l 0 = tail l := by
  cases l <;> rfl