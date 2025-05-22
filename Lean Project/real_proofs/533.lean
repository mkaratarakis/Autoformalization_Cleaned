import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example (l : List α) : eraseIdx l 0 = tail l := by
  cases l <;> rfl