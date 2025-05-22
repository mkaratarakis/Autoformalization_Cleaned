import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) : rotateRight l 0 = l := by
  rw [rotateRight]
  rw [take]
  rw [drop]
  rw [append]
  exact l

/- ACTUAL PROOF OF List.rotateRight_zero -/

example (l : List α) : rotateRight l 0 = l := by
  simp [rotateRight]