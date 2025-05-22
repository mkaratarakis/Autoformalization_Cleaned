import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) : rotateRight l 0 = l := by
  rw [rotateRight]
  split
  · intro h
    rfl
  · simp [Mod.mod, Nat.sub_zero]
    rw [take_right, drop_right]
    rw [append_nil]
    rfl

/- ACTUAL PROOF OF List.rotateRight_zero -/

example (l : List α) : rotateRight l 0 = l := by
  simp [rotateRight]