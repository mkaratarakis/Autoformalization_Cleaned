import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) : rotateRight l 0 = l := by
  rw [rotateRight]
  split
  · intro h
    exact h
  · simp [Mod.mod, Nat.sub_zero, take_all, drop_all, append_nil]

/- ACTUAL PROOF OF List.rotateRight_zero -/

example (l : List α) : rotateRight l 0 = l := by
  simp [rotateRight]