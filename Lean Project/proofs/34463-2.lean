import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (l : List α) : rotateRight l 0 = l := by
  rw [rotateRight]
  split
  · intro h
    rw [Nat.le_zero] at h
    rw [h]
  · unfold Mod.mod
    simp
    rw [Nat.sub_zero]
    rw [take_all]
    rw [drop_all]
    rw [append_nil]

/- ACTUAL PROOF OF List.rotateRight_zero -/

example (l : List α) : rotateRight l 0 = l := by
  simp [rotateRight]