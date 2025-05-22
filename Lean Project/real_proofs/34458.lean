import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (l : List α) : rotateLeft l 0 = l := by
  simp [rotateLeft]