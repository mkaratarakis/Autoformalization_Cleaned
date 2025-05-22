import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : 0 < n) : findSome? f (replicate n a) = f a := by
  unfold findSome?
  simp [replicate, List.foldr]
  cases h
  case posit =>
    simp [List.foldr]
    rw [Option.orElse]
    rfl

/- ACTUAL PROOF OF List.findSome?_replicate_of_pos -/

example (h : 0 < n) : findSome? f (replicate n a) = f a := by
  simp [findSome?_replicate, Nat.ne_of_gt h]