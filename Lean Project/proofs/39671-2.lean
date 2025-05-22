import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (_ : (f a).isSome) : findSome? f (replicate n a) = if n = 0 then none else f a := by
  by_cases h : n = 0
  · simp [h]
  · have hn : n > 0 := Nat.pos_of_ne_zero h
    simp [hn]

/- ACTUAL PROOF OF List.find?_replicate_of_isSome -/

example (_ : (f a).isSome) : findSome? f (replicate n a) = if n = 0 then none else f a := by
  simp [findSome?_replicate]