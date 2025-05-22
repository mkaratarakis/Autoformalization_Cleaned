import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : p a) : find? p (replicate n a) = if n = 0 then none else some a := by
  by_cases n = 0
  · simp [find?, replicate, h]
    rfl
  · simp [find?, replicate, h]
    rfl

/- ACTUAL PROOF OF List.find?_replicate_of_pos -/

example (h : p a) : find? p (replicate n a) = if n = 0 then none else some a := by
  simp [find?_replicate, h]