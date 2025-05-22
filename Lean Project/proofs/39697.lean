import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example : find? p (replicate n a) = if n = 0 then none else if p a then some a else none := by
  cases n with
  | zero =>
    simp [replicate, find?]
  | succ n' =>
    by_cases h : p a
    · simp [replicate, find?, h]
    · simp [replicate, find?, h]

/- ACTUAL PROOF OF List.find?_replicate -/

example : find? p (replicate n a) = if n = 0 then none else if p a then some a else none := by
  cases n
  · simp
  · by_cases p a <;> simp_all [replicate_succ]