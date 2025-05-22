import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example : find? p (replicate n a) = if n = 0 then none else if p a then some a else none := by
  cases n
  · simp
  · by_cases p a <;> simp_all [replicate_succ]