import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with
  | nil =>
    simp
  | cons head tail ih =>
    by_cases hp : p head
    · simp [hp]
    · simp [hp]
      have h1 : ∀ i, i + 1 + tail.length = i + (tail.length + 1) := by intro i; rfl
      rw [ih]
      simp
      congr
      funext i
      exact h1 i

/- ACTUAL PROOF OF List.findIdx?_append -/

example :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with simp
  | cons _ _ _ => split <;> simp_all [Option.map_orElse, Option.map_map]; rfl