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
      rw [ih]
      simp [Option.map_orElse]
      rfl

/- ACTUAL PROOF OF List.findIdx?_append -/

example :
    (xs ++ ys : List α).findIdx? p =
      (xs.findIdx? p <|> (ys.findIdx? p).map fun i => i + xs.length) := by
  induction xs with simp
  | cons _ _ _ => split <;> simp_all [Option.map_orElse, Option.map_map]; rfl