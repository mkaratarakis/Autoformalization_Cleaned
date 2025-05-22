import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example {l₁ l₂ : List α} {n : Nat} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, Nat.sub_eq_zero_of_le h]