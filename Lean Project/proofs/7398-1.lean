import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} (i : Nat) :
    take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ := by
  rw [take_append_of_le]
  . rw [min_eq_right (Nat.le_add_right _ _)]
    rw [add_tsub_cancel_of_le (Nat.le_add_left _ _)]
  . exact Nat.le_add_right _ _

/- ACTUAL PROOF OF List.take_append -/

example {l₁ l₂ : List α} (i : Nat) :
    take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ := by
  rw [take_append_eq_append_take, take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]