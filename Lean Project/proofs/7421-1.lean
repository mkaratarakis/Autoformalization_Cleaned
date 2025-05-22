import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} (i : Nat) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  have h₁ : drop (l₁.length + i) (l₁ ++ l₂) = drop (l₁.length + i) l₁ ++ drop (l₁.length + i - l₁.length) l₂ := by
    rw [drop_append]
  have h₂ : drop (l₁.length + i) l₁ = [] := by
    apply drop_ge_length
  rw [h₁, h₂, Nat.add_sub_cancel_left, nil_append]

/- ACTUAL PROOF OF List.drop_append -/

example {l₁ l₂ : List α} (i : Nat) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  rw [drop_append_eq_append_drop, drop_eq_nil_of_le] <;>
    simp [Nat.add_sub_cancel_left, Nat.le_add_right]