import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat
open sub



example {motive : Nat → Prop}
    (x y : Nat)
    (h₁ : y ≤ x → (k : Nat) → x = y + k → motive k)
    (h₂ : x < y → motive 0)
    : motive (x - y) := by
  cases Nat.lt_or_ge x y with
  | inl hlt => rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]; exact h₂ hlt
  | inr hle => exact h₁ hle (x - y) (Nat.add_sub_of_le hle).symm