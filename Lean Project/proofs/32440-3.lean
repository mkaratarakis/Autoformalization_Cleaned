import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} : a ≤ c → b ≤ c → max a b ≤ c := by
  intro hac hbc
  by_cases h : a ≤ b
  · apply max_le_of_le_left
    exact hbc
  · apply max_le_of_le_right
    exact hac

/- ACTUAL PROOF OF Nat.max_le_of_le_of_le -/

example {a b c : Nat} : a ≤ c → b ≤ c → max a b ≤ c := by
  intros; cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right h]; assumption
  | inr h => rw [Nat.max_eq_left h]; assumption