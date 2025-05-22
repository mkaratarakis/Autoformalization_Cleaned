import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  constructor
  · intro h
    cases le_total a b with
    | inl h₁ =>
      apply And.intro
      · exact lt_of_lt_of_le h h₁
      · rw [max_eq_left h₁] at h
        exact lt_of_lt_of_le h h₁
    | inr h₁ =>
      apply And.intro
      · rw [max_eq_right h₁] at h
        exact lt_of_lt_of_le h h₁
      · exact lt_of_lt_of_le h h₁
  · intro h
    cases le_total a b with
    | inl h₁ =>
      rw [max_eq_left h₁]
      exact h.1
    | inr h₁ =>
      rw [max_eq_right h₁]
      exact h.2

/- ACTUAL PROOF OF Nat.max_lt -/

example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.succ_max_succ a b]; exact Nat.max_le