import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    cases n <;> cases m <;> try {simp only [WithBot.coe_eq_coe, WithBot.coe_add, Nat.add_eq_zero_iff] at h}
    · exfalso
      exact bot_ne_zero h
    · exfalso
      exact bot_ne_zero h
    · simp at h
      exact h
    · simp at h
      exact h
    · simp at h
      exact h
  · rintro ⟨rfl, rfl⟩
    rfl

/- ACTUAL PROOF OF Nat.WithBot.add_eq_zero_iff -/

example {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, add_eq_zero_iff_of_nonneg]