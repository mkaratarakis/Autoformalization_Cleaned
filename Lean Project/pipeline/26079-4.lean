import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    cases n
    · simp at h
    · cases m
      · simp at h
      · simp
        exact Nat.add_eq_zero_iff.1 h
  · rintro ⟨rfl, rfl⟩
    simp

/- ACTUAL PROOF OF Nat.WithBot.add_eq_zero_iff -/

example {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, add_eq_zero_iff_of_nonneg]