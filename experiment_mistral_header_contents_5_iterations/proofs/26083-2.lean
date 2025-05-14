import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n <;> cases m <;> simp [WithBot.bot_add, WithBot.add_bot, WithBot.coe_add, Nat.add_eq_three_iff]
  · exact iff_of_false (by simp) (by simp)
  · exact iff_of_false (by simp) (by simp)
  · exact iff_of_false (by simp) (by simp)
  · exact Nat.add_eq_three_iff

/- ACTUAL PROOF OF Nat.WithBot.add_eq_three_iff -/

example {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]