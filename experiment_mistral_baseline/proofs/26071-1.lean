import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n <;> cases m <;> simp
  · exact bot_le
  · exact (not_lt.2 h).elim
  · intro a b
    rw [some_lt_some, add_one_le_iff] at h
    exact some_le_some.2 h

/- ACTUAL PROOF OF Nat.WithBot.add_one_le_of_lt -/

example {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h