import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · exact bot_le
  cases m
  · exfalso
    apply not_lt_bot _ h
  · exact WithBot.coe_le_coe.2 (Nat.add_one_le_of_lt (WithBot.coe_lt_coe.1 h))

/- ACTUAL PROOF OF Nat.WithBot.add_one_le_of_lt -/

example {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m := by
  cases n
  · simp only [WithBot.bot_add, bot_le]
  cases m
  · exact (not_lt_bot h).elim
  · rwa [WithBot.coe_lt_coe, ← Nat.add_one_le_iff, ← WithBot.coe_le_coe, WithBot.coe_add,
      WithBot.coe_one] at h