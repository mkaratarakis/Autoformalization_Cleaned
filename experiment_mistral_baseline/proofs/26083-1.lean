import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.WithBot

open Nat
open WithBot


example {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n <;> cases m <;> simp [WithBot.add, Nat.cast_zero, Nat.cast_one, Nat.cast_two, Nat.cast_three, Nat.cast_add]
  repeat rw [Nat.cast_id]
  exact
    ⟨fun h => by
      { rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _),
        { exact ⟨rfl, rfl⟩ },
        { exact ⟨rfl, rfl⟩ },
        { exact ⟨rfl, rfl⟩ },
        { exact ⟨rfl, rfl⟩ },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), },
        { exfalso, exact Nat.not_succ_le_zero 2 (Nat.le_of_lt (Nat.lt_of_succ_lt_succ h)), }, },
      fun h => by
      { rcases h with (rfl | rfl | rfl | rfl),
        { rfl, },
        { rfl, },
        { rfl, },
        { rfl, }, }⟩

/- ACTUAL PROOF OF Nat.WithBot.add_eq_three_iff -/

example {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 := by
  cases n
  · simp [WithBot.bot_add]
  cases m
  · simp [WithBot.add_bot]
  simp [← WithBot.coe_add, Nat.add_eq_three_iff]