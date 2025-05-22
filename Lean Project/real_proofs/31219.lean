import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (h : b < a) : a ≠ 0 := by
  cases a
  exact absurd h (Nat.not_lt_zero _)
  apply Nat.noConfusion