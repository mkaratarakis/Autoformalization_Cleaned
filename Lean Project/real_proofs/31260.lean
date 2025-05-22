import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hne : b - a ≠ 0 := Nat.sub_ne_zero_of_lt h
    have : a ≤ b := Nat.le_of_succ_le h
    rw [sub_succ, Nat.succ_add, ← Nat.add_succ, Nat.succ_pred hne, ih this]