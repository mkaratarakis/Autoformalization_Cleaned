import Init.Data.UInt.Basic
import Init.Data.Char.Basic

open Char



example (n : Nat) (h : isValidCharNat n) : n < UInt32.size := by
  match h with
  | Or.inl h        =>
    apply Nat.lt_trans h
    decide
  | Or.inr ⟨_,  h₂⟩ =>
    apply Nat.lt_trans h₂
    decide