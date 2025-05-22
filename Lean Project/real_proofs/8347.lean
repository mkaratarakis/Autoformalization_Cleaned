import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc



example {a : Nat} (b : Nat) {c : Nat} (h : c ≤ a) : (a = b + c) = (b = a - c) := by
  rw [@Eq.comm Nat a (b + c)]
  exact add_eq_le b h