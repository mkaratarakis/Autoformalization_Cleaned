import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc



example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  rw [@Eq.comm _ (a + b) _, add_eq_add_le c a h, @Eq.comm _ _ c]