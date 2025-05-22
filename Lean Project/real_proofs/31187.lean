import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by
  simp