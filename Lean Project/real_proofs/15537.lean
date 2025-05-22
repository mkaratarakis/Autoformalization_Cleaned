import Init.Omega
import Init.Data.Nat.Mod

open Nat



example {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases a <;> simp_all