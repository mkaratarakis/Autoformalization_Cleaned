import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Hyperoperation





example : hyperoperation 1 = (· + ·) := by
  ext m k
  induction' k with bn bih
  · rw [Nat.add_zero m, hyperoperation]
  · rw [hyperoperation_recursion, bih, hyperoperation_zero]
    exact Nat.add_assoc m bn 1