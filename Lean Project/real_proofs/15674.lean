import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Hyperoperation





example (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 := by
  rw [hyperoperation]