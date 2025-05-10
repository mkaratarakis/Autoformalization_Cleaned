import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Hyperoperation





example (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  rw [hyperoperation]