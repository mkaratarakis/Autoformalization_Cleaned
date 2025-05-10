import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Hyperoperation





example (n : ℕ) : ∀ k : ℕ, hyperoperation (n + 3) 1 k = 1 := by
  induction' n with nn nih
  · intro k
    rw [hyperoperation_three]
    dsimp
    rw [one_pow]
  · intro k
    cases k
    · rw [hyperoperation_ge_three_eq_one]
    · rw [hyperoperation_recursion, nih]