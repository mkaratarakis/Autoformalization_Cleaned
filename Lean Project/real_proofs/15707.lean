import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Hyperoperation





example : hyperoperation 2 = (· * ·) := by
  ext m k
  induction' k with bn bih
  · rw [hyperoperation]
    exact (Nat.mul_zero m).symm
  · rw [hyperoperation_recursion, hyperoperation_one, bih]
    -- Porting note: was `ring`
    dsimp only
    nth_rewrite 1 [← mul_one m]
    rw [← mul_add, add_comm]