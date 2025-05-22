import Init.Data.Int.Lemmas
import Init.Data.Int.Pow

open Int


example (b : Int) (e : Nat) : b ^ (e+1) = b * (b ^ e) := by
  rw [Int.pow_succ]
  rfl

/- ACTUAL PROOF OF Int.pow_succ' -/

example (b : Int) (e : Nat) : b ^ (e+1) = b * (b ^ e) := by
  rw [Int.mul_comm, Int.pow_succ]