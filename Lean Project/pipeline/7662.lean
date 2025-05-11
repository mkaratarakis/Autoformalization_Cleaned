import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Int.Bitwise
example (n : Nat) : (0 : Int) >>> n = 0 := by
  rw [Int.shiftRight_eq_div_pow]
  simp

/- ACTUAL PROOF OF Int.zero_shiftRight -/

example (n : Nat) : (0 : Int) >>> n = 0 := by
  simp [Int.shiftRight_eq_div_pow]