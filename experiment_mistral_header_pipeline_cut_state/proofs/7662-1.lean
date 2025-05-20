import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Int.Bitwise
import Init.Data.Int.Bitwise.Lemmas

open Int


example (n : Nat) : (0 : Int) >>> n = 0 := by
  rw [shiftr_eq_div_pow]
  simp [Int.ofNat_eq_coe, Nat.zero_div]

/- ACTUAL PROOF OF Int.zero_shiftRight -/

example (n : Nat) : (0 : Int) >>> n = 0 := by
  simp [Int.shiftRight_eq_div_pow]