import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  have h := p
  unfold testBit at h
  simp only [Ne.def] at h
  have h_shift : (x >> i) % 2 = 1 := by
    simp [h]
  have h_ge : x ≥ 2^i := by
    have h_ge_shift : x >> i ≥ 1 := Nat.mod_lt (x >> i) 2
    apply Nat.le_of_pow_le_pow_of_le
    · exact Nat.le_refl 2
    · exact h_ge_shift
    rw [Nat.mul_div_cancel']
    · simp
    · apply Nat.pos_of_ne_zero
      simp [Nat.mul_div_cancel']

/- ACTUAL PROOF OF Nat.testBit_implies_ge -/

example {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  simp only [testBit_to_div_mod] at p
  apply Decidable.by_contra
  intro not_ge
  have x_lt : x < 2^i := Nat.lt_of_not_le not_ge
  simp [div_eq_of_lt x_lt] at p