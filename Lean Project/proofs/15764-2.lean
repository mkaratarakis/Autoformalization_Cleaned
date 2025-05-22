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
  simp only [Bool.decide_eq_true] at h
  rw [← Nat.land_one_iff] at h
  have h_mod : x % 2^i % 2 = 1 := by simp [h]
  have h_div : x / 2^i % 2 = 1 := by
    apply Nat.mod_mod_of_dvd
    · exact h_mod
    · exact Nat.dvd_pow 2 i
  have h_ge : x ≥ 2^i := by
    apply Nat.le_of_dvd
    · exact Nat.dvd_pow 2 i
    · rw [Nat.mul_div_cancel']
      · simp
      · exact Nat.pos_of_ne_zero
        simp [Nat.mul_div_cancel']
  exact h_ge

/- ACTUAL PROOF OF Nat.testBit_implies_ge -/

example {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  simp only [testBit_to_div_mod] at p
  apply Decidable.by_contra
  intro not_ge
  have x_lt : x < 2^i := Nat.lt_of_not_le not_ge
  simp [div_eq_of_lt x_lt] at p