import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) (i : Nat) :
    x * (twoPow w i) = x <<< i := by
  have h : (x * twoPow w i).toNat = (x <<< i).toNat := by
    simp [BitVec.toNat, BitVec.val, twoPow, BitVec.shl]
    split
    · intro h₁
      have h₂ : 2 ^ i < 2 ^ w := Nat.pow_lt_pow_of_lt h₁ (Nat.zero_lt_succ _)
      simp [Nat.mod_eq_of_lt h₂]
    · intro h₁
      have h₂ : 2 ^ i ≡ 0 [MOD 2 ^ w] := Nat.ModEq.of_dvd (Nat.dvd_pow_self _ _ h₁)
      simp [h₂, Nat.ModEq.zero_mod_eq_zero]
  exact BitVec.toNat_inj h
  exact BitVec.ext h

/- ACTUAL PROOF OF BitVec.mul_twoPow_eq_shiftLeft -/

example (x : BitVec w) (i : Nat) :
    x * (twoPow w i) = x <<< i := by
  apply eq_of_toNat_eq
  simp only [toNat_mul, toNat_twoPow, toNat_shiftLeft, Nat.shiftLeft_eq]
  by_cases hi : i < w
  · have hpow : 2^i < 2^w := Nat.pow_lt_pow_of_lt (by omega) (by omega)
    rw [Nat.mod_eq_of_lt hpow]
  · have hpow : 2 ^ i % 2 ^ w = 0 := by
      rw [Nat.mod_eq_zero_of_dvd]
      apply Nat.pow_dvd_pow 2 (by omega)
    simp [Nat.mul_mod, hpow]