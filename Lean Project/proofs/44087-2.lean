import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {i j : BitVec n} : i.toInt = j.toInt → i = j := by
  intro eq
  dsimp [toInt] at eq
  apply toNat_injective

  match n with
  | 0 => simp
  | _ + 1 =>
    cases h: toNat i < 2^n
    · cases h': toNat j < 2^n
      · simp [h, h'] at eq
        assumption
      · simp [h, h'] at eq
        linarith
    · cases h': toNat j < 2^n
      · simp [h, h'] at eq
        linarith
      · simp [h, h'] at eq
        linarith

    exact Nat.lt_pow_succ n 2

/- ACTUAL PROOF OF BitVec.eq_of_toInt_eq -/

example {i j : BitVec n} : i.toInt = j.toInt → i = j := by
  intro eq
  simp [toInt_eq_toNat_cond] at eq
  apply eq_of_toNat_eq
  revert eq
  have _ilt := i.isLt
  have _jlt := j.isLt
  split <;> split <;> omega