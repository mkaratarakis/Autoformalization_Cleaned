import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example : -1#w = allOnes w := by
  have h1 : 1 < 2^w := by
    apply Nat.one_lt_pow
    apply Nat.pos_of_ne_zero
    intro h
    apply h
    simp
  have h2 : 2^w - 1 < 2^w := by
    simp
    apply Nat.sub_lt
    apply Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.zero_lt_succ _)
  rw [ofInt_neg, ofInt_one, ← ofInt_inj (Nat.lt_of_le_of_lt (Nat.zero_le _) h1),
    ← ofInt_inj (Nat.lt_of_le_of_lt (Nat.zero_le _) h2), allOnes_toNat,
    Nat.mod_eq_of_lt h2]

/- ACTUAL PROOF OF BitVec.negOne_eq_allOnes -/

example : -1#w = allOnes w := by
  apply eq_of_toNat_eq
  if g : w = 0 then
    simp [g]
  else
    have q : 1 < 2^w := by simp [g]
    have r : (2^w - 1) < 2^w := by omega
    simp [Nat.mod_eq_of_lt q, Nat.mod_eq_of_lt r]