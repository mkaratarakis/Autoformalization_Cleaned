import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Nat) : BitVec.ofNat n x - BitVec.ofNat n y = .ofNat n ((2^n - y % 2^n) + x) := by
  have h1 : toNat (BitVec.ofNat n x - BitVec.ofNat n y) = (x - y) % 2^n := by
    rw [BitVec.toNat_sub]
    rw [BitVec.toNat_ofNat]
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_add_mod]
    exact Nat.mod_lt (x - y) (2^n)
  have h2 : toNat (BitVec.ofNat n ((2^n - y % 2^n) + x)) = ((2^n - y % 2^n) + x) % 2^n := by
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_add_mod]
    exact Nat.mod_lt ((2^n - y % 2^n) + x) (2^n)
  rw [← h1, ← h2]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.mod_lt y (2^n)) (Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ n) (Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ n)))))))))))))))))

/- ACTUAL PROOF OF BitVec.ofNat_sub_ofNat -/

example {n} (x y : Nat) : BitVec.ofNat n x - BitVec.ofNat n y = .ofNat n ((2^n - y % 2^n) + x) := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]