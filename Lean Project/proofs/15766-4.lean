import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x i : Nat) :
    (x.testBit i).toNat = x / 2 ^ i % 2 := by

simp [testBit, Bool.toNat, decide_eq_true_eq]
split
· intros h
  simp [h]
· intros h
  simp [h]
  norm_num

/- ACTUAL PROOF OF Nat.toNat_testBit -/

example (x i : Nat) :
    (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_to_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2^i) <;> simp_all