import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Int) : BitVec.ofInt n (x + y) =
    BitVec.ofInt n x + BitVec.ofInt n y := by
  -- Step 1: Show that the integer representation of BitVec.ofInt(n, x + y) is equal to (x + y) % 2^n
  have h₁ : (BitVec.ofInt n (x + y)).toInt = (x + y) % 2^n := by
    rw [BitVec.toInt_ofInt]
    rfl

  -- Step 2: Show that the integer representation of BitVec.ofInt(n, x) + BitVec.ofInt(n, y) is equal to (x % 2^n + y % 2^n) % 2^n
  have h₂ : (BitVec.ofInt n x + BitVec.ofInt n y).toInt = (x % 2^n + y % 2^n) % 2^n := by
    rw [BitVec.toInt_add]
    rw [BitVec.toInt_ofInt]
    rw [BitVec.toInt_ofInt]
    rfl

  -- Step 3: Use the properties of modulo arithmetic to show that (x + y) % 2^n = (x % 2^n + y % 2^n) % 2^n
  have h₃ : (x + y) % 2^n = (x % 2^n + y % 2^n) % 2^n := by
    rw [Int.add_mod]
    rfl

  -- Step 4: Conclude that BitVec.ofInt(n, x + y) = BitVec.ofInt(n, x) + BitVec.ofInt(n, y)
  rw [BitVec.ext_int]
  exact h₃.trans h₂.symm

/- ACTUAL PROOF OF BitVec.ofInt_add -/

example {n} (x y : Int) : BitVec.ofInt n (x + y) =
    BitVec.ofInt n x + BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp