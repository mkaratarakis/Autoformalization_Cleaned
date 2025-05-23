import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) : x * 1#w = x := by
  cases w with
  | zero =>
    -- The type of bitvectors of width 0 is a subsingleton
    exact Subsingleton.elim _ _
  | succ n =>
    -- We need to show that x * 1#(n + 1) = x
    -- It suffices to show that the natural number representation of x * 1#(n + 1) is equal to the natural number representation of x
    have h : (x * 1#(n + 1)).toNat = x.toNat := by
      -- Using the property of natural numbers
      rw [toNat_mul, Nat.mul_one]
    -- Using the theorem that if the natural number representation of two bitvectors of the same width are equal, then the bitvectors themselves are equal
    exact toNat_inj h

/- ACTUAL PROOF OF BitVec.mul_one -/

example (x : BitVec w) : x * 1#w = x := by
  cases w
  · apply Subsingleton.elim
  · apply eq_of_toNat_eq; simp [Nat.mod_eq_of_lt]