import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec w) : x + y - y = x := by
  -- Show that (x + y - y).toNat = x.toNat
  suffices (x + y - y).toNat = x.toNat by
    apply eq_of_toNat_eq
    exact this
  -- Show that y.toNat < 2^w
  have y_lt_2w : y.toNat < 2^w := by
    apply val_bound
  -- Simplify (x + y - y).toNat step by step
  calc
    (x + y - y).toNat
      = (2^w - y.toNat + (x + y).toNat) % 2^w := by
        rw [toNat_sub, toNat_add]
        simp [Nat.mod_eq_of_lt y_lt_2w]
    _ = (2^w - y.toNat + (x.toNat + y.toNat) % 2^w) % 2^w := by
        rw [toNat_add]
    _ = ((x.toNat + y.toNat) % 2^w + (2^w - y.toNat)) % 2^w := by
        rw [Nat.add_mod]
    _ = (x.toNat + y.toNat + 2^w - y.toNat) % 2^w := by
        rw [Nat.add_assoc]
    _ = (x.toNat + (y.toNat + 2^w - y.toNat)) % 2^w := by
        rw [Nat.add_assoc]
    _ = (x.toNat + 2^w) % 2^w := by
        simp [Nat.add_sub_cancel]
    _ = x.toNat % 2^w := by
        rw [Nat.mod_eq_of_lt (Nat.lt_two_pow _ _)]
    _ = x.toNat := by
        apply toNat_mod

/- ACTUAL PROOF OF BitVec.add_sub_cancel -/

example (x y : BitVec w) : x + y - y = x := by
  apply eq_of_toNat_eq
  have y_toNat_le := Nat.le_of_lt y.isLt
  rw [toNat_sub, toNat_add, Nat.add_comm, Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_sub_assoc y_toNat_le,
      Nat.add_sub_cancel_left, Nat.add_mod_right, toNat_mod_cancel]