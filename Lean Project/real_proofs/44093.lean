import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example (x y : BitVec v) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.or_lt_two_pow x.isLt y.isLt).symm