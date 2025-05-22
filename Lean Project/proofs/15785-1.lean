import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (n : Nat) : 1 &&& n = n % 2 := by
  cases h : n % 2 with
  | 0 =>
    simp [and, h]
  | 1 =>
    simp [and, h]
  | _ =>
    exfalso
    exact Nat.mod_lt n (by norm_num)

/- ACTUAL PROOF OF Nat.one_and_eq_mod_two -/

example (n : Nat) : 1 &&& n = n % 2 := by
  if n0 : n = 0 then
    subst n0; decide
  else
    simp only [HAnd.hAnd, AndOp.and, land]
    cases mod_two_eq_zero_or_one n with | _ h => simp [bitwise, n0, h]