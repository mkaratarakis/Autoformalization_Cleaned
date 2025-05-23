import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  have hn : 0 ≤ -a := by
    exact neg_nonneg_of_nonpos H
  have habs:  natAbs  a =  natAbs(-a) := by
    exact abs_neg a
  have hcon :  natAbs(-a) = -a := by
    exact natAbs_of_nonneg hn
  calc
  natAbs a =  natAbs(-a) := habs
  _   = -a := hcon

/- ACTUAL PROOF OF Int.ofNat_natAbs_of_nonpos -/

example {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]