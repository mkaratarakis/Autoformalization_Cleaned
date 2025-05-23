import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  have hn : 0 ≤ -a := by
    exact neg_nonneg_of_nonpos H
  calc
  (natAbs a : Int) = natAbs (-a) := by rw [Int.natAbs_neg]
  _ = -a := by rw [Int.natAbs_of_nonneg hn]

/- ACTUAL PROOF OF Int.ofNat_natAbs_of_nonpos -/

example {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]