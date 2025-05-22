import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (a b : Int) : natAbs (a * b) = natAbs a * natAbs b := by
  cases a <;> cases b <;>
    simp only [← Int.mul_def, Int.mul, natAbs_negOfNat] <;> simp only [natAbs]