import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := { decide := true }) [sign]