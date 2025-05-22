import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {x k l : Nat} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l := by
  have h1 : x ^ k ∣ x ^ l ↔ x ^ k ≤ x ^ l := by
    exact dvd_iff_le_of_pos (pow_pos w _) (pow_pos w _)
  have h2 : x ^ k ≤ x ^ l ↔ k ≤ l := by
    exact pow_right_strictMono w
  rw [h1, h2]

/- ACTUAL PROOF OF Nat.pow_dvd_pow_iff_le_right -/

example {x k l : Nat} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l := by
  rw [pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w), Nat.pow_le_pow_iff_right w]