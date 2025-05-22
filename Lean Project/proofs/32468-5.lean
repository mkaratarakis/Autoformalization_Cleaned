import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {p k m : Nat} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m := by
  have : p ^ 1 ∣ m := by
    have : p ^ (k - 1) * p ∣ m := by
      rw [pow_succ' k p]
      exact hpk
    cases' k with k
    · simp
    · exact this
  rwa [pow_one] at this

/- ACTUAL PROOF OF Nat.dvd_of_pow_dvd -/

example {p k m : Nat} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m := by
  rw [← Nat.pow_one p]; exact pow_dvd_of_le_of_pow_dvd hk hpk