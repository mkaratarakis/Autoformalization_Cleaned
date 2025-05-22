import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat

example {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  by_cases hk : k = 0
  · exact dvd_zero _
  · have hm : m > 0 := pos_of_dvd_of_pos H1 (Nat.pos_of_ne_zero hk)
    have hn : n > 0 := pos_of_dvd_of_pos H2 (Nat.pos_of_ne_zero hk)
    rw [lcm_mul_gcd_cancel hm hn]
    apply dvd_gcd
    · apply dvd_mul_of_dvd_left
      exact H1
    · apply dvd_mul_of_dvd_right
      exact H2

/- ACTUAL PROOF OF Nat.lcm_dvd -/

example {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  match eq_zero_or_pos k with
  | .inl h => rw [h]; exact Nat.dvd_zero _
  | .inr kpos =>
    apply Nat.dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos))
    rw [gcd_mul_lcm, ← gcd_mul_right, Nat.mul_comm n k]
    exact dvd_gcd (Nat.mul_dvd_mul_left _ H2) (Nat.mul_dvd_mul_right H1 _)