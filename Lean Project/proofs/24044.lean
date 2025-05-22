import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  by_cases hk : k = 0
  · exact dvd_zero (lcm m n)

  · have hm : m > 0 := Nat.pos_of_dvd_of_pos H1 hk
    have hn : n > 0 := Nat.pos_of_dvd_of_pos H2 hk
    have hgcd : gcd m n * lcm m n = m * n := gcd_mul_lcm m n
    have hgcdk : gcd (m * k) (n * k) = gcd m n * k := gcd_mul_right m k n
    rw [mul_comm] at hgcdk
    rw [hgcd]
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