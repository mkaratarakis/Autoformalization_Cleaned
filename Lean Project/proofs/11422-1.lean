import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example : k ∣ m → k ∣ n → k ∣ gcd m n := by
  intro hkm hkn
  induction m with
  | zero =>
    simp [gcd]
    exact hkn
  | succ m ih =>
    simp [gcd]
    obtain ⟨q, r, hq, hr⟩ := Nat.div_mod_of_dvd hkm
    rw [Nat.mod_eq_of_lt hr]
    apply ih
    · apply Dvd.intro
      use q
      simp [hr, hq, Nat.mul_sub_left_cancel hr]
    · apply Dvd.intro
      use q
      simp [hr, hq, Nat.mul_sub_left_cancel hr]

/- ACTUAL PROOF OF Nat.dvd_gcd -/

example : k ∣ m → k ∣ n → k ∣ gcd m n := by
  induction m, n using gcd.induction with intro km kn
  | H0 n => rw [gcd_zero_left]; exact kn
  | H1 n m _ IH => rw [gcd_rec]; exact IH ((dvd_mod_iff km).2 kn) km