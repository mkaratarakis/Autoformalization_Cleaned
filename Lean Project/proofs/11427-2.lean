import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m with
  | zero =>
    exact ⟨dvd_zero _ _, dvd_refl _⟩
  | succ m ih =>
    have h1 : gcd (succ m) n = gcd (n % succ m) (succ m) := gcd_rec _ _
    rw [h1]
    apply ih
    exact ⟨dvd_of_mod_dvd (dvd_refl _), dvd_refl _⟩

/- ACTUAL PROOF OF Nat.gcd_dvd -/

example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (dvd_mod_iff IH.2).1 IH.1⟩