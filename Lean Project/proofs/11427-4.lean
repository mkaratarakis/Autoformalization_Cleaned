import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m with
  | zero =>
    exact ⟨(by simp [gcd]), (by simp [gcd])⟩
  | succ m ih =>
    rw [gcd_rec]
    have ih := ih
    apply And.intro
    · exact ih.right
    · apply dvd_add
      · exact ih.left
      · apply dvd_of_mod_dvd_right
        exact ih.right

/- ACTUAL PROOF OF Nat.gcd_dvd -/

example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (dvd_mod_iff IH.2).1 IH.1⟩