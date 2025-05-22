import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction' m with m ih
  · -- Base case: m = 0
    exact ⟨dvd_zero _, dvd_refl _⟩

  · -- Inductive step: m > 0
    let g := gcd m n
    have h₁ : g = gcd (n % m) m := gcd_rec m n
    rw [h₁] at ih
    have h₂ : g ∣ n % m := ih.1
    have h₃ : g ∣ m := ih.2
    exact ⟨h₃, dvd_add h₂ h₃⟩

/- ACTUAL PROOF OF Nat.gcd_dvd -/

example (m n : Nat) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) := by
  induction m, n using gcd.induction with
  | H0 n => rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩
  | H1 m n _ IH => rw [← gcd_rec] at IH; exact ⟨IH.2, (dvd_mod_iff IH.2).1 IH.1⟩