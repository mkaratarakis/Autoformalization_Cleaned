import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (a b : Nat) :
    gcd a b = g ↔ g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  constructor
  · intro h
    rw [h]
    exact ⟨gcd_dvd_left a b, gcd_dvd_right a b, fun c hac hbc => dvd_gcd hac hbc⟩
  · rintro ⟨hga, hgb, hc⟩
    apply gcd_eq_iff.2
    exact ⟨hga, hgb, hc⟩

/- ACTUAL PROOF OF Nat.gcd_eq_iff -/

example (a b : Nat) :
    gcd a b = g ↔ g ∣ a ∧ g ∣ b ∧ (∀ c, c ∣ a → c ∣ b → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun _ => Nat.dvd_gcd⟩
  · rintro ⟨ha, hb, hc⟩
    apply Nat.dvd_antisymm
    · apply hc
      · exact gcd_dvd_left a b
      · exact gcd_dvd_right a b
    · exact Nat.dvd_gcd ha hb