import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  have h₃ : ∃ n : ℕ, a + n = b := by
    apply le_iff_exists_nat.1
    exact h₁
  have h₄ : ∃ m : ℕ, b + m = a := by
    apply le_iff_exists_nat.1
    exact h₂
  cases' h₃ with n h₃
  cases' h₄ with m h₄
  rw [h₃] at h₄
  rw [h₄] at h₃
  have h₅ : a + (m + n) = a := by
    rw [add_assoc]
    exact h₃
  have h₆ : m + n = 0 := by
    apply add_right_cancel
    exact h₅
  have h₇ : n = 0 := by
    apply Nat.eq_zero_of_add_eq_zero_left
    exact h₆
  rw [h₇] at h₃
  exact h₃

/- ACTUAL PROOF OF Int.le_antisymm -/

example {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← ofNat_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]