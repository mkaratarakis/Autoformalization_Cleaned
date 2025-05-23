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
  rcases h₃ with ⟨n, rfl⟩
  rcases h₄ with ⟨m, rfl⟩
  calc
    a = a + 0 := by rw [add_zero]
    _ = a + (n + m) := by rw [add_eq_of_le_of_sub_eq_add h₁ h₂]
    _ = (a + n) + m := by rw [add_assoc]
    _ = b + m := by rw [h₃]
    _ = a := by rw [h₄]

/- ACTUAL PROOF OF Int.le_antisymm -/

example {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← ofNat_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]