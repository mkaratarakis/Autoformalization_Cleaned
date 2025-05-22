import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  let ⟨n, hn⟩ := le.dest h₁; let ⟨m, hm⟩ := le.dest h₂
  have := hn; rw [← hm, Int.add_assoc, ← ofNat_add] at this
  have := Int.ofNat.inj <| Int.add_left_cancel <| this.trans (Int.add_zero _).symm
  rw [← hn, Nat.eq_zero_of_add_eq_zero_left this, ofNat_zero, Int.add_zero a]