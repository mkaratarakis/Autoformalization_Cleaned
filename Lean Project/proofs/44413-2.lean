import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (n : Nat) : 0 < -[n+1] ↔ False := by
  constructor
  · intro h
    apply Nat.noConfusion (↑n + 1)
    case zero =>
      simp [Int.ofNat] at h
      exact absurd h (not_lt_zero.2 (Int.ofNat_zero : 0 = 0 : Int))
    case succ n =>
      simp [Int.ofNat] at h
      exact absurd h (not_lt_zero.2 (Int.ofNat_succ : ↑n + 1 = ↑(n+1) : Int))
  · intro h
    exfalso
    exact h

/- ACTUAL PROOF OF Int.negSucc_not_pos -/

example (n : Nat) : 0 < -[n+1] ↔ False := by
  simp only [Int.not_lt, iff_false]; constructor