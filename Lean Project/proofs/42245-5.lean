import Init.Data.Nat.Linear
import Init.Data.Nat.Power2

open Nat


example (n : Nat) : n.nextPowerOfTwo.isPowerOfTwo := by
  unfold nextPowerOfTwo
  unfold nextPowerOfTwo.go
  by_cases h : 1 < n
  · simp [h]
    unfold nextPowerOfTwo.go
    by_cases h2 : 2 < n
    · simp [h2]
      exact nextPowerOfTwo_rec n 2 h2
    · simp [h2]
      exact isPowerOfTwo_two
  · simp [h]
    exact isPowerOfTwo_one

/- ACTUAL PROOF OF Nat.isPowerOfTwo_nextPowerOfTwo -/

example (n : Nat) : n.nextPowerOfTwo.isPowerOfTwo := by
  apply isPowerOfTwo_go
  apply one_isPowerOfTwo
where
  isPowerOfTwo_go (power : Nat) (h₁ : power > 0) (h₂ : power.isPowerOfTwo) : (nextPowerOfTwo.go n power h₁).isPowerOfTwo := by
    unfold nextPowerOfTwo.go
    split
    . exact isPowerOfTwo_go (power*2) (Nat.mul_pos h₁ (by decide)) (Nat.mul2_isPowerOfTwo_of_isPowerOfTwo h₂)
    . assumption
  termination_by n - power
  decreasing_by simp_wf; apply nextPowerOfTwo_dec <;> assumption