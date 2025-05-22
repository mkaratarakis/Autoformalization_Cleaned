import Init.Data.Nat.Linear
import Init.Data.Nat.Power2

open Nat


example (n : Nat) : n.nextPowerOfTwo.isPowerOfTwo := by
  unfold nextPowerOfTwo
  unfold nextPowerOfTwo.go
  apply isPowerOfTwo.rec
  · apply isPowerOfTwo.one
  · intros power _n ih
    apply ih
    simp [Nat.sub_eq_zero_iff_le]
    apply Nat.sub_lt
    simp
    apply Nat.lt_of_lt_of_le
    · simp
    · apply Nat.le_mul_of_pos_right
      simp
      apply Nat.pos_of_ne_zero
      simp

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