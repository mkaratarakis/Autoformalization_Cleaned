import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (b : Nat) : 0 % b = 0 := by
  unfold Nat.mod
  simp
  split
  . intro h
    exfalso
    apply h.right
    apply Nat.not_lt_zero
  . rfl

/- ACTUAL PROOF OF Nat.zero_mod -/

example (b : Nat) : 0 % b = 0 := by
  rw [mod_eq]
  have : ¬ (0 < b ∧ b = 0) := by
    intro ⟨h₁, h₂⟩
    simp_all
  simp [this]