import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (b : Nat) : 0 % b = 0 := by
  cases b
  . rfl
  . simp [mod, Nat.sub]

/- ACTUAL PROOF OF Nat.zero_mod -/

example (b : Nat) : 0 % b = 0 := by
  rw [mod_eq]
  have : ¬ (0 < b ∧ b = 0) := by
    intro ⟨h₁, h₂⟩
    simp_all
  simp [this]