import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x : Nat) : x % 1 = 0 := by
  have : ∀ y, y < 1 → y = 0 := by
    intro y h
    cases y
    · exact rfl
    · exact absurd (Nat.succ_lt_succ_iff.mp h) (Nat.not_lt_zero _)
  apply this
  exact Nat.mod_lt x (by decide)

/- ACTUAL PROOF OF Nat.mod_one -/

example (x : Nat) : x % 1 = 0 := by
  have h : x % 1 < 1 := mod_lt x (by decide)
  have : (y : Nat) → y < 1 → y = 0 := by
    intro y
    cases y with
    | zero   => intro _; rfl
    | succ y => intro h; apply absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero y)
  exact this _ h