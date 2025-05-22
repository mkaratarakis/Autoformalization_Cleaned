import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y := by
  by_contra h
  let ⟨i, hp⟩ := Nat.exists_testBit_ne_of_ne h
  have := pred i
  rw [hp] at this
  tauto

/- ACTUAL PROOF OF Nat.eq_of_testBit_eq -/

example {x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y := by
  if h : x = y then
    exact h
  else
    let ⟨i,eq⟩ := ne_implies_bit_diff h
    have p := pred i
    contradiction