import Mathlib.RingTheory.Multiplicity
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.Padics.PadicVal.Defs

open padicValNat
open Nat
open multiplicity
variable {p : ℕ}
open multiplicity
open List


example : padicValNat p 0 = 0 := by
  simp [padicValNat]