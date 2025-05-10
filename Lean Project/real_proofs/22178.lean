import Mathlib.Algebra.Order.Field.Power
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm

open padicNorm
open padicValRat
variable {p : ℕ}


example : padicNorm p 0 = 0 := by
  simp [padicNorm]