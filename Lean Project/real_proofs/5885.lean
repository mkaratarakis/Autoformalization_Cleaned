import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.Minpoly.Basic

open minpoly
open scoped Classical
open Polynomial Set Function
variable {A B B' : Type*}
variable (A) [CommRing A] [Ring B] [Algebra A B]
variable [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']
variable {x : B}
variable {x : B}


example (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1