import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/

open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)
variable [Algebra R A]
example {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩

theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

end Ring

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] (f : R →+* S)

theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
(hb : IsIntegral R b) : IsIntegral R (f b) := by
  obtain ⟨p, hp_monic, hp_eval⟩ := hb
  use p
  constructor
  · exact hp_monic
  · rw [← aeval_def (algebraMap R C), aeval_def, ← AlgHomClass.commutes, aeval_map_algebraMap]
    exact hp_eval

/- ACTUAL PROOF OF IsIntegral.map -/

example {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  obtain ⟨P, hP⟩ := hb
  refine ⟨P, hP.1, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap A,
    aeval_algHom_apply, aeval_map_algebraMap, aeval_def, hP.2, _root_.map_zero]