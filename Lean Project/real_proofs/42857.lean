import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.ReesAlgebra

open reesAlgebra
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
open Polynomial
open Polynomial
variable {I}


example (hI : I.FG) : (reesAlgebra I).FG := by
  classical
    obtain ⟨s, hs⟩ := hI
    rw [← adjoin_monomial_eq_reesAlgebra, ← hs]
    use s.image (monomial 1)
    rw [Finset.coe_image]
    change
      _ =
        Algebra.adjoin R
          (Submodule.map (monomial 1 : R →ₗ[R] R[X]) (Submodule.span R ↑s) : Set R[X])
    rw [Submodule.map_span, Algebra.adjoin_span]