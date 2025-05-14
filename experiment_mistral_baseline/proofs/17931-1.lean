import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by
  funext
  dsimp [PInfty, PInftyToNormalizedMooreComplex]
  rw [CategoryTheory.Functor.comp_map]
  rfl

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex -/

example (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by
  aesop_cat