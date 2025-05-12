import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by
  rw [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_map]
  apply CategoryTheory.Functor.map_id

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap -/

example (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by
  aesop_cat