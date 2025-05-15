import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by
  apply PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap -/

example (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by
  aesop_cat