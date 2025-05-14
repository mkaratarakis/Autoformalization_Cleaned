import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext n
  · -- Component at degree 0
    simp only [inclusionOfMooreComplexMap_f_0, PInfty_f_0, comp_id]

  · -- Component at degree n + 1
    simp only [inclusionOfMooreComplexMap_f_succ, PInfty_f_succ, HigherFacesVanish.inclusionOfMooreComplexMap]

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty -/

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_|n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self