import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext n
  dsimp [inclusionOfMooreComplexMap, PInfty]
  cases n
  · -- Component at degree 0
    simp
  · -- Component at degree n + 1
    simp
    rw [← Category.id_comp (inclusionOfMooreComplexMap X).f (n + 1)]
    exact HigherFacesVanish.inclusionOfMooreComplexMap _ _

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty -/

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_|n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self