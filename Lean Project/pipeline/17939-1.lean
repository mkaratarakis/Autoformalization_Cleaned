import Mathlib.AlgebraicTopology.DoldKan.FunctorN
import Mathlib.AlgebraicTopology.DoldKan.Normalized

open AlgebraicTopology
open DoldKan
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable {A : Type*} [Category A] [Abelian A] {X : SimplicialObject A}

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext n
  · calc
      ((inclusionOfMooreComplexMap X ≫ PInfty).app (op [n]))
        = ((inclusionOfMooreComplexMap X).app (op [n]) ≫ PInfty.app (op [n])) := rfl
    _ = ((inclusionOfMooreComplexMap X).app (op [n]) ≫ 𝟙 (X.obj (op [n]))) := by
        apply DoldKan.PInfty_app_self
    _ = ((inclusionOfMooreComplexMap X).app (op [n])) := by simp
  · calc
      ((inclusionOfMooreComplexMap X ≫ PInfty).app (op [n+1]))
        = ((inclusionOfMooreComplexMap X).app (op [n+1]) ≫ PInfty.app (op [n+1])) := rfl
    _ = ((inclusionOfMooreComplexMap X).app (op [n+1])) := by
        apply DoldKan.PInfty_app_higher_faces_vanish

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty -/

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_|n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self