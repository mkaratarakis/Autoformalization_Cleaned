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
    dsimp
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow, assoc, assoc, factorThru_arrow,
      ← inclusionOfMooreComplexMap_f, ← normalizedMooreComplex_objD,
      ← (inclusionOfMooreComplexMap X).comm (n + 1) n, inclusionOfMooreComplexMap_f,
      factorThru_arrow_assoc, ← alternatingFaceMapComplex_obj_d]
    exact PInfty.comm (n + 1) n

/- ACTUAL PROOF OF AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty -/

example (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X := by
  ext (_|n)
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_P_eq_self