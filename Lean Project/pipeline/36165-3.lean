import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

open Projectivization
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  constructor
  · intro h
    rcases h with ⟨g, hg, hg_lin_ind⟩
    have hg_rep : ∀ i, (Projectivization.rep ∘ fun i => mk K (g i) (hg i)) i ≠ 0 := fun i => Projectivization.rep_nonzero (mk K (g i) (hg i))
    apply LinearIndependent.of_comp_injective
    · intro i
      apply exists_smul_eq_mk_rep
      exact hg i
    · intro i j hij
      rw [Function.comp_apply, Function.comp_apply] at hij
      simp only [Projectivization.mk_rep] at hij
      rcases hij with ⟨u, rfl⟩
      use u
      rfl
    · exact hg_lin_ind
  · intro h
    choose a ha using fun i => exists_smul_eq_mk_rep (f i).rep (Projectivization.rep_nonzero (f i))
    refine Independent.mk (fun i => a i • (Projectivization.rep ∘ f) i) (fun i => _) (h.of_comp_injective _ _)
    · exact (Units.mk0_ne_zero _).1 (ha i).1
    · intro i j hij
      rw [Function.comp_apply, Function.comp_apply] at hij
      rcases hij with ⟨u, rfl⟩
      use u
      rfl
    · intro i
      exact (ha i).2

/- ACTUAL PROOF OF Projectivization.independent_iff -/

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh.units_smul a
    ext i
    exact (ha i).symm
  · convert Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero