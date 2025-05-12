import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

open Projectivization
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  constructor
  · intro hInd
    cases' hInd with ff hf hl
    have hrep : ∀ i, (f i).rep = a i • ff i := fun i =>
      let ⟨u, hu⟩ := exists_smul_eq_mk_rep (ff i) (hf i)
      (mk_eq_mk_iff _ _ _ (rep_nonzero _) (hf _)).mp (congr_arg _ (congr_fun hu i))
    apply LinearIndependent.comp K _ _ hl
    intro i
    rw [hrep i]
    apply smul_right_injective _ _
    · apply Units.ne_zero
    · exact hf i
  · intro hl
    refine' Independent.mk (Projectivization.rep ∘ f) _ hl
    intro i
    exact rep_nonzero (f i)

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