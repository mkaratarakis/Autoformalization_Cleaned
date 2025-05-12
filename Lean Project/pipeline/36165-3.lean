import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

open Projectivization
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  constructor
  · intro hInd
    cases' hInd with ff hf hl
    have hrep : ∀ i, (f i).rep = ff i := fun i =>
      (mk_eq_mk_iff K _ _ (rep_nonzero _) (hf _)).mp (mk_rep _)
    exact hl.comp _ (fun i => (hrep i).symm)
  · intro hl
    refine' Independent.mk _ (fun i => (f i).rep_nonzero) hl
    ext i
    exact (f i).mk_rep

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