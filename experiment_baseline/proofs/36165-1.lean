import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

open Projectivization
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  constructor
  · intro h
    rcases h with ⟨ff, hff1, hff2, hff3⟩
    have hff4 : ∀ i, (Projectivization.rep (f i)) = ff i := by
      intro i
      exact (Projectivization.rep_mk_eq_iff_eq_smul (hff1 i)).mp (hff2 i)
    rw [Function.comp_apply, hff4]
    exact hff3
  · intro h
    choose a ha using fun i => (Projectivization.rep (f i)).2
    use fun i => a i • (Projectivization.rep (f i))
    constructor
    · intro i
      exact (Projectivization.mk_ne_zero _ _).mpr ⟨a i, (MulAction.mem_nonzero_divisors_iff_ne_zero _).mpr (ha i).1⟩
    · intro i
      exact (Projectivization.rep_mk_eq_iff_eq_smul _ _ _).mpr (ha i).2
    · rw [Function.comp_apply]
      exact (LinearIndependent.smul_iff _ _).mpr h

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