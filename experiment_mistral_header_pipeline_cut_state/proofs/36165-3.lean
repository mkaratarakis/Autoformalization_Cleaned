import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Independence

open Projectivization
open scoped LinearAlgebra.Projectivization
variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

example : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  constructor
  · intro h
    rcases h with ⟨g, hg, hl⟩
    have : ∀ i, ∃ a : Kˣ, a • g i = (mk K (g i) (hg i)).rep := fun i =>
      (Projectivization.mk_eq_mk_iff K _ _ (hg i) _).1 (Projectivization.mk_rep _)
    choose a ha using this
    rw [← LinearIndependent.comp_injective (fun i => (a i).inv • ((mk K (g i) (hg i)).rep))
      (fun i j => (Units.inv_injective _).ne)]
    convert hl
    ext i
    rw [Units.inv_smul_val, MulAction.smul_inv_smul₀, ha]
  · intro hl
    have hg : ∀ i, (f i).rep ≠ 0 := fun i => Projectivization.rep_nonzero _
    exact Independent.mk (Projectivization.rep ∘ f) hg hl

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