import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Intrinsic

open IsClosed
open AffineSubspace Set
open scoped Pointwise
variable {𝕜 V W Q P : Type*}
variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}
variable {𝕜}

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure]
  have h_sub : s ⊆ (↑) '' ((↑) ⁻¹' s) := by
    intro x
    simp
  have h_eq : ((↑) '' ((↑) ⁻¹' s)) ⊆ s := by
    intro x
    simp
  have h_closure : closure ((↑) ⁻¹' s : Set (affineSpan 𝕜 s)) = ((↑) ⁻¹' s) := hs.closure_eq
  rw [h_closure]
  ext y
  constructor
  · intro hy
    rw [mem_image] at hy
    rcases hy with ⟨z, hz1, hz2⟩
    exact hz2
  · intro hy
    use y
    simp

/- ACTUAL PROOF OF IsClosed.intrinsicClosure -/

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset