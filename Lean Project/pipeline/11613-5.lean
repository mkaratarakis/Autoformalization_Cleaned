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
  have h1 : intrinsicClosure 𝕜 s = (Subtype.val '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :=
    rfl
  rw [h1]
  have h2 : (closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) = ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) :=
    hs.closure_eq
  rw [h2]
  have h3 : (Subtype.val '' ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) = s := by
    ext x
    simp only [mem_image, mem_preimage, Subtype.exists, Subtype.coe_mk, exists_prop]
    exact ⟨fun ⟨y, hy, hxy⟩ => hxy.symm ▸ hy, fun hx => ⟨⟨x, hx⟩, hx, rfl⟩⟩
  rw [h3]

/- ACTUAL PROOF OF IsClosed.intrinsicClosure -/

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset