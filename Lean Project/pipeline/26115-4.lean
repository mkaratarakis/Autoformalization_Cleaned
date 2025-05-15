import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.IsLocalHomeomorph

open IsLocalHomeomorphOn
open Topology
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)
variable {g f s t}

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intros x hx
  obtain ⟨e_f, hx_e_f, rfl⟩ := hf x hx
  obtain ⟨e_g, hx_e_g, rfl⟩ := hg (e_f x) (h hx_e_f)
  refine ⟨e_f.trans e_g, _, ?_⟩
  · exact e_f.map_source hx_e_f
  · ext y
    by_cases hy : y ∈ e_f.source
    · rw [PartialHomeomorph.trans_apply hy]
      rfl
    · rw [dif_neg hy, dif_neg hy]
      rfl

/- ACTUAL PROOF OF IsLocalHomeomorphOn.comp -/

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩