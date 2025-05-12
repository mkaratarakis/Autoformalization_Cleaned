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
  intro x hx
  obtain ⟨e, hxe, rfl⟩ := hf x hx
  obtain ⟨e_g, hxge, rfl⟩ := hg (e x) (h hxe)
  refine ⟨e_g.trans e, hxe, funext fun y => _⟩
  by_cases hy : y ∈ e.source
  · exact e_g.map_source (e_g.map_source (e.map_source hy))
  · rw [hy.symm.rec (not_mem_subset (e.source ⊆ e.toPartialEquiv.source) hy)]
    rw [PartialEquiv.trans_coe, PartialEquiv.trans_symm_apply, PartialEquiv.trans_apply_not_of_not_mem_source]
    exact e.right_inv (e_g.map_target (e.map_source hy))

/- ACTUAL PROOF OF IsLocalHomeomorphOn.comp -/

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩