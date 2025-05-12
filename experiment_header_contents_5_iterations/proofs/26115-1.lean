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
  obtain ⟨e_g, hxge, rfl⟩ := hg (e x) (h hx hxe)
  refine ⟨e_g.trans e, hxe, ?_⟩
  ext y
  · have h : y ∈ e.source := hxe
    rw [h]
    exact e_g.map_source hxge
  · have h : y ∈ e_g.source := hxge
    rw [h]
    exact e.map_source hxe

/- ACTUAL PROOF OF IsLocalHomeomorphOn.comp -/

example (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
    (h : Set.MapsTo f s t) : IsLocalHomeomorphOn (g ∘ f) s := by
  intro x hx
  obtain ⟨eg, hxg, rfl⟩ := hg (f x) (h hx)
  obtain ⟨ef, hxf, rfl⟩ := hf x hx
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩