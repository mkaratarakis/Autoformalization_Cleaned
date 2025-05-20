import Mathlib.Topology.PartialHomeomorph
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.IsLocalHomeomorph

open IsLocalHomeomorphOn
open Topology
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z)
  (f : X → Y) (s : Set X) (t : Set Y)

example (h : ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hxe, he⟩ := h x hx
  let e' := PartialHomeomorph.mk (e.toPartialEquiv.trans (PartialEquiv.setCongr (he.symm)))
    (by simpa using e.continuousOn_toFun) (by simpa using e.continuousOn_invFun) e.open_source
    (by simpa using e.open_target)
  use e'
  constructor
  · exact hxe
  · ext x'
    by_cases hx' : x' ∈ e'.source
    · simp [hx', e'.mapsTo, he]
    · simp [hx']

-- Continue with the rest of the proof...

/- ACTUAL PROOF OF IsLocalHomeomorphOn.mk -/

example (h : ∀ x ∈ s, ∃ e : PartialHomeomorph X Y, x ∈ e.source ∧ Set.EqOn f e e.source) :
    IsLocalHomeomorphOn f s := by
  intro x hx
  obtain ⟨e, hx, he⟩ := h x hx
  exact
    ⟨{ e with
        toFun := f
        map_source' := fun _x hx ↦ by rw [he hx]; exact e.map_source' hx
        left_inv' := fun _x hx ↦ by rw [he hx]; exact e.left_inv' hx
        right_inv' := fun _y hy ↦ by rw [he (e.map_target' hy)]; exact e.right_inv' hy
        continuousOn_toFun := (continuousOn_congr he).mpr e.continuousOn_toFun },
      hx, rfl⟩