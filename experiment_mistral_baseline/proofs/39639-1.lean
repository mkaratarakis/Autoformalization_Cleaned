import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

open JoinedIn
open Topology Filter unitInterval Set Function
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}
variable (γ : Path x y)
open ContinuousMap
variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}
variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}
variable (X)
variable {X}
variable {F : Set X}

example (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  obtain ⟨γ, γ_cont, γ_start, γ_end, γ_in_F⟩ := h
  have x_in_F : x ∈ F := by
    have := γ_in_F 0
    rw [γ_start] at this
    exact this
  have y_in_F : y ∈ F := by
    have := γ_in_F 1
    rw [γ_end] at this
    exact this
  exact ⟨x_in_F, y_in_F⟩

/- ACTUAL PROOF OF JoinedIn.mem -/

example (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this