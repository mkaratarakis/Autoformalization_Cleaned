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
  rcases h with ⟨γ, hγ⟩
  exact ⟨hγ 0, hγ 1⟩

/- ACTUAL PROOF OF JoinedIn.mem -/

example (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this