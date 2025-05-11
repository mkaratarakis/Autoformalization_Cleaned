import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Antichain

/-!
# Minimality and Maximality

This file proves basic facts about minimality and maximality
of an element with respect to a predicate `P` on an ordered type `α`.

## Implementation Details

This file underwent a refactor from a version where minimality and maximality were defined using
sets rather than predicates, and with an unbundled order relation rather than a `LE` instance.

A side effect is that it has become less straightforward to state that something is minimal
with respect to a relation that is *not* defeq to the default `LE`.
One possible way would be with a type synonym,
and another would be with an ad hoc `LE` instance and `@` notation.
This was not an issue in practice anywhere in mathlib at the time of the refactor,
but it may be worth re-examining this to make it easier in the future; see the TODO below.

## TODO

* In the linearly ordered case, versions of lemmas like `minimal_mem_image` will hold with
  `MonotoneOn`/`AntitoneOn` assumptions rather than the stronger `x ≤ y ↔ f x ≤ f y` assumptions.

* `Set.maximal_iff_forall_insert` and `Set.minimal_iff_forall_diff_singleton` will generalize to
  lemmas about covering in the case of an `IsStronglyAtomic`/`IsStronglyCoatomic` order.

* `Finset` versions of the lemmas about sets.

* API to allow for easily expressing min/maximality with respect to an arbitrary non-`LE` relation.

-/

assert_not_exists CompleteLattice

open Set OrderDual

variable {α : Type*} {P Q : α → Prop} {a x y : α}

section LE

variable [LE α]

@[simp] theorem minimal_toDual : Minimal (fun x ↦ P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[simp] theorem maximal_toDual : Maximal (fun x ↦ P (ofDual x)) (toDual x) ↔ Minimal P x :=
  Iff.rfl

alias ⟨Maximal.of_dual, Maximal.dual⟩ := maximal_toDual

@[simp] theorem minimal_false : ¬ Minimal (fun _ ↦ False) x := by
  simp [Minimal]

@[simp] theorem maximal_false : ¬ Maximal (fun _ ↦ False) x := by
  simp [Maximal]

@[simp] theorem minimal_true : Minimal (fun _ ↦ True) x ↔ IsMin x := by
  simp [IsMin, Minimal]

@[simp] theorem maximal_true : Maximal (fun _ ↦ True) x ↔ IsMax x :=
  minimal_true (α := αᵒᵈ)

@[simp] theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x ↦ P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[simp] theorem maximal_subtype {x : Subtype Q} :
    Maximal (fun x ↦ P x.1) x ↔ Maximal (P ⊓ Q) x :=
  minimal_subtype (α := αᵒᵈ)
example {x : Subtype P} : Maximal (fun _ ↦ True) x ↔ Maximal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Maximal, hx]

theorem minimal_true_subtype {x : Subtype P} : Minimal (fun _ ↦ True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[simp] theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hy hyx ↦ h.le_of_le hy.prop hyx⟩⟩

@[simp] theorem maximal_maximal : Maximal (Maximal P) x ↔ Maximal P x :=
  minimal_minimal (α := αᵒᵈ)

/-- If `P` is down-closed, then minimal elements satisfying `P` are exactly the globally minimal
elements satisfying `P`. -/
theorem minimal_iff_isMin (hP : ∀ ⦃x y⦄, P y → x ≤ y → P x) : Minimal P x ↔ P x ∧ IsMin x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_le (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

/-- If `P` is up-closed, then maximal elements satisfying `P` are exactly the globally maximal
elements satisfying `P`. -/
theorem maximal_iff_isMax (hP : ∀ ⦃x y⦄, P y → y ≤ x → P x) : Maximal P x ↔ P x ∧ IsMax x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_ge (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

theorem Minimal.mono (h : Minimal P x) (hle : Q ≤ P) (hQ : Q x) : Minimal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_le (hle y hQy)⟩

theorem Maximal.mono (h : Maximal P x) (hle : Q ≤ P) (hQ : Q x) : Maximal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_ge (hle y hQy)⟩

theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ P x ∧ Q x) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩

theorem Maximal.and_right (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (P x ∧ Q x)) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

theorem Maximal.and_left (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩

@[simp] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp (config := {contextual := true}) [Minimal]

@[simp] theorem maximal_eq_iff : Maximal (· = y) x ↔ x = y := by
  simp (config := {contextual := true}) [Maximal]

theorem not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ ∃ y, P y ∧ y ≤ x ∧ ¬ (x ≤ y) := by
  simp [Minimal, hx]

theorem not_maximal_iff (hx : P x) : ¬ Maximal P x ↔ ∃ y, P y ∧ x ≤ y ∧ ¬ (y ≤ x) :=
  not_minimal_iff (α := αᵒᵈ) hx

theorem Minimal.or (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨hx, hle⟩ := h
  by_cases hP : P x
  · left
    exact ⟨hP, fun y hy hyx ↦ hle y (Or.inl hy) hyx⟩
  · right
    exact ⟨by rw [not_or] at hx; exact hx hP, fun y hy hyx ↦ hle y (Or.inr hy) hyx⟩

/- ACTUAL PROOF OF Minimal.or -/

example (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩