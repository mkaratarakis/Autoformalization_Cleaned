import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Basic

/-!
# Properties of `List.enum`

## Deprecation note

Many lemmas in this file have been replaced by theorems in Lean4,
in terms of `xs[i]?` and `xs[i]` rather than `get` and `get?`.

The deprecated results here are unused in Mathlib.
Any downstream users who can not easily adapt may remove the deprecations as needed.
-/

namespace List

variable {α : Type*}
example {l : List α} {n : ℕ} {p : α × ℕ → Prop} :
    (∀ x ∈ l.zipIdx n, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (l[i], n + i) := by
  simp only [forall_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

/-- Variant of `forall_mem_zipIdx` with the `zipIdx` argument specialized to `0`. -/
theorem forall_mem_zipIdx' {l : List α} {p : α × ℕ → Prop} :
    (∀ x ∈ l.zipIdx, p x) ↔ ∀ (i : ℕ) (_ : i < length l), p (l[i], i) :=
  forall_mem_zipIdx.trans <| by simp

theorem exists_mem_zipIdx {l : List α} {n : ℕ} {p : α × ℕ → Prop} :
    (∃ x ∈ l.zipIdx n, p x) ↔ ∃ (i : ℕ) (_ : i < length l), p (l[i], n + i) := by
  simp only [exists_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

/-- Variant of `exists_mem_zipIdx` with the `zipIdx` argument specialized to `0`. -/
theorem exists_mem_zipIdx' {l : List α} {p : α × ℕ → Prop} :
    (∃ x ∈ l.zipIdx, p x) ↔ ∃ (i : ℕ) (_ : i < length l), p (l[i], i) :=
  exists_mem_zipIdx.trans <| by simp

@[deprecated (since := "2025-01-28")]
alias forall_mem_enumFrom := forall_mem_zipIdx
@[deprecated (since := "2025-01-28")]
alias forall_mem_enum := forall_mem_zipIdx'
@[deprecated (since := "2025-01-28")]
alias exists_mem_enumFrom := exists_mem_zipIdx
@[deprecated (since := "2025-01-28")]
alias exists_mem_enum := exists_mem_zipIdx'

end List

theorem List.mem_enum_iff_get? {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = some x.2 := by
  rw [List.mem_zipIdx_iff_getElem?]
  exact Iff.rfl

/- ACTUAL PROOF OF List.mem_enum_iff_get? -/

example {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = x.2 := by
  simp [mem_enum_iff_getElem?]