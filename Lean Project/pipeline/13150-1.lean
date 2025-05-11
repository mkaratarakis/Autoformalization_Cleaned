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

theorem List.mk_mem_enumFrom_iff_le_and_get?_sub {n i : ℕ} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l.get? (i - n) = some x := by
  simp only [zipIdx_eq_enumFrom, mem_zipIdx_iff, forall_mem_zipIdx, get?_eq_some]
  split
  · intro h
    exact ⟨le_of_lt (fst h), (snd h).symm⟩
  · rintro ⟨hn, hx⟩
    exact ⟨hn, hx.symm⟩

/- ACTUAL PROOF OF List.mk_mem_enumFrom_iff_le_and_get?_sub -/

example {n i : ℕ} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l.get? (i - n) = x := by
  simp [mk_mem_enumFrom_iff_le_and_getElem?_sub]