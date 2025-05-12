import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA

open εNFA
open Set
open Computability
variable {α : Type u} {σ σ' : Type v} (M : εNFA α σ) {S : Set σ} {x : List α} {s : σ} {a : α}
variable {M}
variable (M)

example (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction' x with a x ih
  · simpa using evalFrom_nil ∅
  · simpa [ih, stepSet_empty] using evalFrom_append_singleton ∅ x a

/- ACTUAL PROOF OF εNFA.evalFrom_empty -/

example (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction' x using List.reverseRecOn with x a ih
  · rw [evalFrom_nil, εClosure_empty]
  · rw [evalFrom_append_singleton, ih, stepSet_empty]