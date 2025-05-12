import Mathlib.Order.Partition.Equipartition
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

open Finpartition
open Finset Nat
variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : ℕ} {P : Finpartition s}
variable (h : a * m + b * (m + 1) = s.card)
variable {h}
variable (P h)
variable (s)

example (hn : n ≠ 0) (hs : n ≤ s.card) :
    ∃ P : Finpartition s, P.IsEquipartition ∧ P.parts.card = n := by
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hn'' : n ≤ s.card := hs
  let P := equitabilise s n
  have hP : P.IsEquipartition := equitabilise_is_equipartition s n
  have hP' : P.parts.card = n - s.card % n + s.card % n :=
    (Finpartition.card_parts_equitabilise s n).trans
      (by rw [Nat.sub_add_cancel (s.card % n)])
  have hP'' : P.parts.card = n := by rw [hP']; simp
  exact ⟨P, hP, hP''⟩

/- ACTUAL PROOF OF Finpartition.exists_equipartition_card_eq -/

example (hn : n ≠ 0) (hs : n ≤ s.card) :
    ∃ P : Finpartition s, P.IsEquipartition ∧ P.parts.card = n := by
  rw [← pos_iff_ne_zero] at hn
  have : (n - s.card % n) * (s.card / n) + s.card % n * (s.card / n + 1) = s.card := by
    rw [tsub_mul, mul_add, ← add_assoc,
      tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le), mul_one, add_comm,
      mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne', tsub_add_cancel_of_le (mod_lt _ hn).le]