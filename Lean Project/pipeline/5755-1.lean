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
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have h₁ : 0 < n := hn0
  obtain ⟨a, b, m, h₁, rfl⟩ := exists_a_b_m_eq_s_card_of_le hs
  obtain ⟨Q, hQ⟩ := equitabilise_aux h₁
  exists Q
  constructor
  · exact fun p hp ↦ Or.inl (hQ.1 p hp)
  · have h₂ : Q.parts.card = a + b := by
      rw [← Nat.add_sub_of_le (Nat.le_add_right a b)]
      exact hQ.2.2
    rw [h₂]
    calc
      a + b = n - s.card % n + s.card % n := by rw [Nat.add_sub_cancel']
      _ = n := by rw [Nat.sub_add_cancel (Nat.le_of_lt_succ h₁)]

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