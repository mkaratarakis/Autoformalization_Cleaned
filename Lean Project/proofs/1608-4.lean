import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : m ∈ (range' 1 n).reverse ↔ 1 ≤ m ∧ m ≤ n := by
  rw [mem_reverse]
  simp
  split
  · rintro ⟨_, hmn, rfl⟩
    exact ⟨Nat.succ_le_of_lt hmn, hmn.le⟩
  · rintro ⟨h1, h2⟩
    use  m - 1
    simp
    exact ⟨Nat.sub_pos_of_lt (Nat.lt_of_le_of_lt h1 h2), by rw [Nat.sub_add_cancel h2]⟩

/- ACTUAL PROOF OF List.mem_iota -/

example {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]