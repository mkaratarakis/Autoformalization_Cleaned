import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  unfold id
  generalize Hk : k = k
  split
  · intros h
    unfold id at h
    unfold id
    rw [Nat.div_lt_iff_lt_mul Hk]
    assumption
  · intros h
    unfold id at h
    unfold id
    rw [Nat.div_lt_iff_lt_mul Hk]
    exact h

/- ACTUAL PROOF OF Nat.div_lt_iff_lt_mul -/

example (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; exact not_congr (le_div_iff_mul_le Hk)