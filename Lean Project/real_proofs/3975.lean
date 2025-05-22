import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat



example {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h