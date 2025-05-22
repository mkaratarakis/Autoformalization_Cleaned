import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open IsPrefix
open Nat
variable [BEq α]


example {l l' : List α} (h : l <+: l') (k : Nat) :
    eraseIdx l k <+: eraseIdx l' k := by
  rcases h with ⟨t, rfl⟩
  if hkl : k < length l then
    simp [eraseIdx_append_of_lt_length hkl]
  else
    rw [Nat.not_lt] at hkl
    simp [eraseIdx_append_of_length_le hkl, eraseIdx_of_length_le hkl]