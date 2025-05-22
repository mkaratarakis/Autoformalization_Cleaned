import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example : ∀(b b' : Bool), BitVec.ofBool b = BitVec.ofBool b' ↔ b = b' := by
  intros b b'
  constructor
  · intro h
    cases b <;> cases b' <;> simp [ofBool] at h
    all_goals {
      try {exact h}
      try {exact (Bool.noConfusion h)}
      try {exact rfl}
    }
  · intro h
    simp [h, ofBool]

/- ACTUAL PROOF OF BitVec.ofBool_eq_iff_eq -/

example : ∀(b b' : Bool), BitVec.ofBool b = BitVec.ofBool b' ↔ b = b' := by
  decide