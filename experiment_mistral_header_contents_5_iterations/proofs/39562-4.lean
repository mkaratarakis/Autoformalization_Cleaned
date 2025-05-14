import Mathlib.Algebra.ContinuedFractions.Translations
import Mathlib.Algebra.ContinuedFractions.TerminatedStable

open GenContFract
variable {K : Type*} {g : GenContFract K} {n m : ℕ}
variable [DivisionRing K]

example {s : Stream'.Seq <| Pair K}
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s (n + 1) = convs'Aux s n := by
  induction n with
  | zero =>
    simp only [Stream'.Seq.get?, Stream'.Seq.head, Stream'.Seq.tail, convs'Aux, terminatedAt_n]
    rw [convs'Aux_succ_none (by simpa using terminatedAt_n)]
  | succ n ih =>
    cases h : s.head <;> simp [convs'Aux, h]
    · simp only [convs'Aux_succ_none, convs'Aux]
    · have : s.tail.TerminatedAt n := terminatedAt_n.tail (by simp)
      rw [convs'Aux_succ_some h, ih this]

/- ACTUAL PROOF OF GenContFract.convs'Aux_stable_step_of_terminated -/

example {s : Stream'.Seq <| Pair K}
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s (n + 1) = convs'Aux s n := by
  change s.get? n = none at terminatedAt_n
  induction n generalizing s with
  | zero => simp only [convs'Aux, terminatedAt_n, Stream'.Seq.head]
  | succ n IH =>
    cases s_head_eq : s.head with
    | none => simp only [convs'Aux, s_head_eq]
    | some gp_head =>
      have : s.tail.TerminatedAt n := by
        simp only [Stream'.Seq.TerminatedAt, s.get?_tail, terminatedAt_n]
      have := IH this
      rw [convs'Aux] at this
      simp [this, Nat.add_eq, add_zero, convs'Aux, s_head_eq]