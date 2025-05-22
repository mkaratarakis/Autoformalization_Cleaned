import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @take = @takeTR := by
  funext α n l; simp [takeTR]
  suffices ∀ xs acc, l = acc.data ++ xs → takeTR.go l xs n acc = acc.data ++ xs.take n from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing n with intro acc
  | nil => cases n <;> simp [take, takeTR.go]
  | cons x xs IH =>
    cases n with simp only [take, takeTR.go]
    | zero => simp
    | succ n => intro h; rw [IH] <;> simp_all