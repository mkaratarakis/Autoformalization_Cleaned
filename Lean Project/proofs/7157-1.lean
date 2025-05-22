import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @zipWith = @zipWithTR := by
  funext α β γ f as bs
  induction as generalizing bs
  · simp [zipWith, zipWithTR]
  · simp [zipWith, zipWithTR, zipWithTR.go]
    cases bs with b bs
    · simp [zipWith, zipWithTR]
    · simp [zipWith, zipWithTR, zipWithTR.go]
      have := ih bs
      simp [Array.data, Array.push, zipWith, zipWithTR, zipWithTR.go] at this
      exact this

/- ACTUAL PROOF OF List.zipWith_eq_zipWithTR -/

example : @zipWith = @zipWithTR := by
  funext α β γ f as bs
  let rec go : ∀ as bs acc, zipWithTR.go f as bs acc = acc.data ++ as.zipWith f bs
    | [], _, acc | _::_, [], acc => by simp [zipWithTR.go, zipWith]
    | a::as, b::bs, acc => by simp [zipWithTR.go, zipWith, go as bs]
  exact (go as bs #[]).symm