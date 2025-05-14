import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesHasSum
open LSeries

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  have h : LSeriesHasSum (fun n => 0) s 0 := by
    simp
  rw [← LSeriesHasSum.add h hf]
  exact LSeriesHasSum.neg hf

/- ACTUAL PROOF OF LSeriesHasSum.neg -/

example {f : ℕ → ℂ} {s a : ℂ} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa only [LSeriesHasSum, term_neg] using HasSum.neg hf