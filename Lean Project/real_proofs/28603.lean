import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

open LSeriesSummable
open LSeries


example {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa only [LSeriesSummable, term_neg] using Summable.neg hf