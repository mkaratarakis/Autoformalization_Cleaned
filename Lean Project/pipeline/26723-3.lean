import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open qrSign
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [qrSign, qrSign]
  simp only [Nat.div_mul_cancel, Nat.odd_iff] at hm hn
  rw [← pow_mul]
  congr
  rw [Nat.mul_comm]
  norm_cast

/- ACTUAL PROOF OF qrSign.symm -/

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]