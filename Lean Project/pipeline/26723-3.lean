import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open qrSign
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [qrSign, qrSign]
  simp only [pow_two, Nat.div_mul_cancel]
  congr
  rw [Nat.mul_div_cancel_left _ (by exact two_ne_zero)]
  rw [Nat.mul_div_cancel_left _ (by exact two_ne_zero)]
  exact (mul_comm _ _).symm

/- ACTUAL PROOF OF qrSign.symm -/

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]