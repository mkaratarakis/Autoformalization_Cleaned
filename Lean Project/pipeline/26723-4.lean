import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

open qrSign
open Nat ZMod
open NumberTheorySymbols
open jacobiSym

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [qrSign, qrSign]
  rw [pow_two, pow_two]
  congr
  rw [mul_comm]

/- ACTUAL PROOF OF qrSign.symm -/

example {m n : ℕ} (hm : Odd m) (hn : Odd n) : qrSign m n = qrSign n m := by
  rw [neg_one_pow hm hn, neg_one_pow hn hm, mul_comm (m / 2)]