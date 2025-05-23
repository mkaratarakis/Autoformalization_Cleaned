import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b < c) : b < c - a := by
  apply Int.add_neg_lt_of_lt_add h


+++++ test_cases/Lean4/T100_valid.lean
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b < c) : b < c - a := by
  apply Int.add_neg_lt_of_lt_add h


+++++ test_cases/Lean4/T034_valid.lean
import Lean.Data.Nat
import Lean.Data.Nat.GCD
import Lean.Data.Nat.GCD.Basic

open Nat

lemma gcd_aux_eq_gcd :
  ∀ (a b : Nat), gcd_aux a b = gcd a b
| a, b := by
  rw [gcd_aux, gcd_eq_gcd_aux]


+++++ test_cases/Lean4/T024_valid.lean
import Lean.Data.Nat
import Lean.Data.Nat.GCD
import Lean.Data.Nat.GCD.Basic

open Nat

lemma gcd_aux_eq_gcd :
  ∀ (a b : Nat), gcd_aux a b = gcd a b
| a, b := by
  induction b generalizing a <;> simp [gcd_aux, gcd_eq_gcd_aux, *]


+++++ test_cases/Lean4/T100_invalid.lean
import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a + b < c) : b < c - a := by
  have : a + b + (-a) < c + (-a) := by
    apply Int.add_lt_add_left h (-a)
  have : b + a + (-a) < c + (-a) := by
    rw [Int.add_assoc] at this
    exact this
  have : b < c + (-a) := by
    rw [Int.add_neg_cancel_right] at this
    exact this
  exact this


+++++ test_cases/Lean4/T032_valid.lean
import Lean.Data.Nat
import Lean.Data.Nat.GCD
import Lean.Data.Nat.GCD.Basic

open Nat

lemma gcd_aux_eq_gcd :
  ∀ (a b : Nat), gcd_aux a b = gcd a b
| a, b := by
  rw [gcd_aux]; rw [gcd_eq_gcd_aux]

/- ACTUAL PROOF OF Int.lt_sub_left_of_add_lt -/

example {a b c : Int} (h : a + b < c) : b < c - a := by
  have h := Int.add_lt_add_right h (-a)
  rwa [Int.add_comm a b, Int.add_neg_cancel_right] at h