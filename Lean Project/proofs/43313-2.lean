import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Poly
open Linear (Var hugeFuel Context Var.denote)

example (ctx : Context) (p₁ p₂ : Poly) : (p₁.mul p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  induction p₁ generalizing p₂
  case zero =>
    simp [denote, mul]
  case one =>
    simp [denote, mul]
  case add p₁ p₂ ih₁ ih₂ =>
    simp [denote, mul, add_mul, ih₁, ih₂]
  case var x ih =>
    simp [denote, mul, ih]

/- ACTUAL PROOF OF Nat.SOM.Poly.mul_denote -/

example (ctx : Context) (p₁ p₂ : Poly) : (p₁.mul p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mul, go]; simp!
where
  go (p₁ : Poly) (acc : Poly) : (mul.go p₂ p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
    match p₁ with
    | [] => simp!
    | (k, m) :: p₁ =>
      simp! [go p₁, Nat.left_distrib, add_denote, mulMon_denote,
             Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
             Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]