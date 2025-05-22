import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Expr
open Linear (Var hugeFuel Context Var.denote)

example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e using Expr.recOn
  case mul a b ih_a ih_b =>
    show Poly.denote ctx (a.mul b).toPoly = Expr.denote ctx (a.mul b)
    rw [Expr.toPoly_mul]
    rw [Poly.denote_mul]
    exact mul_eq_mul ih_a ih_b
  case num i =>
    show Poly.denote ctx (num i).toPoly = Expr.denote ctx (num i)
    rw [Expr.toPoly_num]
    rw [Poly.denote_num]
  case var v =>
    show Poly.denote ctx (var v).toPoly = Expr.denote ctx (var v)
    rw [Expr.toPoly_var]
    rw [Poly.denote_var]
  case add a b ih_a ih_b =>
    show Poly.denote ctx (a.add b).toPoly = Expr.denote ctx (a.add b)
    rw [Expr.toPoly_add]
    rw [Poly.denote_add]
    exact add_eq_add ih_a ih_b

/- ACTUAL PROOF OF Nat.SOM.Expr.toPoly_denote -/

example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    simp [eq_of_beq h]
  | var v => simp!
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]