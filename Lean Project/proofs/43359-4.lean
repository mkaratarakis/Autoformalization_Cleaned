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
    rw [←ih_a, ←ih_b]
    exact Poly.denote_mul ctx (Poly.denote ctx a.toPoly) (Poly.denote ctx b.toPoly)
  case num i =>
    show Poly.denote ctx (num i).toPoly = Expr.denote ctx (num i)
    rfl
  case var v =>
    show Poly.denote ctx (var v).toPoly = Expr.denote ctx (var v)
    rfl
  case add a b ih_a ih_b =>
    show Poly.denote ctx (a.add b).toPoly = Expr.denote ctx (a.add b)
    rw [←ih_a, ←ih_b]
    exact Poly.denote_add ctx (Poly.denote ctx a.toPoly) (Poly.denote ctx b.toPoly)

/- ACTUAL PROOF OF Nat.SOM.Expr.toPoly_denote -/

example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    simp [eq_of_beq h]
  | var v => simp!
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]