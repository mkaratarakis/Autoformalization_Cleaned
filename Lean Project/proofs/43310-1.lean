import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Poly
open Linear (Var hugeFuel Context Var.denote)

example (ctx : Context) (p : Poly) (k : Nat) (m : Mon) : (p.mulMon k m).denote ctx = p.denote ctx * k * m.denote ctx := by
  -- Apply the definition of `mulMon`
  unfold mulMon
  -- Simplify the goal using the definition of `denote`
  simp [denote]
  -- Apply the definition of `go`
  unfold go
  -- Simplify the goal using the properties of polynomial and monomial evaluation
  simp [*]
  -- The goal should now be trivial
  rfl

/- ACTUAL PROOF OF Nat.SOM.Poly.mulMon_denote -/

example (ctx : Context) (p : Poly) (k : Nat) (m : Mon) : (p.mulMon k m).denote ctx = p.denote ctx * k * m.denote ctx := by
  simp [mulMon, go]; simp!
where
  go (p : Poly) (acc : Poly) : (mulMon.go k m p acc).denote ctx = acc.denote ctx + p.denote ctx * k * m.denote ctx := by
   match p with
   | [] => simp!
   | (k', m') :: p =>
     simp! [go p, Nat.left_distrib, denote_insertSorted, Mon.mul_denote, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]