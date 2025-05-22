import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction l generalizing n l'
  · simp
  · cases l'
    · simp
    · cases n
      · simp
      · simp [drop, zipWith, Nat.succ_eq_add_one]
        rw [ih]
        simp

def drop : Nat → List α → List α
  | 0, xs => xs
  | n + 1, [] => []
  | n + 1, x :: xs => drop n xs

def zipWith : (α → β → γ) → List α → List β → List γ
  | f, [], ys => []
  | f, xs, [] => []
  | f, x :: xs, y :: ys => f x y :: zipWith f xs ys

inductive List (α : Type u)
  | nil : List α
  | cons : α → List α → List α

inductive Nat
  | zero : Nat
  | succ : Nat → Nat

def Nat.add : Nat → Nat → Nat
  | zero, n => n
  | succ m, n => succ (add m n)

def List.drop : Nat → List α → List α
  | 0, xs => xs
  | n + 1, [] => []
  | n + 1, x :: xs => drop n xs

def List.zipWith : (α → β → γ) → List α → List β → List γ
  | f, [], ys => []
  | f, xs, [] => []
  | f, x :: xs, y :: ys => f x y :: zipWith f xs ys

/- ACTUAL PROOF OF List.drop_zipWith -/

example : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction l generalizing l' n with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · cases n
        · simp
        · simp [hl]