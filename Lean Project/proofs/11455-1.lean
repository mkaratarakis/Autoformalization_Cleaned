import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let m' := gcd k m
  let n' := gcd k n
  let g := gcd k (m * n)
  have h1 : g ∣ k := dvd_gcd 1 k (m * n)
  have h2 : g ∣ m * n := dvd_gcd k (m * n)
  have h3 : m' ∣ k := dvd_gcd 1 k m
  have h4 : m' ∣ m := dvd_gcd k m
  have h5 : n' ∣ k := dvd_gcd 1 k n
  have h6 : n' ∣ n := dvd_gcd k n
  have h7 : g ∣ m' * n' := by
    apply dvd_mul
    · apply dvd_mul_of_dvd_left h1 h4
    · apply dvd_mul_of_dvd_right h1 h6
  exact dvd_trans h7 (dvd_mul_right (dvd_mul_left dvd_refl h5) h3)

/- ACTUAL PROOF OF Nat.gcd_mul_dvd_mul_gcd -/

example (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, (h : gcd k (m * n) = m' * n')⟩ :=
    prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n)
  rw [h]
  have h' : m' * n' ∣ k := h ▸ gcd_dvd_left ..
  exact Nat.mul_dvd_mul
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_right m' n') h') hm')
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_left n' m') h') hn')