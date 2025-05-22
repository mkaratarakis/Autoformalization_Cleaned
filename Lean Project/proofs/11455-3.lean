import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let m' := gcd k m
  let n' := gcd k n
  let g := gcd k (m * n)
  have h1 : g ∣ k := gcd_dvd_left k (m * n)
  have h2 : g ∣ m * n := gcd_dvd_right k (m * n)
  have h3 : m' ∣ k := gcd_dvd_left k m
  have h4 : m' ∣ m := gcd_dvd_right k m
  have h5 : n' ∣ k := gcd_dvd_left k n
  have h6 : n' ∣ n := gcd_dvd_right k n
  have h7 : g ∣ m' * n' := by
    apply dvd_mul_of_dvd_of_dvd
    · exact h1
    · apply dvd_mul
      · exact h3
      · exact h5
  exact dvd_mul_right (dvd_mul_left dvd_refl h4) h6

/- ACTUAL PROOF OF Nat.gcd_mul_dvd_mul_gcd -/

example (k m n : Nat) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  let ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, (h : gcd k (m * n) = m' * n')⟩ :=
    prod_dvd_and_dvd_of_dvd_prod <| gcd_dvd_right k (m * n)
  rw [h]
  have h' : m' * n' ∣ k := h ▸ gcd_dvd_left ..
  exact Nat.mul_dvd_mul
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_right m' n') h') hm')
    (dvd_gcd (Nat.dvd_trans (Nat.dvd_mul_left n' m') h') hn')