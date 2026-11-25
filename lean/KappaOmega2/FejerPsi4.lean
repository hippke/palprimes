import Mathlib

/-!
# ψ₄ ≥ 1 for the Fejér-weighted family (PROOF_K2 §6b), polynomial part

With E the fourth-moment integral, 315 M⁷ (1 − b E) = (M − 1) P₆(M) for odd b = 2M − 1 and
630 M³ (M + 1)³ (1 − b E) = 2 M P₅(M) for even b = 2M. Here the closed forms of E are taken as given
(exact counts, PROOF_K2 §6b); this file proves the identities between the closed forms and the factored
right sides, and the positivity of P₆, P₅ for M ≥ 2.
-/

namespace KappaOmega2

theorem fejer_odd_identity (M : ℚ) (hM : M ≠ 0) :
    315 * M ^ 7 * (1 - (2 * M - 1) * ((151 * M ^ 6 + 70 * M ^ 4 + 49 * M ^ 2 + 45) / (315 * M ^ 7)))
      = (M - 1) * (13 * M ^ 6 + 164 * M ^ 5 + 24 * M ^ 4 + 94 * M ^ 3 - 4 * M ^ 2 + 45 * M - 45) := by
  field_simp
  ring

theorem fejer_even_identity (M : ℚ) (hM : M ≠ 0) (hM1 : M + 1 ≠ 0) :
    630 * M ^ 3 * (M + 1) ^ 3 * (1 - (2 * M) * ((2 * M + 1) * (151 * M ^ 4 + 302 * M ^ 3 + 161 * M ^ 2 + 10 * M + 6)
      / (630 * M ^ 3 * (M + 1) ^ 3)))
      = 2 * M * (13 * M ^ 5 + 190 * M ^ 4 + 321 * M ^ 3 + 134 * M ^ 2 - 22 * M - 6) := by
  field_simp
  ring

theorem P6_pos (M : ℚ) (hM : 2 ≤ M) :
    0 < 13 * M ^ 6 + 164 * M ^ 5 + 24 * M ^ 4 + 94 * M ^ 3 - 4 * M ^ 2 + 45 * M - 45 := by
  have h1 : 4 * M ^ 2 ≤ 94 * M ^ 3 := by nlinarith [sq_nonneg M]
  have h2 : 0 < 13 * M ^ 6 + 164 * M ^ 5 + 24 * M ^ 4 := by positivity
  nlinarith

theorem P5_pos (M : ℚ) (hM : 2 ≤ M) :
    0 < 13 * M ^ 5 + 190 * M ^ 4 + 321 * M ^ 3 + 134 * M ^ 2 - 22 * M - 6 := by
  have h1 : 22 * M + 6 ≤ 134 * M ^ 2 := by nlinarith
  have h2 : 0 < 13 * M ^ 5 + 190 * M ^ 4 + 321 * M ^ 3 := by positivity
  nlinarith

/-- ψ₄ ≥ 1, i.e. b E ≤ 1, for odd b = 2M − 1, M ≥ 2, given the closed form of E. -/
theorem psi4_odd (M : ℚ) (hM : 2 ≤ M) :
    (2 * M - 1) * ((151 * M ^ 6 + 70 * M ^ 4 + 49 * M ^ 2 + 45) / (315 * M ^ 7)) < 1 := by
  have hM0 : M ≠ 0 := by linarith
  have hid := fejer_odd_identity M hM0
  have hpos : 0 < (M - 1) * (13 * M ^ 6 + 164 * M ^ 5 + 24 * M ^ 4 + 94 * M ^ 3 - 4 * M ^ 2 + 45 * M - 45) :=
    mul_pos (by linarith) (P6_pos M hM)
  have hden : 0 < 315 * M ^ 7 := by positivity
  rw [← hid] at hpos
  have := (mul_pos_iff_of_pos_left hden).mp hpos
  linarith

/-- ψ₄ ≥ 1 for even b = 2M, M ≥ 2, given the closed form of E. -/
theorem psi4_even (M : ℚ) (hM : 2 ≤ M) :
    (2 * M) * ((2 * M + 1) * (151 * M ^ 4 + 302 * M ^ 3 + 161 * M ^ 2 + 10 * M + 6)
      / (630 * M ^ 3 * (M + 1) ^ 3)) < 1 := by
  have hM0 : M ≠ 0 := by linarith
  have hM1 : M + 1 ≠ 0 := by linarith
  have hid := fejer_even_identity M hM0 hM1
  have hpos : 0 < 2 * M * (13 * M ^ 5 + 190 * M ^ 4 + 321 * M ^ 3 + 134 * M ^ 2 - 22 * M - 6) :=
    mul_pos (by linarith) (P5_pos M hM)
  have hden : 0 < 630 * M ^ 3 * (M + 1) ^ 3 := by positivity
  rw [← hid] at hpos
  have := (mul_pos_iff_of_pos_left hden).mp hpos
  linarith

end KappaOmega2
