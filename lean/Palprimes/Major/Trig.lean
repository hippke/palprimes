import Mathlib

/-! # Certified bounds for `|sin(π a / D)|` in natural-number arithmetic

Taylor bounds of order 11 (sine) and 10 (cosine) from `Complex.exp_bound`, `π ∈ (3.141592, 3.141593)`,
and fixed-point evaluation with scale `Sc = 10¹²`:
* `sinPiLo a D / Sc ≤ |sin(π a / D)|`, `|sin(π a / D)| ≤ sinPiHi a D / Sc`.
These are the primitives of the kernel-checked certificates in `Palprimes/Major/LemmaL.lean`. -/

set_option linter.style.longLine false

open Real

namespace Palprimes

open Complex in
theorem sin_taylor11 (x : ℝ) (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)| ≤
      |x| ^ 11 * (12 / 439084800) := by
  have hn : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have h := Complex.exp_bound hn (n := 11) (by norm_num)
  have him : (exp ((x : ℂ) * I) - ∑ m ∈ Finset.range 11, ((x : ℂ) * I) ^ m / m.factorial).im =
      Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sub_im, Complex.add_im,
      exp_ofReal_mul_I_im, mul_pow, Nat.factorial]
    simp [pow_succ, Complex.mul_im]
    ring
  calc _ = |(exp ((x : ℂ) * I) - ∑ m ∈ Finset.range 11, ((x : ℂ) * I) ^ m / m.factorial).im| := by
        rw [him]
    _ ≤ _ := Complex.abs_im_le_norm _
    _ ≤ _ := h
    _ = _ := by simp [Nat.factorial]; norm_num

open Complex in
theorem cos_taylor10 (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320)| ≤
      |x| ^ 10 * (11 / 36288000) := by
  have hn : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have h := Complex.exp_bound hn (n := 10) (by norm_num)
  have hre : (exp ((x : ℂ) * I) - ∑ m ∈ Finset.range 10, ((x : ℂ) * I) ^ m / m.factorial).re =
      Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sub_re, Complex.add_re,
      exp_ofReal_mul_I_re, mul_pow, Nat.factorial]
    simp [pow_succ, Complex.mul_re]
    ring
  calc _ = |(exp ((x : ℂ) * I) - ∑ m ∈ Finset.range 10, ((x : ℂ) * I) ^ m / m.factorial).re| := by
        rw [hre]
    _ ≤ _ := Complex.abs_re_le_norm _
    _ ≤ _ := h
    _ = _ := by simp [Nat.factorial]; norm_num

/-! ## Constants -/

def Pl : ℕ := 3141592
def Ph : ℕ := 3141593
def Pd : ℕ := 1000000
def Sc : ℕ := 1000000000000

theorem pi_lo : (Pl : ℝ) / Pd < π := by
  have := Real.pi_gt_d6; norm_num [Pl, Pd]; linarith

theorem pi_hi : π < (Ph : ℝ) / Pd := by
  have := Real.pi_lt_d6; norm_num [Ph, Pd]; linarith

theorem Sc_pos : (0 : ℝ) < Sc := by norm_num [Sc]

/-! ## Rounding helpers -/

theorem floor_tsub_le (a b d : ℕ) (hd : 0 < d) (v : ℝ) (hv0 : 0 ≤ v)
    (hv : ((a : ℝ) - b) / d ≤ v) : ((((a - b) * Sc / d : ℕ) : ℝ)) / Sc ≤ v := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((((a - b) * Sc / d : ℕ) : ℝ)) ≤ (((a - b) * Sc : ℕ) : ℝ) / d := Nat.cast_div_le
  rw [div_le_iff₀ Sc_pos]
  refine le_trans h1 ?_
  rw [div_le_iff₀ hd']
  rcases le_total b a with hab | hab
  · rw [Nat.cast_mul, Nat.cast_sub hab]
    rw [div_le_iff₀ hd'] at hv
    have := Sc_pos
    nlinarith
  · rw [Nat.sub_eq_zero_of_le hab]; simp; have := Sc_pos; positivity

theorem le_ceil_div (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ (((n + (d - 1)) / d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have h1 := Nat.div_add_mod (n + (d - 1)) d
  have h2 := Nat.mod_lt (n + (d - 1)) hd
  have : n ≤ ((n + (d - 1)) / d) * d := by
    have : d * ((n + (d - 1)) / d) = ((n + (d - 1)) / d) * d := mul_comm _ _
    omega
  exact_mod_cast this

theorem le_ceil_tsub (a b d : ℕ) (hd : 0 < d) (v : ℝ)
    (hv : v ≤ ((a : ℝ) - b) / d) : v ≤ ((((a - b) * Sc + (d - 1)) / d : ℕ) : ℝ) / Sc := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := le_ceil_div ((a - b) * Sc) d hd
  rw [le_div_iff₀ Sc_pos]
  refine le_trans ?_ h1
  have h2 : ((a : ℝ) - b) ≤ ((a - b : ℕ) : ℝ) := by
    rcases le_total b a with hab | hab
    · rw [Nat.cast_sub hab]
    · rw [Nat.sub_eq_zero_of_le hab]; simp; exact_mod_cast hab
  rw [Nat.cast_mul, le_div_iff₀ hd']
  rw [le_div_iff₀ hd'] at hv
  have := Sc_pos
  nlinarith

/-! ## Taylor evaluation at `z = A/Q ∈ [0, 1]` -/

def sinPos (A Q : ℕ) : ℕ := A * Q ^ 10 * 439084800 + A ^ 5 * Q ^ 6 * 3659040 + A ^ 9 * Q ^ 2 * 1210
def sinNeg (A Q : ℕ) : ℕ := A ^ 3 * Q ^ 8 * 73180800 + A ^ 7 * Q ^ 4 * 87120
def sinErr (A : ℕ) : ℕ := 12 * A ^ 11
def sinDen (Q : ℕ) : ℕ := Q ^ 11 * 439084800

def cosPos (A Q : ℕ) : ℕ := Q ^ 10 * 36288000 + A ^ 4 * Q ^ 6 * 1512000 + A ^ 8 * Q ^ 2 * 900
def cosNeg (A Q : ℕ) : ℕ := A ^ 2 * Q ^ 8 * 18144000 + A ^ 6 * Q ^ 4 * 50400
def cosErr (A : ℕ) : ℕ := 11 * A ^ 10
def cosDen (Q : ℕ) : ℕ := Q ^ 10 * 36288000

def sinTLo (A Q : ℕ) : ℕ := (sinPos A Q - (sinNeg A Q + sinErr A)) * Sc / sinDen Q
def sinTHi (A Q : ℕ) : ℕ := ((sinPos A Q + sinErr A - sinNeg A Q) * Sc + (sinDen Q - 1)) / sinDen Q
def cosTLo (A Q : ℕ) : ℕ := (cosPos A Q - (cosNeg A Q + cosErr A)) * Sc / cosDen Q
def cosTHi (A Q : ℕ) : ℕ := ((cosPos A Q + cosErr A - cosNeg A Q) * Sc + (cosDen Q - 1)) / cosDen Q

theorem sin_poly_eq (A Q : ℕ) (hQ : 0 < Q) :
    ((sinPos A Q : ℝ) - sinNeg A Q) / sinDen Q =
      (A / Q : ℝ) - (A / Q : ℝ) ^ 3 / 6 + (A / Q : ℝ) ^ 5 / 120 - (A / Q : ℝ) ^ 7 / 5040 + (A / Q : ℝ) ^ 9 / 362880 := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp only [sinPos, sinNeg, sinDen]; push_cast
  field_simp; ring

theorem sin_err_eq (A Q : ℕ) (hQ : 0 < Q) :
    (sinErr A : ℝ) / sinDen Q = (A / Q : ℝ) ^ 11 * (12 / 439084800) := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp only [sinErr, sinDen]; push_cast
  field_simp

theorem cos_poly_eq (A Q : ℕ) (hQ : 0 < Q) :
    ((cosPos A Q : ℝ) - cosNeg A Q) / cosDen Q =
      1 - (A / Q : ℝ) ^ 2 / 2 + (A / Q : ℝ) ^ 4 / 24 - (A / Q : ℝ) ^ 6 / 720 + (A / Q : ℝ) ^ 8 / 40320 := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp only [cosPos, cosNeg, cosDen]; push_cast
  field_simp; ring

theorem cos_err_eq (A Q : ℕ) (hQ : 0 < Q) :
    (cosErr A : ℝ) / cosDen Q = (A / Q : ℝ) ^ 10 * (11 / 36288000) := by
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  simp only [cosErr, cosDen]; push_cast
  field_simp

theorem sinDen_pos (Q : ℕ) (hQ : 0 < Q) : 0 < sinDen Q := by unfold sinDen; positivity
theorem cosDen_pos (Q : ℕ) (hQ : 0 < Q) : 0 < cosDen Q := by unfold cosDen; positivity

theorem sinTLo_le (A Q : ℕ) (hQ : 0 < Q) (hAQ : A ≤ Q) :
    (sinTLo A Q : ℝ) / Sc ≤ Real.sin (A / Q) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hz0 : (0 : ℝ) ≤ A / Q := by positivity
  have hz1 : (A / Q : ℝ) ≤ 1 := by rw [div_le_one hQ']; exact_mod_cast hAQ
  have ht := sin_taylor11 (A / Q) (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [abs_of_nonneg hz0] at ht
  have hsin0 : 0 ≤ Real.sin (A / Q) := Real.sin_nonneg_of_nonneg_of_le_pi hz0 (by linarith [Real.pi_gt_three])
  unfold sinTLo
  apply floor_tsub_le _ _ _ (sinDen_pos Q hQ) _ hsin0
  have hd : (0 : ℝ) < sinDen Q := by exact_mod_cast sinDen_pos Q hQ
  have e1 := sin_poly_eq A Q hQ
  have e2 := sin_err_eq A Q hQ
  have : ((sinPos A Q : ℝ) - ((sinNeg A Q + sinErr A : ℕ) : ℝ)) / sinDen Q =
      ((sinPos A Q : ℝ) - sinNeg A Q) / sinDen Q - (sinErr A : ℝ) / sinDen Q := by
    push_cast; ring
  rw [this, e1, e2]
  linarith [(abs_le.1 ht).1]

theorem le_sinTHi (A Q : ℕ) (hQ : 0 < Q) (hAQ : A ≤ Q) :
    Real.sin (A / Q) ≤ (sinTHi A Q : ℝ) / Sc := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hz0 : (0 : ℝ) ≤ A / Q := by positivity
  have hz1 : (A / Q : ℝ) ≤ 1 := by rw [div_le_one hQ']; exact_mod_cast hAQ
  have ht := sin_taylor11 (A / Q) (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [abs_of_nonneg hz0] at ht
  unfold sinTHi
  apply le_ceil_tsub _ _ _ (sinDen_pos Q hQ)
  have e1 := sin_poly_eq A Q hQ
  have e2 := sin_err_eq A Q hQ
  have : (((sinPos A Q + sinErr A : ℕ) : ℝ) - sinNeg A Q) / sinDen Q =
      ((sinPos A Q : ℝ) - sinNeg A Q) / sinDen Q + (sinErr A : ℝ) / sinDen Q := by
    push_cast; ring
  rw [this, e1, e2]
  linarith [(abs_le.1 ht).2]

theorem cosTLo_le (A Q : ℕ) (hQ : 0 < Q) (hAQ : A ≤ Q) :
    (cosTLo A Q : ℝ) / Sc ≤ Real.cos (A / Q) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hz0 : (0 : ℝ) ≤ A / Q := by positivity
  have hz1 : (A / Q : ℝ) ≤ 1 := by rw [div_le_one hQ']; exact_mod_cast hAQ
  have ht := cos_taylor10 (A / Q) (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [abs_of_nonneg hz0] at ht
  have hcos0 : 0 ≤ Real.cos (A / Q) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  unfold cosTLo
  apply floor_tsub_le _ _ _ (cosDen_pos Q hQ) _ hcos0
  have e1 := cos_poly_eq A Q hQ
  have e2 := cos_err_eq A Q hQ
  have : ((cosPos A Q : ℝ) - ((cosNeg A Q + cosErr A : ℕ) : ℝ)) / cosDen Q =
      ((cosPos A Q : ℝ) - cosNeg A Q) / cosDen Q - (cosErr A : ℝ) / cosDen Q := by
    push_cast; ring
  rw [this, e1, e2]
  linarith [(abs_le.1 ht).1]

theorem le_cosTHi (A Q : ℕ) (hQ : 0 < Q) (hAQ : A ≤ Q) :
    Real.cos (A / Q) ≤ (cosTHi A Q : ℝ) / Sc := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hz0 : (0 : ℝ) ≤ A / Q := by positivity
  have hz1 : (A / Q : ℝ) ≤ 1 := by rw [div_le_one hQ']; exact_mod_cast hAQ
  have ht := cos_taylor10 (A / Q) (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [abs_of_nonneg hz0] at ht
  unfold cosTHi
  apply le_ceil_tsub _ _ _ (cosDen_pos Q hQ)
  have e1 := cos_poly_eq A Q hQ
  have e2 := cos_err_eq A Q hQ
  have : (((cosPos A Q + cosErr A : ℕ) : ℝ) - cosNeg A Q) / cosDen Q =
      ((cosPos A Q : ℝ) - cosNeg A Q) / cosDen Q + (cosErr A : ℝ) / cosDen Q := by
    push_cast; ring
  rw [this, e1, e2]
  linarith [(abs_le.1 ht).2]

/-! ## `|sin(π a/D)|` -/

/-- Reduced numerator: `|sin(π a/D)| = sin(π s/D)` with `2s ≤ D`. -/
def redS (a D : ℕ) : ℕ := min (a % D) (D - a % D)

def sinPiLoS (s D : ℕ) : ℕ :=
  if 4 * s ≤ D then sinTLo (Pl * s) (Pd * D) else cosTLo (Ph * (D - 2 * s)) (2 * Pd * D)

def sinPiHiS (s D : ℕ) : ℕ :=
  if 4 * s ≤ D then sinTHi (Ph * s) (Pd * D) else cosTHi (Pl * (D - 2 * s)) (2 * Pd * D)

def sinPiLo (a D : ℕ) : ℕ := sinPiLoS (redS a D) D
def sinPiHi (a D : ℕ) : ℕ := sinPiHiS (redS a D) D

theorem redS_le (a D : ℕ) : 2 * redS a D ≤ D := by
  unfold redS
  have := Nat.mod_le a D
  rcases le_total (a % D) (D - a % D) with h | h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right h]; omega

theorem abs_sin_redS (a D : ℕ) (hD : 0 < D) :
    |Real.sin (π * a / D)| = Real.sin (π * (redS a D) / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr : a % D < D := Nat.mod_lt a hD
  have e : π * (a : ℝ) / D = π * ((a % D : ℕ) : ℝ) / D + ((a / D : ℕ) : ℝ) * π := by
    have := Nat.div_add_mod a D
    have h2 : (a : ℝ) = D * ((a / D : ℕ) : ℝ) + ((a % D : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [h2]; field_simp; ring
  rw [e, Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hs0 : ∀ s : ℕ, 2 * s ≤ D → 0 ≤ Real.sin (π * s / D) := by
    intro s hs
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    rw [div_le_iff₀ hD']
    have : (s : ℝ) ≤ D := by exact_mod_cast (by omega : s ≤ D)
    nlinarith [Real.pi_pos]
  unfold redS
  rcases le_total (a % D) (D - a % D) with h | h
  · rw [min_eq_left h, abs_of_nonneg (hs0 _ (by omega))]
  · rw [min_eq_right h]
    have e2 : π * ((D - a % D : ℕ) : ℝ) / D = π - π * ((a % D : ℕ) : ℝ) / D := by
      rw [Nat.cast_sub hr.le]; field_simp
    rw [e2, Real.sin_pi_sub]
    rw [abs_of_nonneg]
    have := hs0 (D - a % D) (by omega)
    rwa [e2, Real.sin_pi_sub] at this

/-- `sin(π s/D) = cos(π (D − 2s)/(2D))`. -/
theorem sin_eq_cos_red (s D : ℕ) (hD : 0 < D) (hs : 2 * s ≤ D) :
    Real.sin (π * s / D) = Real.cos (π * ((D - 2 * s : ℕ) : ℝ) / (2 * D)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  rw [Nat.cast_sub hs]; push_cast; field_simp

theorem sinPiLoS_le (s D : ℕ) (hD : 0 < D) (hs : 2 * s ≤ D) :
    (sinPiLoS s D : ℝ) / Sc ≤ Real.sin (π * s / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hPl := pi_lo
  have hPh := pi_hi
  have hPd : (0 : ℝ) < Pd := by norm_num [Pd]
  unfold sinPiLoS
  split_ifs with h4
  · have hA : Pl * s ≤ Pd * D := by simp only [Pl, Pd]; omega
    refine le_trans (sinTLo_le _ _ (by simp [Pd]; omega) hA) ?_
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : (0 : ℝ) ≤ ((Pl * s : ℕ) : ℝ) / ((Pd * D : ℕ) : ℝ) := by positivity
      linarith [Real.pi_pos]
    · rw [div_le_iff₀ hD']
      have : (4 * s : ℝ) ≤ D := by exact_mod_cast h4
      nlinarith [Real.pi_pos]
    · push_cast
      rw [div_le_div_iff₀ (by positivity) hD']
      have : (Pl : ℝ) ≤ π * Pd := by rw [div_lt_iff₀ hPd] at hPl; linarith
      have hs0 : (0 : ℝ) ≤ s := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs0 hD'.le)]
  · have hle : D - 2 * s ≤ D := Nat.sub_le _ _
    have hA : Ph * (D - 2 * s) ≤ 2 * Pd * D := by simp only [Ph, Pd]; omega
    rw [sin_eq_cos_red s D hD hs]
    refine le_trans (cosTLo_le _ _ (by simp [Pd]; omega) hA) ?_
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have : (((Ph * (D - 2 * s) : ℕ) : ℝ) / ((2 * Pd * D : ℕ) : ℝ)) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.2 (by simp [Pd]; omega))]; exact_mod_cast hA
      linarith [Real.pi_gt_three]
    · push_cast
      rw [div_le_div_iff₀ (by positivity) (by have := hPd; positivity)]
      have : π * Pd ≤ (Ph : ℝ) := by rw [lt_div_iff₀ hPd] at hPh; linarith
      have hs0 : (0 : ℝ) ≤ ((D - 2 * s : ℕ) : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs0 hD'.le)]

theorem le_sinPiHiS (s D : ℕ) (hD : 0 < D) (hs : 2 * s ≤ D) :
    Real.sin (π * s / D) ≤ (sinPiHiS s D : ℝ) / Sc := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hPl := pi_lo
  have hPh := pi_hi
  have hPd : (0 : ℝ) < Pd := by norm_num [Pd]
  unfold sinPiHiS
  split_ifs with h4
  · have hA : Ph * s ≤ Pd * D := by simp only [Ph, Pd]; omega
    refine le_trans ?_ (le_sinTHi _ _ (by simp [Pd]; omega) hA)
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : (0 : ℝ) ≤ π * s / D := by positivity
      linarith [Real.pi_pos]
    · have : (((Ph * s : ℕ) : ℝ) / ((Pd * D : ℕ) : ℝ)) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.2 (by simp [Pd]; omega))]; exact_mod_cast hA
      linarith [Real.pi_gt_three]
    · push_cast
      rw [div_le_div_iff₀ hD' (by positivity)]
      have : π * Pd ≤ (Ph : ℝ) := by rw [lt_div_iff₀ hPd] at hPh; linarith
      have hs0 : (0 : ℝ) ≤ s := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs0 hD'.le)]
  · have hle : D - 2 * s ≤ D := Nat.sub_le _ _
    have hA : Pl * (D - 2 * s) ≤ 2 * Pd * D := by simp only [Pl, Pd]; omega
    rw [sin_eq_cos_red s D hD hs]
    refine le_trans ?_ (le_cosTHi _ _ (by simp [Pd]; omega) hA)
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have h4' : ((D - 2 * s : ℕ) : ℝ) * 2 ≤ D := by
        have : (D - 2 * s) * 2 ≤ D := by omega
        exact_mod_cast this
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    · push_cast
      rw [div_le_div_iff₀ (by positivity) (by have := hPd; positivity)]
      have : (Pl : ℝ) ≤ π * Pd := by rw [div_lt_iff₀ hPd] at hPl; linarith
      have hs0 : (0 : ℝ) ≤ ((D - 2 * s : ℕ) : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs0 hD'.le)]

theorem sinPiLo_le (a D : ℕ) (hD : 0 < D) :
    (sinPiLo a D : ℝ) / Sc ≤ |Real.sin (π * a / D)| := by
  rw [abs_sin_redS a D hD]; exact sinPiLoS_le _ _ hD (redS_le a D)

theorem le_sinPiHi (a D : ℕ) (hD : 0 < D) :
    |Real.sin (π * a / D)| ≤ (sinPiHi a D : ℝ) / Sc := by
  rw [abs_sin_redS a D hD]; exact le_sinPiHiS _ _ hD (redS_le a D)

end Palprimes
