import Palprimes.Major2D.Sound
import Palprimes.Major2D.TabR

/-! # Soundness of the table entries: `tabOK M tab M = true → TabGood M tab` -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real Complex

namespace Palprimes.M2

/-! ## The Taylor sums -/

theorem fct_eq (n : ℕ) : fct n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fct, Nat.factorial, ih]

/-- the `k`-th integer term `a^k b^(n−1−k) (n−1)!/k!`. -/
def tayC (a b n k : ℕ) : ℕ := a ^ k * b ^ (n - 1 - k) * (fct (n - 1) / fct k)

theorem tayC_real (a b n k : ℕ) (hb : 0 < b) (hk : k ≤ n - 1) :
    (tayC a b n k : ℝ) = (b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) * (((a : ℝ) / b) ^ k / (Nat.factorial k : ℝ)) := by
  unfold tayC
  rw [fct_eq, fct_eq]
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdvd := Nat.factorial_dvd_factorial hk
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div hdvd (by exact_mod_cast (Nat.factorial_pos k).ne'), Nat.cast_pow, Nat.cast_pow]
  have hfk : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have : (b : ℝ) ^ (n - 1) = (b : ℝ) ^ (n - 1 - k) * (b : ℝ) ^ k := by rw [← pow_add]; congr 1; omega
  rw [this, div_pow]
  field_simp

theorem re_Ipow (x : ℝ) (k : ℕ) :
    ((I * (x : ℂ)) ^ k).re = if k % 4 = 0 then x ^ k else if k % 4 = 2 then -x ^ k else 0 := by
  rw [mul_pow, ← Complex.ofReal_pow]
  have h4 : I ^ k = I ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [h4]
  generalize x ^ k = y
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> simp [pow_succ, Complex.I_mul_I]

theorem im_Ipow (x : ℝ) (k : ℕ) :
    ((I * (x : ℂ)) ^ k).im = if k % 4 = 1 then x ^ k else if k % 4 = 3 then -x ^ k else 0 := by
  rw [mul_pow, ← Complex.ofReal_pow]
  have h4 : I ^ k = I ^ (k % 4) := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [h4]
  generalize x ^ k = y
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 4) <;> simp [pow_succ, Complex.I_mul_I]

theorem tayRe_eq (a b n : ℕ) (hb : 0 < b) : ∀ m ≤ n,
    (tayRe a b n m : ℝ) = (b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) *
      (∑ k ∈ Finset.range m, (I * (((a : ℝ) / b : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)).re := by
  intro m hm
  induction m with
  | zero => simp [tayRe]
  | succ m ih =>
    rw [tayRe, Finset.sum_range_succ, Complex.add_re, mul_add, ← ih (by omega)]
    have hdiv : ((I * (((a : ℝ) / b : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)).re =
        ((I * (((a : ℝ) / b : ℝ) : ℂ)) ^ m).re / (Nat.factorial m : ℝ) := by
      rw [show (Nat.factorial m : ℂ) = ((Nat.factorial m : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
    rw [hdiv, re_Ipow]
    have hC := tayC_real a b n m hb (by omega)
    unfold tayC at hC
    rw [Int.cast_add]
    split_ifs with h1 h2
    · rw [Int.cast_natCast, hC]
    · rw [Int.cast_neg, Int.cast_natCast, hC]; ring
    · simp

theorem tayIm_eq (a b n : ℕ) (hb : 0 < b) : ∀ m ≤ n,
    (tayIm a b n m : ℝ) = (b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) *
      (∑ k ∈ Finset.range m, (I * (((a : ℝ) / b : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)).im := by
  intro m hm
  induction m with
  | zero => simp [tayIm]
  | succ m ih =>
    rw [tayIm, Finset.sum_range_succ, Complex.add_im, mul_add, ← ih (by omega)]
    have hdiv : ((I * (((a : ℝ) / b : ℝ) : ℂ)) ^ m / (Nat.factorial m : ℂ)).im =
        ((I * (((a : ℝ) / b : ℝ) : ℂ)) ^ m).im / (Nat.factorial m : ℝ) := by
      rw [show (Nat.factorial m : ℂ) = ((Nat.factorial m : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_im]
    rw [hdiv, im_Ipow]
    have hC := tayC_real a b n m hb (by omega)
    unfold tayC at hC
    rw [Int.cast_add]
    split_ifs with h1 h2
    · rw [Int.cast_natCast, hC]
    · rw [Int.cast_neg, Int.cast_natCast, hC]; ring
    · simp

/-- `|cos x − re/den|, |sin x − im/den| ≤ |x|^n/n!`. -/
theorem tay_bound (a b n : ℕ) (hb : 0 < b) (hn : 0 < n) :
    |Real.cos ((a : ℝ) / b) - (tayRe a b n n : ℝ) / ((b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ))| ≤ |(a : ℝ) / b| ^ n / n.factorial ∧
    |Real.sin ((a : ℝ) / b) - (tayIm a b n n : ℝ) / ((b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ))| ≤ |(a : ℝ) / b| ^ n / n.factorial := by
  have hden : (0 : ℝ) < (b : ℝ) ^ (n - 1) * (Nat.factorial (n - 1) : ℝ) := by
    have : (0 : ℝ) < b := by exact_mod_cast hb
    have : (0 : ℝ) < Nat.factorial (n - 1) := by exact_mod_cast Nat.factorial_pos _
    positivity
  rw [tayRe_eq a b n hb n le_rfl, tayIm_eq a b n hb n le_rfl, mul_div_cancel_left₀ _ hden.ne',
    mul_div_cancel_left₀ _ hden.ne']
  have h := exp_I_taylor n ((a : ℝ) / b)
  unfold expRem at h
  constructor
  · have := (Complex.abs_re_le_norm _).trans h
    rw [Complex.sub_re, show cexp (I * (((a : ℝ) / b : ℝ) : ℂ)) = cexp ((((a : ℝ) / b : ℝ) : ℂ) * I) by ring_nf,
      Complex.exp_ofReal_mul_I_re] at this
    exact this
  · have := (Complex.abs_im_le_norm _).trans h
    rw [Complex.sub_im, show cexp (I * (((a : ℝ) / b : ℝ) : ℂ)) = cexp ((((a : ℝ) / b : ℝ) : ℂ) * I) by ring_nf,
      Complex.exp_ofReal_mul_I_im] at this
    exact this


/-! ## Rounding -/

theorem roundE_spec (v : ℤ) (den : ℕ) (hden : 0 < den) (c δ : ℝ) (hc : |c| ≤ 1) (hδ : 0 ≤ δ)
    (hv : |(v : ℝ) / den - c| ≤ δ) : |(roundE v den : ℝ) / 2 ^ 62 - 1 - c| ≤ δ + 1 / 2 ^ 62 := by
  unfold roundE
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have hdz : (0 : ℤ) < den := by exact_mod_cast hden
  set F : ℤ := ((v + den) * two62) / (den : ℤ) with hF
  have hF1 : F * den ≤ (v + den) * two62 := Int.ediv_mul_le _ hdz.ne'
  have hF2 : (v + den) * two62 < (F + 1) * den := Int.lt_ediv_add_one_mul_self _ hdz
  have hF1r : (F : ℝ) * den ≤ ((v : ℝ) + den) * 2 ^ 62 := by
    have := (Int.cast_le (R := ℝ)).2 hF1; push_cast at this; unfold two62 at this; norm_num at this ⊢; linarith
  have hF2r : ((v : ℝ) + den) * 2 ^ 62 < ((F : ℝ) + 1) * den := by
    have := (Int.cast_lt (R := ℝ)).2 hF2; push_cast at this; unfold two62 at this; norm_num at this ⊢; linarith
  -- w = (v/den + 1) 2^62, t = (c + 1) 2^62
  set w : ℝ := ((v : ℝ) / den + 1) * 2 ^ 62
  set t : ℝ := (c + 1) * 2 ^ 62
  have hw1 : (F : ℝ) ≤ w := by
    simp only [w]; rw [div_add_one hd.ne', div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
  have hw2 : w < F + 1 := by
    simp only [w]; rw [div_add_one hd.ne', div_mul_eq_mul_div, div_lt_iff₀ hd]; linarith
  have hwt : |w - t| ≤ δ * 2 ^ 62 := by
    have : w - t = ((v : ℝ) / den - c) * 2 ^ 62 := by simp only [w, t]; ring
    rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
    exact mul_le_mul_of_nonneg_right hv (by positivity)
  have ht0 : 0 ≤ t := by have := neg_abs_le c; simp only [t]; nlinarith [abs_nonneg c]
  have ht1 : t ≤ 2 ^ 63 := by have := le_abs_self c; simp only [t]; nlinarith [abs_nonneg c]
  -- the clamped value R
  have key : |((min F.toNat (two64 - 1) : ℕ) : ℝ) - t| ≤ δ * 2 ^ 62 + 1 := by
    have hwt' := abs_le.1 hwt
    rcases le_or_gt 0 F with hF0 | hF0
    · have hcast : ((F.toNat : ℕ) : ℝ) = (F : ℝ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg hF0]
      rcases le_total F.toNat (two64 - 1) with hm | hm
      · rw [min_eq_left hm, hcast, abs_le]; constructor <;> linarith
      · rw [min_eq_right hm]
        have h2 : ((two64 - 1 : ℕ) : ℝ) ≤ F := by rw [← hcast]; exact_mod_cast hm
        have h3 : ((two64 - 1 : ℕ) : ℝ) = 2 ^ 64 - 1 := by unfold two64; norm_num
        rw [h3] at h2 ⊢
        rw [abs_le]; constructor <;> nlinarith
    · have : F.toNat = 0 := Int.toNat_of_nonpos hF0.le
      rw [this, Nat.zero_min]
      have hF0' : (F : ℝ) + 1 ≤ 0 := by have : F + 1 ≤ 0 := by omega
                                        exact_mod_cast this
      simp only [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg ht0]
      linarith
  have e : (((min F.toNat (two64 - 1) : ℕ) : ℝ)) / 2 ^ 62 - 1 - c = (((min F.toNat (two64 - 1) : ℕ) : ℝ) - t) / 2 ^ 62 := by
    simp only [t]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62), div_le_iff₀ (by positivity)]
  calc _ ≤ δ * 2 ^ 62 + 1 := key
    _ = (δ + 1 / 2 ^ 62) * 2 ^ 62 := by field_simp


/-! ## Table entries -/

theorem pi_lo_lt : (piLoN : ℝ) / piD < π := by
  have := Real.pi_gt_d20; unfold piLoN piD; norm_num at this ⊢; linarith

theorem pi_gap : π - (piLoN : ℝ) / piD ≤ 1 / 10 ^ 20 := by
  have := Real.pi_lt_d20; unfold piLoN piD; norm_num at this ⊢; linarith

set_option maxHeartbeats 1000000 in
theorem entry_sound (M n : ℕ) (hM : 0 < M) (h4 : 4 ∣ M) (hn : n < M) :
    |((entry M n).1 : ℝ) / 2 ^ 62 - 1 - Real.cos (2 * π * n / M)| ≤ 4 / 2 ^ 62 ∧
    |((entry M n).2 : ℝ) / 2 ^ 62 - 1 - Real.sin (2 * π * n / M)| ≤ 4 / 2 ^ 62 := by
  obtain ⟨m4, rfl⟩ := h4
  have hm4 : 0 < m4 := by omega
  unfold entry
  simp only []
  have hq : 4 * n / (4 * m4) = n / m4 := Nat.mul_div_mul_left n m4 (by norm_num)
  have hM4 : 4 * m4 / 4 = m4 := by omega
  rw [hq, hM4]
  have hdm := Nat.div_add_mod n m4
  set q := n / m4 with hqd
  have hq4 : q < 4 := by rw [hqd]; exact Nat.div_lt_of_lt_mul (by linarith)
  have hrp : n - q * m4 = n % m4 := by
    rw [Nat.mul_comm]; apply Nat.sub_eq_of_eq_add; rw [Nat.add_comm]; exact hdm.symm
  rw [hrp]
  set rp := n % m4 with hrpd
  have hrp_lt : rp < m4 := Nat.mod_lt _ hm4
  set a := 2 * piLoN * rp with ha
  set b := piD * (4 * m4) with hb
  have hb0 : 0 < b := by rw [hb]; unfold piD; positivity
  obtain ⟨hc, hs⟩ := tay_bound a b NT hb0 (by unfold NT; norm_num)
  set re := tayRe a b NT NT
  set im := tayIm a b NT NT
  set den := b ^ (NT - 1) * fct (NT - 1) with hden
  have hden0 : 0 < den := by rw [hden, fct_eq]; positivity
  have hdenr : ((den : ℕ) : ℝ) = (b : ℝ) ^ (NT - 1) * (Nat.factorial (NT - 1) : ℝ) := by rw [hden, fct_eq]; push_cast; ring
  rw [← hdenr] at hc hs
  -- the angles
  set α : ℝ := 2 * π * rp / (4 * m4 : ℕ) with hα
  have hm4r : (0 : ℝ) < m4 := by exact_mod_cast hm4
  have hrpr : (rp : ℝ) < m4 := by exact_mod_cast hrp_lt
  have hab : (a : ℝ) / b = 2 * ((piLoN : ℝ) / piD) * rp / (4 * m4 : ℕ) := by
    rw [ha, hb]; push_cast; field_simp
  have hdiff : |α - (a : ℝ) / b| ≤ 1 / 10 ^ 20 := by
    rw [hab, hα]
    have e : 2 * π * rp / ((4 * m4 : ℕ) : ℝ) - 2 * ((piLoN : ℝ) / piD) * rp / ((4 * m4 : ℕ) : ℝ) =
        (π - (piLoN : ℝ) / piD) * (rp / (2 * m4)) := by push_cast; field_simp; ring
    rw [e, abs_mul]
    have h1 : |π - (piLoN : ℝ) / piD| ≤ 1 / 10 ^ 20 := by
      rw [abs_of_pos (by linarith [pi_lo_lt])]; exact pi_gap
    have h2 : |(rp : ℝ) / (2 * m4)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith
    calc _ ≤ 1 / 10 ^ 20 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hasmall : |(a : ℝ) / b| ≤ 15708 / 10000 := by
    rw [hab, abs_of_nonneg (by positivity)]
    have hlo : (piLoN : ℝ) / piD ≤ 31416 / 10000 := by unfold piLoN piD; norm_num
    have : 2 * ((piLoN : ℝ) / piD) * rp / ((4 * m4 : ℕ) : ℝ) = ((piLoN : ℝ) / piD) * (rp / m4) / 2 := by
      push_cast; field_simp; ring
    rw [this]
    have h3 : (rp : ℝ) / m4 ≤ 1 := by rw [div_le_one hm4r]; linarith
    have h4 : 0 ≤ (piLoN : ℝ) / piD := by unfold piLoN piD; norm_num
    nlinarith
  have htay : |(a : ℝ) / b| ^ NT / (NT.factorial : ℝ) ≤ 1 / 10 ^ 23 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hasmall NT
    unfold NT at *
    rw [div_le_iff₀ (by positivity)]
    calc |(a : ℝ) / b| ^ 28 ≤ (15708 / 10000) ^ 28 := this
      _ ≤ 1 / 10 ^ 23 * (Nat.factorial 28 : ℝ) := by norm_num [Nat.factorial]
  set δ : ℝ := 1 / 10 ^ 23 + 1 / 10 ^ 20 with hδ
  have hcos : |(re : ℝ) / den - Real.cos α| ≤ δ := by
    have := abs_cos_sub_cos_le α ((a : ℝ) / b)
    calc |(re : ℝ) / den - Real.cos α| ≤ |(re : ℝ) / den - Real.cos ((a : ℝ) / b)| + |Real.cos ((a : ℝ) / b) - Real.cos α| :=
          abs_sub_le _ _ _
      _ = |Real.cos ((a : ℝ) / b) - (re : ℝ) / den| + |Real.cos α - Real.cos ((a : ℝ) / b)| := by
          rw [abs_sub_comm ((re : ℝ) / den) (Real.cos ((a : ℝ) / b)), abs_sub_comm (Real.cos ((a : ℝ) / b)) (Real.cos α)]
      _ ≤ _ := add_le_add (le_trans hc htay) (le_trans this hdiff)
  have hsin : |(im : ℝ) / den - Real.sin α| ≤ δ := by
    have := abs_sin_sub_sin_le α ((a : ℝ) / b)
    calc |(im : ℝ) / den - Real.sin α| ≤ |(im : ℝ) / den - Real.sin ((a : ℝ) / b)| + |Real.sin ((a : ℝ) / b) - Real.sin α| :=
          abs_sub_le _ _ _
      _ = |Real.sin ((a : ℝ) / b) - (im : ℝ) / den| + |Real.sin α - Real.sin ((a : ℝ) / b)| := by
          rw [abs_sub_comm ((im : ℝ) / den) (Real.sin ((a : ℝ) / b)), abs_sub_comm (Real.sin ((a : ℝ) / b)) (Real.sin α)]
      _ ≤ _ := add_le_add (le_trans hs htay) (le_trans this hdiff)
  have hδ0 : 0 ≤ δ := by positivity
  have hδ4 : δ + 1 / 2 ^ 62 ≤ 4 / 2 ^ 62 := by rw [hδ]; norm_num
  -- the rotation
  have hθ : 2 * π * (n : ℝ) / ((4 * m4 : ℕ) : ℝ) = q * (π / 2) + α := by
    have : (n : ℝ) = q * m4 + rp := by
      have : n = q * m4 + rp := by rw [hqd, hrpd]; rw [Nat.mul_comm]; exact (Nat.div_add_mod n m4).symm
      exact_mod_cast this
    rw [this, hα]; push_cast; field_simp; ring
  rw [hθ]
  have hR : ∀ (v : ℤ) (c : ℝ), |(v : ℝ) / den - c| ≤ δ → |c| ≤ 1 → |(roundE v den : ℝ) / 2 ^ 62 - 1 - c| ≤ 4 / 2 ^ 62 :=
    fun v c h1 h2 => le_trans (roundE_spec v den hden0 c δ h2 hδ0 h1) hδ4
  have neg_close : ∀ (v : ℤ) (c : ℝ), |(v : ℝ) / den - c| ≤ δ → |((-v : ℤ) : ℝ) / den - (-c)| ≤ δ := by
    intro v c h; rw [show ((-v : ℤ) : ℝ) / den - -c = -((v : ℝ) / den - c) by push_cast; ring, abs_neg]; exact h
  interval_cases q
  · simp only [if_pos rfl, Nat.cast_zero, zero_mul, zero_add]
    exact ⟨hR _ _ hcos (Real.abs_cos_le_one _), hR _ _ hsin (Real.abs_sin_le_one _)⟩
  · simp only [show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, Nat.cast_one, one_mul]
    rw [show π / 2 + α = α + π / 2 by ring, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    exact ⟨hR _ _ (neg_close _ _ hsin) (by rw [abs_neg]; exact Real.abs_sin_le_one _), hR _ _ hcos (Real.abs_cos_le_one _)⟩
  · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false, if_true, Nat.cast_ofNat]
    rw [show 2 * (π / 2) + α = α + π by ring, Real.cos_add_pi, Real.sin_add_pi]
    exact ⟨hR _ _ (neg_close _ _ hcos) (by rw [abs_neg]; exact Real.abs_cos_le_one _),
      hR _ _ (neg_close _ _ hsin) (by rw [abs_neg]; exact Real.abs_sin_le_one _)⟩
  · simp only [show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, if_false,
      Nat.cast_ofNat]
    rw [show 3 * (π / 2) + α = (α + π / 2) + π by ring, Real.cos_add_pi, Real.sin_add_pi, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two, neg_neg]
    exact ⟨hR _ _ hsin (Real.abs_sin_le_one _), hR _ _ (neg_close _ _ hcos) (by rw [abs_neg]; exact Real.abs_cos_le_one _)⟩

/-! ## The table check -/

theorem tabOK_spec (M tab : ℕ) : ∀ m, tabOK M tab m = true → ∀ n < m, getT tab n = entryP M n := by
  intro m
  induction m with
  | zero => intro _ n hn; omega
  | succ m ih =>
    intro h n hn
    simp only [tabOK, Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | hn
    · exact ih h.2 n hn
    · rw [hn]; exact h.1

theorem entry_lt (M n : ℕ) : (entry M n).1 < two64 ∧ (entry M n).2 < two64 := by
  unfold entry roundE
  simp only []
  constructor <;> (apply lt_of_le_of_lt (min_le_right _ _); unfold two64; norm_num)

theorem neg_close63 (x : ℕ) (c : ℝ) (hc : c ≤ 1) (h : |(x : ℝ) / 2 ^ 62 - 1 - c| ≤ 4 / 2 ^ 62) :
    |(((two63 - x : ℕ) : ℝ)) / 2 ^ 62 - 1 - (-c)| ≤ 4 / 2 ^ 62 := by
  have h63 : (two63 : ℝ) = 2 * 2 ^ 62 := by unfold two63; norm_num
  rcases le_total x two63 with hx | hx
  · rw [Nat.cast_sub hx, h63]
    have : (2 * 2 ^ 62 - (x : ℝ)) / 2 ^ 62 - 1 - -c = -((x : ℝ) / 2 ^ 62 - 1 - c) := by field_simp; ring
    rw [this, abs_neg]; exact h
  · rw [Nat.sub_eq_zero_of_le hx]
    have hx' : (2 * 2 ^ 62 : ℝ) ≤ x := by rw [← h63]; exact_mod_cast hx
    have h1 := (abs_le.1 h).2
    have : (2 : ℝ) ≤ (x : ℝ) / 2 ^ 62 := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [Nat.cast_zero, zero_div, abs_le]; constructor <;> linarith

/-- **Table soundness** (full table with fields `0 … M−1`). -/
theorem tabOK_good (M tab : ℕ) (hM : 0 < M) (h4 : 4 ∣ M) (h : tabOK M tab M = true) : TabGood M tab := by
  intro n hn
  have he := tabOK_spec M tab M h n hn
  obtain ⟨l1, l2⟩ := entry_lt M n
  have hc : (lookE tab M n).1 = (entry M n).1 := by
    show getT tab n % two64 = _
    rw [he]; unfold entryP; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1]
  have hs : (lookE tab M n).2 = (entry M n).2 := by
    show Nat.shiftRight (getT tab n) 64 = _
    rw [shr_eq, show (2 : ℕ) ^ 64 = two64 by rfl, he]; unfold entryP
    rw [Nat.add_mul_div_left _ _ (by unfold two64; norm_num), Nat.div_eq_of_lt l1, zero_add]
  rw [hc, hs]
  exact entry_sound M n hM h4 hn


theorem tabOKr_spec (M tab a : ℕ) : ∀ n, tabOKr M tab a n = true → ∀ m, a ≤ m → m < a + n → getT tab m = entryP M m := by
  intro n
  induction n with
  | zero => intro _ m h1 h2; omega
  | succ n ih =>
    intro h m h1 h2
    simp only [tabOKr, Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_or_ge m (a + n) with hm | hm
    · exact ih h.2 m h1 hm
    · have : m = a + n := by omega
      rw [this]; exact h.1

/-- **Table soundness from range checks** of size `R`. -/
theorem tabGood_of_ranges (M tab R : ℕ) (hM : 0 < M) (h4 : 4 ∣ M) (hR : 0 < R) (hdiv : R ∣ M)
    (h : ∀ i < M / R, tabOKr M tab (R * i) R = true) : TabGood M tab := by
  intro n hn
  have he : getT tab n = entryP M n := by
    have hi : n / R < M / R := Nat.div_lt_div_of_lt_of_dvd hdiv hn
    have h1 : R * (n / R) ≤ n := Nat.mul_div_le n R
    have h2 : n < R * (n / R) + R := by
      have := Nat.lt_div_mul_add (a := n) hR
      rw [Nat.mul_comm] at this; exact this
    exact tabOKr_spec M tab (R * (n / R)) R (h _ hi) n h1 h2
  obtain ⟨l1, l2⟩ := entry_lt M n
  have hc : (lookE tab M n).1 = (entry M n).1 := by
    show getT tab n % two64 = _
    rw [he]; unfold entryP; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1]
  have hs : (lookE tab M n).2 = (entry M n).2 := by
    show Nat.shiftRight (getT tab n) 64 = _
    rw [shr_eq, show (2 : ℕ) ^ 64 = two64 by rfl, he]; unfold entryP
    rw [Nat.add_mul_div_left _ _ (by unfold two64; norm_num), Nat.div_eq_of_lt l1, zero_add]
  rw [hc, hs]
  exact entry_sound M n hM h4 hn

end Palprimes.M2
