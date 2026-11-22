import Mathlib

/-! # The constant coefficient of the Fejér family (dossier §2.13.3–2.13.4)

With `m = ⌊7b/10⌋`, `H_m = Σ_{k≤m} 1/k`, the constant coefficient of `T_b` is
`τ₀(b) = (3819 (2 m H_m − m − 1) + 10000 b) / (10000 b m)` (weights `ω₁ = 57/50`, `ω = 19/25`,
`b^p = 200b/201`). We prove `τ₀(b) < b^{−2θ}` for `θ = 0.2608` and every `b ≥ 10`:
* `10 ≤ b < 128`: kernel-checked `τ₀^{625} b^{326} < 1` (`tauAll_ok`), with `H_m` rounded up;
* `b ≥ 128`: `b τ₀ ≤ 0.7638 log b + 1.8312 < b^{0.4}` through `log b ≤ 10 b^{1/10}/e`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- `H_m = Σ_{M<m} 1/(M+1)`. -/
noncomputable def Hm (m : ℕ) : ℝ := ∑ M ∈ range m, 1 / ((M : ℝ) + 1)

/-- `m = ⌊7b/10⌋`. -/
def mB (b : ℕ) : ℕ := 7 * b / 10

/-- `τ₀(b)`. -/
noncomputable def tauF (b : ℕ) : ℝ :=
  (3819 * (2 * (mB b : ℝ) * Hm (mB b) - mB b - 1) + 10000 * b) / (10000 * b * mB b)

theorem Hm_ge_one (m : ℕ) (hm : 1 ≤ m) : 1 ≤ Hm m := by
  unfold Hm
  calc (1 : ℝ) = ∑ M ∈ range 1, 1 / ((M : ℝ) + 1) := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hm) (fun i _ _ => by positivity)

theorem mB_ge (b : ℕ) (hb : 10 ≤ b) : 7 ≤ mB b := by unfold mB; omega

theorem tauF_pos (b : ℕ) (hb : 10 ≤ b) : 0 < tauF b := by
  have hm : (7 : ℝ) ≤ mB b := by exact_mod_cast mB_ge b hb
  have hH := Hm_ge_one (mB b) (by have := mB_ge b hb; omega)
  have hb' : (10 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tauF
  apply div_pos _ (by positivity)
  nlinarith

/-! ## Numeric range `10 ≤ b < 128` -/

def ScT : ℕ := 1000000000000000

/-- `Σ_{k<m} ⌈ScT/(k+1)⌉`. -/
def hFix : ℕ → ℕ
  | 0 => 0
  | k + 1 => hFix k + (ScT + k) / (k + 1)

def tauNum (b : ℕ) : ℕ := 3819 * (2 * mB b * hFix (mB b) - (mB b + 1) * ScT) + 10000 * b * ScT
def tauDen (b : ℕ) : ℕ := 10000 * b * mB b * ScT

def tauOK (b : ℕ) : Bool := decide (tauNum b ^ 625 * b ^ 326 < tauDen b ^ 625)

/-- Checks `b = 10, …, k + 9`. -/
def tauAll : ℕ → Bool
  | 0 => true
  | k + 1 => tauAll k && tauOK (k + 10)

theorem tauAll_ok : tauAll 118 = true := by decide +kernel

theorem tauAll_sound : ∀ k, tauAll k = true → ∀ b, 10 ≤ b → b < k + 10 → tauOK b = true := by
  intro k
  induction k with
  | zero => intro _ b h1 h2; omega
  | succ k ih =>
    intro h b h1 h2
    simp only [tauAll, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge b (k + 10) with h3 | h3
    · exact ih h.1 b h1 h3
    · have : b = k + 10 := by omega
      subst this; exact h.2

theorem hFix_ge (k : ℕ) : (ScT : ℝ) * Hm k ≤ hFix k := by
  induction k with
  | zero => simp [Hm, hFix]
  | succ k ih =>
    rw [hFix, Nat.cast_add, Hm, Finset.sum_range_succ, mul_add]
    have h1 : (ScT : ℝ) * (1 / ((k : ℝ) + 1)) ≤ (((ScT + k) / (k + 1) : ℕ) : ℝ) := by
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h := Nat.div_add_mod (ScT + k) (k + 1)
      have h2 := Nat.mod_lt (ScT + k) (by omega : 0 < k + 1)
      have h3 : ScT ≤ (k + 1) * ((ScT + k) / (k + 1)) := by omega
      have h4 : (ScT : ℝ) ≤ ((k : ℝ) + 1) * (((ScT + k) / (k + 1) : ℕ) : ℝ) := by exact_mod_cast h3
      rw [mul_one_div, div_le_iff₀ hk]; linarith
    unfold Hm at ih
    linarith

theorem tauF_le_fix (b : ℕ) (hb : 10 ≤ b) : tauF b ≤ (tauNum b : ℝ) / tauDen b := by
  have hm7 := mB_ge b hb
  have hm : (0 : ℝ) < mB b := by exact_mod_cast (by omega : 0 < mB b)
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hS : (0 : ℝ) < ScT := by norm_num [ScT]
  have hH := hFix_ge (mB b)
  unfold tauF tauNum tauDen
  have e : (10000 * (b : ℝ) * mB b) = ((10000 * b * mB b * ScT : ℕ) : ℝ) / ScT := by
    push_cast; field_simp
  have hDpos : (0 : ℝ) < ((10000 * b * mB b * ScT : ℕ) : ℝ) := by
    have : 0 < 10000 * b * mB b * ScT :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)) (by norm_num [ScT])
    exact_mod_cast this
  rw [e, div_div_eq_mul_div, div_le_div_iff_of_pos_right hDpos]
  have hsub : (2 * (mB b : ℝ) * hFix (mB b) - (mB b + 1) * ScT) ≤
      ((2 * mB b * hFix (mB b) - (mB b + 1) * ScT : ℕ) : ℝ) := by
    rcases le_total ((mB b + 1) * ScT) (2 * mB b * hFix (mB b)) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h]
      have : (((mB b + 1) * ScT : ℕ) : ℝ) ≥ ((2 * mB b * hFix (mB b) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢; linarith
  push_cast
  have : 2 * (mB b : ℝ) * (ScT * Hm (mB b)) ≤ 2 * (mB b : ℝ) * hFix (mB b) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  nlinarith

/-- `x < B^{-c}` from `x^n B^k < 1` and `c n = k`. -/
theorem lt_rpow_of_pow (B x : ℝ) (hB : 0 < B) (_hx : 0 ≤ x) (n k : ℕ) (_hn : n ≠ 0) (c : ℝ)
    (hc : c * n = k) (h : x ^ n * B ^ k < 1) : x < B ^ (-c) := by
  set y := B ^ (-c) with hy
  have hy0 : 0 < y := by positivity
  have hyn : y ^ n * B ^ k = 1 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hB.le, ← Real.rpow_natCast B k,
      ← Real.rpow_add hB, ← hc]
    simp
  by_contra hcon
  push Not at hcon
  have h1 : y ^ n ≤ x ^ n := pow_le_pow_left₀ hy0.le hcon n
  have h2 : y ^ n * B ^ k ≤ x ^ n * B ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

theorem cast_pow_check (A D b n k : ℕ) (hD : 0 < D) (h : A ^ n * b ^ k < D ^ n) :
    ((A : ℝ) / D) ^ n * (b : ℝ) ^ k < 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_pow, div_mul_eq_mul_div, div_lt_one (by positivity)]
  exact_mod_cast h

theorem tauF_lt_of_check (b : ℕ) (hb : 10 ≤ b) (n k : ℕ) (hn : n = 625) (hk : k = 326)
    (h : tauNum b ^ n * b ^ k < tauDen b ^ n) : tauF b < (b : ℝ) ^ (-(2 * (2608 / 10000 : ℝ))) := by
  have hD : 0 < tauDen b :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by have := mB_ge b hb; omega)) (by norm_num [ScT])
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have h2 := cast_pow_check (tauNum b) (tauDen b) b n k hD h
  apply lt_rpow_of_pow (b : ℝ) (tauF b) hb0 (tauF_pos b hb).le n k (by omega) _
    (by rw [hn, hk]; norm_num)
  have h1 : tauF b ^ n ≤ ((tauNum b : ℝ) / tauDen b) ^ n :=
    pow_le_pow_left₀ (tauF_pos b hb).le (tauF_le_fix b hb) n
  calc tauF b ^ n * (b : ℝ) ^ k ≤ ((tauNum b : ℝ) / tauDen b) ^ n * (b : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ < 1 := h2

theorem tauF_lt_small (b : ℕ) (hb : 10 ≤ b) (hb2 : b < 128) :
    tauF b < (b : ℝ) ^ (-(2 * (2608 / 10000 : ℝ))) := by
  have hok := tauAll_sound 118 tauAll_ok b hb (by omega)
  simp only [tauOK, decide_eq_true_eq] at hok
  generalize hn : 625 = n at hok
  generalize hk : 326 = k at hok
  exact tauF_lt_of_check b hb n k hn.symm hk.symm hok

/-! ## Analytic range `b ≥ 128` -/

theorem log_le_div_e (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos hy he)
  rw [Real.log_div hy.ne' he.ne', Real.log_exp] at h
  linarith

theorem Hm_le_log (m : ℕ) : Hm m ≤ 1 + Real.log m := by
  have h := harmonic_le_one_add_log m
  have e : (harmonic m : ℝ) = Hm m := by
    unfold harmonic Hm; push_cast; simp only [one_div]
  rw [← e]; exact h

theorem tauF_lt_large (b : ℕ) (hb : 128 ≤ b) :
    tauF b < (b : ℝ) ^ (-(2 * (2608 / 10000 : ℝ))) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  set m := mB b with hmdef
  have hm7 : 7 ≤ m := mB_ge b (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmb : m ≤ b := by simp only [m, mB]; omega
  have h100 : 69 * b ≤ 100 * m := by simp only [m, mB]; omega
  -- `H_m ≤ 1 + log b`
  have hH : Hm m ≤ 1 + Real.log b := by
    have := Hm_le_log m
    have : Real.log m ≤ Real.log b := Real.log_le_log hm0 (by exact_mod_cast hmb)
    linarith
  -- `b/m ≤ 100/69`
  have hbm : (b : ℝ) / m ≤ 100 / 69 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]
    have : ((69 * b : ℕ) : ℝ) ≤ ((100 * m : ℕ) : ℝ) := by exact_mod_cast h100
    push_cast at this; linarith
  -- `b τ₀ ≤ 0.7638 log b + 1.8312`
  have hbt : (b : ℝ) * tauF b ≤ 7638 / 10000 * Real.log b + 3819 / 10000 + 100 / 69 := by
    unfold tauF
    rw [← hmdef]
    have e : (b : ℝ) * ((3819 * (2 * (m : ℝ) * Hm m - m - 1) + 10000 * b) / (10000 * b * m)) =
        3819 / 10000 * (2 * Hm m - 1 - 1 / m) + b / m := by
      field_simp
    rw [e]
    have : 0 ≤ 1 / (m : ℝ) := by positivity
    nlinarith
  -- `y = b^{1/10} ≥ 1.6`
  set y := (b : ℝ) ^ ((1 : ℝ) / 10) with hydef
  have hy0 : 0 < y := by positivity
  have hy10 : y ^ 10 = b := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; norm_num
  have hy16 : (16 / 10 : ℝ) ≤ y := by
    by_contra h
    push Not at h
    have : y ^ 10 < (16 / 10 : ℝ) ^ 10 := pow_lt_pow_left₀ h hy0.le (by norm_num)
    have hb128 : (128 : ℝ) ≤ b := by exact_mod_cast hb
    rw [hy10] at this; norm_num at this; linarith
  have hlog : Real.log b ≤ 10 * y / Real.exp 1 := by
    have h := log_le_div_e y hy0
    have e : Real.log b = 10 * Real.log y := by
      rw [hydef, Real.log_rpow hb0]; ring
    rw [e]; have := Real.exp_pos 1
    rw [mul_div_assoc]; linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hlog2 : Real.log b ≤ 10 * y / 2.7182818283 := by
    refine le_trans hlog ?_
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) he.le
  have hy3 : (16 / 10 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy16 3
  have hy4 : 7638 / 10000 * Real.log b + 3819 / 10000 + 100 / 69 < y ^ 4 := by
    have e4 : y ^ 4 = y * y ^ 3 := by ring
    have h5 : y * (16 / 10 : ℝ) ^ 3 ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left hy3 hy0.le
    have h6 : 7638 / 10000 * Real.log b ≤ 7638 / 10000 * (10 * y / 2.7182818283) :=
      mul_le_mul_of_nonneg_left hlog2 (by norm_num)
    norm_num at h5 h6 ⊢
    nlinarith
  -- `y^4 = b^{0.4} ≤ b^{1 − 2θ}`
  have hy4b : y ^ 4 ≤ (b : ℝ) ^ (1 - 2 * (2608 / 10000 : ℝ)) := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    apply Real.rpow_le_rpow_of_exponent_le hb1; norm_num
  have h1 : (b : ℝ) * tauF b < (b : ℝ) ^ (1 - 2 * (2608 / 10000 : ℝ)) := by linarith
  rw [Real.rpow_sub hb0, Real.rpow_one] at h1
  rw [Real.rpow_neg hb0.le]
  rw [lt_div_iff₀ (by positivity)] at h1
  have hpos := Real.rpow_pos_of_pos hb0 (2 * (2608 / 10000 : ℝ))
  have h2 : tauF b * (b : ℝ) ^ (2 * (2608 / 10000 : ℝ)) < 1 := by
    rw [mul_assoc] at h1
    exact lt_of_mul_lt_mul_left (by linarith) hb0.le
  rw [← one_div, lt_div_iff₀ hpos]; exact h2

/-- **`τ₀(b) < b^{−2θ}` for every `b ≥ 10`** (`θ = 0.2608`). -/
theorem tauF_lt (b : ℕ) (hb : 10 ≤ b) : tauF b < (b : ℝ) ^ (-(2 * (2608 / 10000 : ℝ))) := by
  rcases Nat.lt_or_ge b 128 with h | h
  · exact tauF_lt_small b hb h
  · exact tauF_lt_large b h

end Palprimes
