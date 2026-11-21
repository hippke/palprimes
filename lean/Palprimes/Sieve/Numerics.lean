import Palprimes.Sieve.Intervals

/-! # Numeric building blocks for the sieve certificate (M14) -/

open Finset Real

namespace Palprimes

/-- `log(1 + t) ≤ t − t²/2 + t³/3 + t⁴/(1 − t)` for `0 ≤ t < 1`. -/
theorem log_one_add_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / (1 - t) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) 3
  rw [abs_neg, abs_of_nonneg h0, sub_neg_eq_add] at h
  have h' := (abs_le.1 h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h'
  norm_num at h'
  have e : (-t) ^ 3 = -t ^ 3 := by ring
  rw [e] at h'
  linarith

/-- Rational upper bound for `log r`, `1 ≤ r < 2`. -/
noncomputable def logub (r : ℝ) : ℝ := (r - 1) - (r - 1) ^ 2 / 2 + (r - 1) ^ 3 / 3 + (r - 1) ^ 4 / (2 - r)

theorem log_le_logub (r : ℝ) (h1 : 1 ≤ r) (h2 : r < 2) : Real.log r ≤ logub r := by
  have := log_one_add_le (r - 1) (by linarith) (by linarith)
  unfold logub
  rw [show 1 + (r - 1) = r by ring, show 1 - (r - 1) = 2 - r by ring] at this
  exact this

/-- `e^γ ≤ 1.7813`, i.e. `e^{−γ} ≥ 1/1.7813`. -/
theorem exp_neg_gamma_ge : 10000 / 17813 ≤ Real.exp (-Real.eulerMascheroniConstant) := by
  have hγ := eulerMascheroni_lt
  have hb := Real.exp_bound (x := (5773 / 10000 : ℝ)) (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (n := 8) (by norm_num)
  have hb' := (abs_le.1 hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb'
  norm_num at hb'
  have h1 : Real.exp (5773 / 10000) ≤ 17813 / 10000 := by linarith
  have h2 : Real.exp Real.eulerMascheroniConstant ≤ 17813 / 10000 :=
    le_trans (Real.exp_le_exp.2 (by norm_num at hγ ⊢; linarith)) h1
  rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
  have := Real.exp_pos Real.eulerMascheroniConstant
  nlinarith

/-- The inner grid `c_i = 1 + i/10`. -/
noncomputable def cIn (i : ℕ) : ℝ := 1 + (i : ℝ) / 10

theorem cIn_mono : Monotone cIn := by
  intro i j hij; unfold cIn
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- Rational lower bound of `g_K(v)` on the inner grid (18 steps, up to `2.8`). -/
noncomputable def gQ (v : ℝ) : ℝ :=
  v - ∑ i ∈ range 18, max (v - cIn i) 0 * logub (cIn (i + 1) / cIn i)

theorem gQ_le_gKc (v : ℝ) : gQ v ≤ gKc cIn 18 v := by
  unfold gQ gKc
  have : ∑ i ∈ range 18, max (v - cIn i) 0 * Real.log (cIn (i + 1) / cIn i) ≤
      ∑ i ∈ range 18, max (v - cIn i) 0 * logub (cIn (i + 1) / cIn i) := by
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    have hc : 0 < cIn i := by unfold cIn; positivity
    apply log_le_logub
    · rw [le_div_iff₀ hc, one_mul]; exact cIn_mono (Nat.le_succ i)
    · rw [div_lt_iff₀ hc]; unfold cIn; push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  linarith

theorem cIn_zero : cIn 0 = 1 := by simp [cIn]
theorem cIn_18 : cIn 18 = 28 / 10 := by norm_num [cIn]

/-- Shared numeric step for the Buchstab packages. -/
theorem B_num (a b m mQ q : ℝ) (ha : 0 < a) (hab : a < b) (hba : b < 2 * a) (hmQ : 0 < mQ) (hm : mQ ≤ m)
    (hU : 1 ≤ 1 / mQ)
    (hq : 1 / (20 * (99 / 100) ^ 3 * a) * (1 / mQ - 1) * logub (b / a) ≤ q) :
    1 / (20 * (99 / 100) ^ 3 * a) * (1 / m - 1) * Real.log (b / a) ≤ q := by
  have hlog : Real.log (b / a) ≤ logub (b / a) :=
    log_le_logub _ (by rw [le_div_iff₀ ha]; linarith) (by rw [div_lt_iff₀ ha]; linarith)
  have hlog0 : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hm1 : 1 / m - 1 ≤ 1 / mQ - 1 := by
    have := one_div_le_one_div_of_le hmQ hm; linarith
  have hc : 0 < 1 / (20 * (99 / 100) ^ 3 * a) := by positivity
  calc 1 / (20 * (99 / 100) ^ 3 * a) * (1 / m - 1) * Real.log (b / a)
      ≤ 1 / (20 * (99 / 100) ^ 3 * a) * (1 / mQ - 1) * Real.log (b / a) := by
        apply mul_le_mul_of_nonneg_right _ hlog0
        exact mul_le_mul_of_nonneg_left hm1 hc.le
    _ ≤ 1 / (20 * (99 / 100) ^ 3 * a) * (1 / mQ - 1) * logub (b / a) :=
        mul_le_mul_of_nonneg_left hlog (by have : 0 ≤ 1 / mQ - 1 := by linarith
                                           positivity)
    _ ≤ q := hq

theorem exp_le_one_div_one_sub (s : ℝ) (h0 : 0 ≤ s) (h1 : s < 1) : Real.exp s ≤ 1 / (1 - s) := by
  have := Real.add_one_le_exp (-s)
  rw [Real.exp_neg] at this
  rw [le_div_iff₀ (by linarith)]
  have hp := Real.exp_pos s
  have : 1 - s ≤ (Real.exp s)⁻¹ := by linarith
  calc Real.exp s * (1 - s) ≤ Real.exp s * (Real.exp s)⁻¹ := mul_le_mul_of_nonneg_left this hp.le
    _ = 1 := by field_simp

section Packages

variable (C₂ C₃ c₁ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (B : ℕ) (hB : 1 ≤ B)
include hC₂ hC₃ hB

/-- Smooth lower bound for `V · S` at exponent `v`, from a rational `g < gQ v`. -/
theorem smooth_pkg (v g : ℝ) (hv : 0 ≤ v) (hv2 : v ≤ 28 / 10) (hg : 0 < g) (hgQ : g < gQ v) :
    ∀ᶠ t : ℕ in Filter.atTop, ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g ≤
        (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y :=
  smooth_eventually C₂ C₃ hC₂ hC₃ B hB v g (99 / 100) hv hg (by norm_num) cIn 18 cIn_zero cIn_mono
    (by rw [cIn_18]; exact hv2) (lt_of_lt_of_le hgQ (gQ_le_gKc v))

/-- **Richert package.** -/
theorem R_pkg (a b v g q : ℝ) (ha : 0 < a) (hab : a < b) (hba : b < 2 * a) (hb : b ≤ 23 / 100)
    (hv : 0 ≤ v) (hvb : v / 10 < 6 / 25 - b) (hv2 : v ≤ 28 / 10) (hg : 0 < g) (hgQ : g < gQ v)
    (hq : (1 - a / (23 / 100)) * (17813 / 10000) / (99 / 100 * g) * logub (b / a) ≤ q) :
    (∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ a < p → (p : ℝ) ≤ x ^ b →
      (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) /
          (p * selS (PB B (Zc x)) (x ^ ((6 : ℝ) / 25) / p)) ≤
        ((1 - a / (23 / 100)) / (99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g)) *
          (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p) ∧
    ((1 - a / (23 / 100)) / (99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g)) *
      Real.log (b / a) ≤ q := by
  have he := exp_neg_gamma_ge
  have he0 : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  refine ⟨richert_interval B a b v _ ha hab.le hb hv hvb (by positivity)
    (smooth_pkg C₂ C₃ hC₂ hC₃ B hB v g hv hv2 hg hgQ), ?_⟩
  have hwa : 0 ≤ 1 - a / (23 / 100) := by
    have : a / (23 / 100) ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
    linarith
  have hlog : Real.log (b / a) ≤ logub (b / a) :=
    log_le_logub _ (by rw [le_div_iff₀ ha]; linarith) (by rw [div_lt_iff₀ ha]; linarith)
  have hlog0 : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hM : (1 - a / (23 / 100)) / (99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g) ≤
      (1 - a / (23 / 100)) * (17813 / 10000) / (99 / 100 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 - a / (23 / 100)) * (99 / 100 * g) * 1 ≤
        (1 - a / (23 / 100)) * (17813 / 10000) * (99 / 100 * g) * Real.exp (-Real.eulerMascheroniConstant) := by
      have h1 : (1 : ℝ) ≤ 17813 / 10000 * Real.exp (-Real.eulerMascheroniConstant) := by linarith
      have h0 : 0 ≤ (1 - a / (23 / 100)) * (99 / 100 * g) := by positivity
      nlinarith
    nlinarith
  calc _ ≤ (1 - a / (23 / 100)) * (17813 / 10000) / (99 / 100 * g) * logub (b / a) :=
        mul_le_mul hM hlog hlog0 (by positivity)
    _ ≤ q := hq

/-- **Buchstab package, smooth bound.** -/
theorem B_pkg_S (a b v g q : ℝ) (ha : 0 < a) (hab : a < b) (hba : b < 2 * a)
    (hv : 0 ≤ v) (hvb : (2 * v + 1) * b ≤ 6 / 25) (hv2 : v ≤ 28 / 10) (hg : 0 < g) (hgQ : g < gQ v)
    (hU : 1 ≤ 1 / (99 / 100 * (10000 / 17813) * g))
    (hq : 1 / (20 * (99 / 100) ^ 3 * a) * (1 / (99 / 100 * (10000 / 17813) * g) - 1) * logub (b / a) ≤ q) :
    (∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ a < p → (p : ℝ) ≤ x ^ b →
      1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p ≤
        ((1 / (20 * (99 / 100) ^ 3 * a)) *
          (1 / (99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g) - 1)) *
          (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p) ∧
    ((1 / (20 * (99 / 100) ^ 3 * a)) * (1 / (99 / 100 * Real.exp (-Real.eulerMascheroniConstant) * g) - 1)) *
      Real.log (b / a) ≤ q := by
  have he := exp_neg_gamma_ge
  refine ⟨buchstab_interval C₃ hC₃ B hB a b v _ (99 / 100) ha hab.le hv hvb (by positivity)
    (by norm_num) (by norm_num) (smooth_pkg C₂ C₃ hC₂ hC₃ B hB v g hv hv2 hg hgQ), ?_⟩
  exact B_num a b _ (99 / 100 * (10000 / 17813) * g) q ha hab hba (by positivity)
    (by apply mul_le_mul_of_nonneg_right _ hg.le; nlinarith) hU hq

include hc₁ in
/-- **Buchstab package, Rankin with `a = log k`, integer exponent `n`.** -/
theorem B_pkg_R (a b q : ℝ) (k n : ℕ) (ha : 0 < a) (hab : a < b) (hba : b < 2 * a) (hk : 2 ≤ k) (hk2 : k < 101)
    (hvb : (2 * (n : ℝ) + 1) * b ≤ 6 / 25)
    (hmQ : 0 < 1 - (1 / (k : ℝ)) ^ n * (27182818286 / 10 ^ 10) ^ (k - 1) / (1 - ((k : ℝ) - 1) / 100))
    (hU : 1 ≤ 1 / (1 - (1 / (k : ℝ)) ^ n * (27182818286 / 10 ^ 10) ^ (k - 1) / (1 - ((k : ℝ) - 1) / 100)))
    (hq : 1 / (20 * (99 / 100) ^ 3 * a) *
      (1 / (1 - (1 / (k : ℝ)) ^ n * (27182818286 / 10 ^ 10) ^ (k - 1) / (1 - ((k : ℝ) - 1) / 100)) - 1) *
        logub (b / a) ≤ q) :
    (∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ a < p → (p : ℝ) ≤ x ^ b →
      1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p ≤
        ((1 / (20 * (99 / 100) ^ 3 * a)) *
          (1 / (1 - (k : ℝ) ^ (-(n : ℝ)) * Real.exp (((k : ℝ) - 1) * (1 + 1 / 100))) - 1)) *
          (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p) ∧
    ((1 / (20 * (99 / 100) ^ 3 * a)) *
      (1 / (1 - (k : ℝ) ^ (-(n : ℝ)) * Real.exp (((k : ℝ) - 1) * (1 + 1 / 100))) - 1)) *
      Real.log (b / a) ≤ q := by
  set mQ := 1 - (1 / (k : ℝ)) ^ n * (27182818286 / 10 ^ 10) ^ (k - 1) / (1 - ((k : ℝ) - 1) / 100)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkk : ((k : ℝ) - 1) / 100 < 1 := by
    have : (k : ℝ) < 101 := by exact_mod_cast hk2
    rw [div_lt_one (by norm_num)]; linarith
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) ≤ ((k : ℝ) - 1) / 100 := div_nonneg (by linarith) (by norm_num)
  -- `mQ ≤ m`
  have hexp : Real.exp (((k : ℝ) - 1) * (1 + 1 / 100)) ≤
      (27182818286 / 10 ^ 10) ^ (k - 1) / (1 - ((k : ℝ) - 1) / 100) := by
    have e1 : Real.exp (((k : ℝ) - 1) * (1 + 1 / 100)) = Real.exp 1 ^ (k - 1) * Real.exp (((k : ℝ) - 1) / 100) := by
      rw [← Real.exp_natCast_mul, ← Real.exp_add]; congr 1
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1]
    calc Real.exp 1 ^ (k - 1) * Real.exp (((k : ℝ) - 1) / 100)
        ≤ (27182818286 / 10 ^ 10) ^ (k - 1) * (1 / (1 - ((k : ℝ) - 1) / 100)) :=
          mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) _)
            (exp_le_one_div_one_sub _ hk1 hkk) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hkn : (k : ℝ) ^ (-(n : ℝ)) = (1 / (k : ℝ)) ^ n := by
    rw [Real.rpow_neg hk0.le, Real.rpow_natCast, one_div, inv_pow]
  have hm : mQ ≤ 1 - (k : ℝ) ^ (-(n : ℝ)) * Real.exp (((k : ℝ) - 1) * (1 + 1 / 100)) := by
    simp only [mQ]; rw [hkn]
    have : 0 ≤ (1 / (k : ℝ)) ^ n := by positivity
    have := mul_le_mul_of_nonneg_left hexp this
    rw [mul_div_assoc]; linarith
  refine ⟨buchstab_interval C₃ hC₃ B hB a b n _ (99 / 100) ha hab.le (Nat.cast_nonneg n) hvb
    (lt_of_lt_of_le hmQ hm) (by norm_num) (by norm_num)
    (rankin_eventually c₁ hc₁ B k hk n (1 / 100) (Nat.cast_nonneg n) (by norm_num)), ?_⟩
  exact B_num a b _ mQ q ha hab hba hmQ hm hU hq

end Packages

end Palprimes
