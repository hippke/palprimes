import KappaOmega2.StatementsK
import Palprimes.TL1.Asymp

/-!
# LK10_Base: pointwise facts about the κ exponential sum `fK` (shared by LK10, LK15, QK04)

* `‖G_g‖ ≤ 1`, `‖M_W‖ ≤ 1`, `‖M_W(β)‖ ≤ 1/(2W‖β‖)`;
* `‖f‖ ≤ ‖g_J‖`, `‖f‖ ≤ ‖M_W(b^m α)‖`, `‖f‖^p ≤ Π_{k∈[1,m)} T(c_k α) · K̃(b^m α)`;
* the middle bound `‖f(h/q + k/r)‖ ≤ qr/(2W)` for `(q, b r) = 1`, `(h, q) = 1`, `q ≥ 2`;
* the shape `20 m ≤ 7(2N+1) < 20(m + 1)`, `ℓ + 2m = 2N + 1`, `m_M(4) ≤ 1/W`.
-/

namespace KappaOmega2

open Finset Real Palprimes

lemma LK10_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma LK10_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) : ‖Gg b g t‖ ≤ 1 := by
  unfold Gg
  calc ‖∑ a ∈ range b, (g a : ℂ) * ee (a * t)‖ ≤ ∑ a ∈ range b, ‖(g a : ℂ) * ee (a * t)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ range b, g a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, LK10_norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.1 a)]
    _ = 1 := hg.2

lemma LK10_Mmid_eq (W : ℕ) (β : ℝ) : ‖Mmid W β‖ = ‖dirK W β‖ / W := by
  unfold Mmid dirK
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  ring

lemma LK10_Mmid_le_one (W : ℕ) (hW : 1 ≤ W) (β : ℝ) : ‖Mmid W β‖ ≤ 1 := by
  rw [LK10_Mmid_eq]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [div_le_one hW0]
  exact norm_dirK_le_M W β

lemma LK10_Mmid_le_dist (W : ℕ) (hW : 1 ≤ W) (β : ℝ) (hβ : 0 < distZ β) :
    ‖Mmid W β‖ ≤ 1 / (2 * W * distZ β) := by
  rw [LK10_Mmid_eq]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := norm_dirK_le W β hβ
  rw [div_le_iff₀ hW0]
  calc ‖dirK W β‖ ≤ 1 / (2 * distZ β) := h
    _ = 1 / (2 * W * distZ β) * W := by field_simp

lemma LK10_shape (N : ℕ) : 20 * mK N ≤ 7 * (2 * N + 1) ∧ 7 * (2 * N + 1) < 20 * (mK N + 1) ∧
    ellK N + 2 * mK N = 2 * N + 1 := by
  unfold ellK mK
  omega

lemma LK10_mM4_le (W : ℕ) (hW : 1 ≤ W) : mM4 W ≤ 1 / (W : ℝ) := by
  unfold mM4
  have hW0 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma LK10_mM4_nonneg (W : ℕ) : 0 ≤ mM4 W := by unfold mM4; positivity

lemma LK10_mw4_nonneg (b : ℕ) (g : ℕ → ℝ) : 0 ≤ mw4 b g := by unfold mw4; positivity

lemma LK10_WK_pos (b N : ℕ) (hb : 1 ≤ b) : 1 ≤ WK b N := by
  unfold WK; exact Nat.one_le_pow _ _ (by omega)

lemma LK10_fK_le_gJK (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N j : ℕ) (hj : j ≤ mK N) (α : ℝ) :
    ‖fK b g N α‖ ≤ ‖gJK b g N j α‖ := by
  unfold fK gJK
  have hJ : Ico (mK N - j) (mK N) ⊆ range (mK N) := by
    intro k hk; simp only [mem_Ico, mem_range] at hk ⊢; omega
  rw [← Finset.prod_sdiff hJ, norm_mul, norm_mul, norm_mul]
  have h1 : ‖∏ k ∈ range (mK N) \ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => LK10_Gg_norm_le b g hg _)
  have h2 : 0 ≤ ‖∏ k ∈ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)‖ *
      ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖ := by positivity
  calc _ = ‖∏ k ∈ range (mK N) \ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)‖ *
        (‖∏ k ∈ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)‖ *
          ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖) := by ring
    _ ≤ 1 * (‖∏ k ∈ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)‖ *
          ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖) := mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

lemma LK10_fK_le_Mmid (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N : ℕ) (α : ℝ) :
    ‖fK b g N α‖ ≤ ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖ := by
  have h := LK10_fK_le_gJK b g hg N 0 (Nat.zero_le _) α
  unfold gJK at h
  simpa using h

lemma LK10_fK_le_one (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (hb : 1 ≤ b) (N : ℕ) (α : ℝ) :
    ‖fK b g N α‖ ≤ 1 :=
  (LK10_fK_le_Mmid b g hg N α).trans (LK10_Mmid_le_one _ (LK10_WK_pos b N hb) _)

/-- `‖f‖^p ≤ Π_{k∈[1,m)} T(c_k α) · K̃(b^m α)` (position 0 bounded by 1). -/
lemma LK10_fKp_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp : 0 < p) (H : ℕ)
    (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (S : ℕ) (κ : ℕ → ℝ) (N : ℕ)
    (hK : ∀ β : ℝ, ‖Mmid (WK b N) β‖ ^ p ≤ trigEval S κ β) (hm : 1 ≤ mK N) (α : ℝ) :
    ‖fK b g N α‖ ^ p ≤ (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ mK N * α) := by
  unfold fK
  rw [norm_mul, norm_prod, Real.mul_rpow (by positivity) (norm_nonneg _),
    ← Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _)]
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
  have h0 : ‖Gg b g ((cK b N 0 : ℝ) * α)‖ ^ p ≤ 1 :=
    Real.rpow_le_one (norm_nonneg _) (LK10_Gg_norm_le b g hg _) hp.le
  have hP0 : 0 ≤ ∏ k ∈ Ico (0 + 1) (mK N), ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p :=
    Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hP : ∏ k ∈ Ico (0 + 1) (mK N), ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p ≤
      ∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α) :=
    Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ _ => hT _)
  have hM := hK ((b : ℝ) ^ mK N * α)
  have hM0 : 0 ≤ ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  calc ‖Gg b g ((cK b N 0 : ℝ) * α)‖ ^ p *
        (∏ k ∈ Ico (0 + 1) (mK N), ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p) *
          ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖ ^ p
      ≤ 1 * (∏ k ∈ Ico (0 + 1) (mK N), ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p) *
          ‖Mmid (WK b N) ((b : ℝ) ^ mK N * α)‖ ^ p := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact mul_le_mul_of_nonneg_right h0 hP0
    _ ≤ _ := by
        rw [one_mul]
        exact mul_le_mul hP hM hM0 ((hP0.trans hP))

/-- Middle bound: `‖f(h/q + k/r)‖ ≤ qr/(2W)` for `q ≥ 2` coprime to `b` and `r`, `(h, q) = 1`. -/
lemma LK10_mid (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (hb : 1 ≤ b) (N q h k r : ℕ) (hq : 2 ≤ q)
    (hqb : Nat.Coprime q b) (hqr : Nat.Coprime q r) (hr : 1 ≤ r) (hh : Nat.Coprime h q) :
    ‖fK b g N ((h : ℝ) / q + (k : ℝ) / (r : ℝ))‖ ≤ (q : ℝ) * r / (2 * (WK b N : ℝ)) := by
  have hW := LK10_WK_pos b N hb
  have hW0 : (0 : ℝ) < WK b N := by exact_mod_cast hW
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set n : ℕ := b ^ mK N * (h * r + k * q) with hn
  have hα : (b : ℝ) ^ mK N * ((h : ℝ) / q + (k : ℝ) / (r : ℝ)) = ((n : ℤ) : ℝ) / ((q * r : ℕ) : ℝ) := by
    rw [hn]; push_cast; field_simp
  have hnd : ¬ ((q * r : ℕ) : ℤ) ∣ (n : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hd
    have h1 : q ∣ n := dvd_trans (dvd_mul_right q r) hd
    have h2 : q ∣ b ^ mK N * h * r := by
      have e : n = b ^ mK N * h * r + q * (b ^ mK N * k) := by rw [hn]; ring
      rw [e] at h1
      exact (Nat.dvd_add_left (dvd_mul_right q _)).1 h1
    have hc : Nat.Coprime q (b ^ mK N * h * r) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hqb) hh.symm) hqr
    have := Nat.Coprime.eq_one_of_dvd hc h2
    omega
  have hqr0 : 0 < q * r := by positivity
  have hd := distZ_div_ge (n : ℤ) (q * r) hqr0 hnd
  have hdpos : 0 < distZ (((n : ℤ) : ℝ) / ((q * r : ℕ) : ℝ)) :=
    lt_of_lt_of_le (by positivity) hd
  calc ‖fK b g N ((h : ℝ) / q + (k : ℝ) / (r : ℝ))‖
      ≤ ‖Mmid (WK b N) ((b : ℝ) ^ mK N * ((h : ℝ) / q + (k : ℝ) / (r : ℝ)))‖ := LK10_fK_le_Mmid b g hg N _
    _ ≤ 1 / (2 * (WK b N : ℝ) * distZ (((n : ℤ) : ℝ) / ((q * r : ℕ) : ℝ))) := by
        rw [hα]; exact LK10_Mmid_le_dist _ hW _ hdpos
    _ ≤ 1 / (2 * (WK b N : ℝ) * (1 / ((q * r : ℕ) : ℝ))) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (q : ℝ) * r / (2 * (WK b N : ℝ)) := by push_cast; field_simp

/-- `b^n = exp(n log b)`. -/
lemma LK10_pow_exp (b : ℕ) (hb : 1 ≤ b) (n : ℕ) : (b : ℝ) ^ n = Real.exp (n * Real.log b) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.exp_natCast_mul, Real.exp_log hb0]

/-- `x = exp((2N+1) log b)`. -/
lemma LK10_xx_exp (b N : ℕ) (hb : 1 ≤ b) : xx b N = Real.exp ((2 * (N : ℝ) + 1) * Real.log b) := by
  unfold xx
  rw [LK10_pow_exp b hb]; push_cast; ring_nf

lemma LK10_xx_rpow (b N : ℕ) (hb : 1 ≤ b) (a : ℝ) :
    xx b N ^ a = Real.exp ((2 * (N : ℝ) + 1) * Real.log b * a) := by
  rw [LK10_xx_exp b N hb, ← Real.exp_mul]

/-- `1 + y ≤ exp(c y)/c` for `0 < c ≤ 1`, `y ≥ 0`. -/
lemma LK10_one_add_le (c y : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hy : 0 ≤ y) :
    1 + y ≤ Real.exp (c * y) / c := by
  rw [le_div_iff₀ hc]
  have h := Real.add_one_le_exp (c * y)
  nlinarith

end KappaOmega2
