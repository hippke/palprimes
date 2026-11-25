import Omega3.Statements
import Palprimes.TL1.Asymp

/-!
# L10: Proposition C_w with the cut A₁ only (r238 §2.7). Sub-blueprint: `L10_PLAN.md`.
-/

namespace Omega3

open Finset Real Palprimes

lemma L10_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma L10_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) : ‖Gg b g t‖ ≤ 1 := by
  unfold Gg
  calc ‖∑ a ∈ range b, (g a : ℂ) * ee (a * t)‖ ≤ ∑ a ∈ range b, ‖(g a : ℂ) * ee (a * t)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ range b, g a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, L10_norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.1 a)]
    _ = 1 := hg.2

/-- `Σ_s (g ∗ g)(s) = (Σ g)²`. -/
lemma L10_conv_total (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) :
    ∑ s ∈ range (2 * b - 1), (∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0) =
      ∑ i ∈ range b, g i * ∑ k ∈ range b, g k := by
  set n := 2 * b - 1 with hn
  simp_rw [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm]
  have hin : ∀ i ∈ Ico 0 n, (∑ s ∈ Ico i n, if i < b ∧ s - i < b then g i * g (s - i) else 0) =
      if i < b then g i * ∑ k ∈ Ico 0 b, g k else 0 := by
    intro i hi
    split_ifs with hib
    · rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, hib, true_and]
      rw [← Finset.sum_filter, Finset.mul_sum]
      have : (range (n - i)).filter (fun k => k < b) = Ico 0 b := by
        ext k; simp only [mem_filter, mem_range, mem_Ico]; omega
      rw [this]
    · exact Finset.sum_eq_zero (fun s _ => by simp [hib])
  rw [Finset.sum_congr rfl hin, ← Finset.sum_filter]
  have : (Ico 0 n).filter (fun i => i < b) = Ico 0 b := by
    ext k; simp only [mem_filter, mem_Ico]; omega
  rw [this]

/-- `m_w(4) ≥ 1/(2b − 1)` (Cauchy–Schwarz). -/
lemma L10_mw4_lower (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) (hg : IsDigitWeight b g) :
    1 ≤ (2 * (b : ℝ) - 1) * mw4 b g := by
  have h := sq_sum_le_card_mul_sum_sq (s := range (2 * b - 1))
    (f := fun s => ∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0)
  rw [L10_conv_total b hb g, ← Finset.sum_mul, hg.2, one_mul, one_pow, card_range] at h
  unfold mw4
  have hc : ((2 * b - 1 : ℕ) : ℝ) = 2 * (b : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hc] at h
  exact h

lemma L10_thw_lt_one (b : ℕ) (hb : 2 ≤ b) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (θw : ℝ)
    (hm4 : mw4 b g ≤ (b : ℝ) ^ (-(1 + θw))) : θw < 1 := by
  by_contra hcon
  push Not at hcon
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 := L10_mw4_lower b (by omega) g hg
  have h2 : (b : ℝ) ^ (-(1 + θw)) ≤ (b : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hb1.le (by linarith)
  have h3 : (b : ℝ) ^ (-2 : ℝ) = 1 / (b : ℝ) ^ 2 := by
    rw [Real.rpow_neg (by linarith), one_div]; norm_cast
  have hpos : 0 < 2 * (b : ℝ) - 1 := by linarith
  have h4 : (2 * (b : ℝ) - 1) * mw4 b g ≤ (2 * (b : ℝ) - 1) * (1 / (b : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  have h5 : (2 * (b : ℝ) - 1) * (1 / (b : ℝ) ^ 2) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; nlinarith
  linarith

lemma L10_F_le_G (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ range (N + 1)) (α : ℝ) : ‖fg b g N α‖ ≤ ‖gJ b g N J α‖ := by
  unfold fg gJ
  rw [← Finset.prod_sdiff hJ, norm_mul]
  have h1 : ‖∏ k ∈ range (N + 1) \ J, Gg b g ((cK b N k : ℝ) * α)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => L10_Gg_norm_le b g hg _)
  calc _ ≤ 1 * ‖∏ k ∈ J, Gg b g ((cK b N k : ℝ) * α)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

lemma L10_Fp_le_TK (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp : 0 < p) (H : ℕ)
    (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (N : ℕ) (α : ℝ) :
    ‖fg b g N α‖ ^ p ≤ ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * α) := by
  unfold fg
  rw [norm_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _), Finset.prod_range_succ]
  have h1 : ‖Gg b g ((cK b N N : ℝ) * α)‖ ^ p ≤ 1 :=
    Real.rpow_le_one (norm_nonneg _) (L10_Gg_norm_le b g hg _) hp.le
  have h0 : 0 ≤ ∏ k ∈ range N, ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p :=
    Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  calc _ ≤ (∏ k ∈ range N, ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p) * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = ∏ k ∈ range N, ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p := mul_one _
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ _ => hT _)

lemma L10_exp1 (p θw δ κ ℓ ψ θ lb : ℝ) (N : ℕ) (hℓ : ℓ = (2 * (N : ℝ) + 1) * lb) (hp0 : 0 < p) (hp1 : p < 1)
    (hθw : 0 < θw) (hθw1 : θw < 1) (hδ : δ ≤ ℓ * θ) (hℓ0 : 0 ≤ ℓ)
    (hii : 2 * θ + 2 * κ < ψ + (1 - p) * (2 * θ * θw - 2 * κ) / 3) :
    (-(θw * δ) / 3 + κ * ℓ / 3) * (1 - p) + 2 * δ + N * (lb * (-ψ)) ≤ ψ * lb / 2 + (δ - κ * ℓ) := by
  have he1 : 0 ≤ 1 - (1 - p) * θw / 3 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hδ he1
  have h2 := mul_nonneg hℓ0 (sub_nonneg.2 hii.le)
  subst hℓ
  nlinarith

lemma L10_exp2 (p θw δ κ ℓ lA θ₀ lb ε : ℝ) (N : ℕ) (hℓ : ℓ = (2 * (N : ℝ) + 1) * lb) (hp1 : p < 1)
    (hθw : 0 < θw) (hδ : ℓ * θ₀ < δ) (hℓ0 : 0 ≤ ℓ)
    (hiii : lA + 2 * κ < (1 - p) * (2 * θ₀ * θw - 2 * κ) / 3) :
    (-(θw * δ) / 3 + κ * ℓ / 3) * (1 - p) + δ + ℓ * (ε / 2) + N * (lb * lA) ≤
      -(lA * lb) / 2 + (δ - κ * ℓ + ℓ * (ε / 2)) := by
  have hpt : 0 ≤ (1 - p) * θw := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hδ.le hpt
  have h2 := mul_nonneg hℓ0 (sub_nonneg.2 hiii.le)
  subst hℓ
  nlinarith

lemma L10_exp3 (θw δ κ ℓ lb : ℝ) (j : ℕ) (hθw : 0 < θw) (hδ : δ < ((j : ℝ) + 1) * lb) :
    3 * -(-(θw * δ) / 3 + κ * ℓ / 3) + 2 * δ + j * (lb * (-(1 + θw))) ≤ (1 + θw) * lb + (δ - κ * ℓ) := by
  have h1 := mul_le_mul_of_nonneg_left hδ.le (by linarith : (0 : ℝ) ≤ 1 + θw)
  nlinarith

set_option maxHeartbeats 1000000 in
theorem itemL10 : ItemL10 := by
  intro b g p H τ ψ lA θw θ κ θ₀ hb hg hp0 hp1 hH hT hτ0 hτψ hA hm4 hθw hκ hθ₀ hθ₀θ hθ hii hiii h28 h29 ε hε
  classical
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set lb := Real.log b with hlbdef
  have hlb : 0 < lb := Real.log_pos hb1
  have hθw1 := L10_thw_lt_one b hb2 g hg θw hm4
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow (ε / 2) (by positivity)
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl; simp at this; linarith
  set C1 : ℝ := 2 * Real.exp (ψ * lb / 2) with hC1
  set C2 : ℝ := 2 * Ce * (4 * (b : ℝ)) ^ (ε / 2) * Real.exp (-(lA * lb) / 2) with hC2
  set C3 : ℝ := (24 + 12 * (b : ℝ)) * Real.exp ((1 + θw) * lb) with hC3
  have hr : (1 : ℝ) < Real.exp (lb * (ε / 2)) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by positivity)
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt (C1 + C2 + C3) hr
  refine ⟨max n₁ ⌈1 / θ₀⌉₊, ?_⟩
  intro N hN D hdy hDlo hDhi β
  have hNn₁ : n₁ ≤ N := le_trans (le_max_left _ _) hN
  have hNθ : 1 / θ₀ ≤ (N : ℝ) := by
    have h1 : 1 / θ₀ ≤ (⌈1 / θ₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / θ₀⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
    linarith
  set ℓ : ℝ := (2 * (N : ℝ) + 1) * lb with hℓ
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hx : xx b N = Real.exp ℓ := by
    unfold xx
    rw [hℓ, show (2 * (N : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_natCast_mul,
      Real.exp_log hb0]
  have hxr : ∀ a : ℝ, xx b N ^ a = Real.exp (ℓ * a) := by
    intro a; rw [hx, ← Real.exp_mul]
  have hD1 : 1 ≤ D := by obtain ⟨k, rfl⟩ := hdy; exact Nat.one_le_two_pow
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  set δ := Real.log D with hδdef
  have hDe : (D : ℝ) = Real.exp δ := (Real.exp_log hDpos).symm
  have hδhi : δ ≤ ℓ * θ := by
    have h := hDhi; rw [hxr, hDe] at h; exact Real.exp_le_exp.1 h
  have hδlo : ℓ * θ₀ < δ := by
    have h := hDlo; rw [hxr, hDe] at h; exact Real.exp_lt_exp.1 h
  have hbe : ∀ n : ℕ, (b : ℝ) ^ n = Real.exp (n * lb) := by
    intro n; rw [Real.exp_natCast_mul, Real.exp_log hb0]
  -- b ≤ D
  have hbD : b ≤ D := by
    have h1 : lb ≤ ℓ * θ₀ := by
      have : 1 ≤ (N : ℝ) * θ₀ := by rwa [div_le_iff₀ hθ₀] at hNθ
      have h2 : 1 ≤ (2 * (N : ℝ) + 1) * θ₀ := by linarith
      rw [hℓ, show (2 * (N : ℝ) + 1) * lb * θ₀ = lb * ((2 * (N : ℝ) + 1) * θ₀) by ring]
      exact le_mul_of_one_le_right hlb.le h2
    have : (b : ℝ) < D := by
      rw [hDe, ← Real.exp_log hb0]; exact Real.exp_lt_exp.2 (by linarith)
    exact_mod_cast this.le
  set j := Nat.log b D with hjdef
  have hj1 : 1 ≤ j := Nat.log_pos (by omega) hbD
  have hbj : b ^ j ≤ D := Nat.pow_log_le_self b (by omega)
  have hbj1 : D < b ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) D
  have hjN : j ≤ N := by
    have h1 : (D : ℝ) < (b : ℝ) ^ (N + 1) := by
      rw [hbe, hDe]
      apply Real.exp_lt_exp.2
      have : ℓ * θ < ((N + 1 : ℕ) : ℝ) * lb := by
        have h3 : (2 * (N : ℝ) + 1) * θ < (2 * (N : ℝ) + 1) * (1 / 2) :=
          mul_lt_mul_of_pos_left hθ (by positivity)
        have h4 : (2 * (N : ℝ) + 1) * θ < (N : ℝ) + 1 := by linarith
        rw [hℓ, show (2 * (N : ℝ) + 1) * lb * θ = ((2 * (N : ℝ) + 1) * θ) * lb by ring]
        push_cast
        exact mul_lt_mul_of_pos_right h4 hlb
      linarith
    have h2 : b ^ j < b ^ (N + 1) := lt_of_le_of_lt hbj (by exact_mod_cast h1)
    by_contra hcon
    have : b ^ (N + 1) ≤ b ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hδj : δ < ((j : ℝ) + 1) * lb := by
    have h1 : (D : ℝ) < (b : ℝ) ^ (j + 1) := by exact_mod_cast hbj1
    rw [hbe, hDe] at h1
    have := Real.exp_lt_exp.1 h1
    push_cast at this; linarith
  have hbjD : (b : ℝ) ^ j ≤ D := by exact_mod_cast hbj
  -- the block
  set Qs := (Ico D (2 * D)).filter (fun d => Nat.Coprime d b) with hQs
  set J := Ico (N - j) N with hJdef
  have hJ : J ⊆ range (N + 1) := by
    intro k hk; simp only [hJdef, mem_Ico, mem_range] at hk ⊢; omega
  set τs : ℝ := Real.exp (-(θw * δ) / 3 + κ * ℓ / 3) with hτsdef
  have hτs : 0 < τs := Real.exp_pos _
  have hTK0 : ∀ α : ℝ, 0 ≤ ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * α) := fun α =>
    (Real.rpow_nonneg (norm_nonneg _) p).trans (L10_Fp_le_TK b g hg p hp0 H τ hT N α)
  have hpt : ∀ α : ℝ, ‖fg b g N α‖ ≤ τs ^ (1 - p) * ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * α) +
      τs⁻¹ ^ 3 * ‖gJ b g N J α‖ ^ 4 := fun α =>
    cut_pointwise _ _ _ _ _ (norm_nonneg _) (L10_F_le_G b g hg N J hJ α) hτs hp0 hp1.le
      (L10_Fp_le_TK b g hg p hp0 H τ hT N α)
  have hblock : blockL1 b g N D β ≤
      τs ^ (1 - p) * (∑ q ∈ Qs, ∑ h ∈ range q,
        ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) +
      τs⁻¹ ^ 3 * (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJ b g N J ((h : ℝ) / d + β)‖ ^ 4) := by
    unfold blockL1 L1farey
    rw [← hQs]
    calc _ ≤ ∑ d ∈ Qs, ∑ h ∈ redRes d, (τs ^ (1 - p) *
            ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β)) +
            τs⁻¹ ^ 3 * ‖gJ b g N J ((h : ℝ) / d + β)‖ ^ 4) :=
          Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun h _ => hpt _))
      _ = τs ^ (1 - p) * (∑ d ∈ Qs, ∑ h ∈ redRes d,
            ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β))) +
          τs⁻¹ ^ 3 * (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJ b g N J ((h : ℝ) / d + β)‖ ^ 4) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
          have h1 : (∑ d ∈ Qs, ∑ h ∈ redRes d,
              ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β))) ≤
              ∑ d ∈ Qs, ∑ h ∈ range d,
              ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / d + β)) :=
            Finset.sum_le_sum (fun d _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => hTK0 _))
          have hτp : 0 ≤ τs ^ (1 - p) := Real.rpow_nonneg hτs.le _
          exact add_le_add (mul_le_mul_of_nonneg_left h1 hτp) le_rfl
  -- Lemma 2.8
  have hQpos : ∀ q ∈ Qs, 1 ≤ q := by
    intro q hq; simp only [hQs, mem_filter, mem_Ico] at hq; omega
  set Td : ℝ := Ce * (4 * (b : ℝ) * xx b N) ^ (ε / 2) with hTddef
  have hTd : ∀ w : ℤ, w ≠ 0 → |w| ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) →
      ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)).card : ℝ) ≤ Td := by
    intro w hw hwle
    have h1 := card_filter_dvd_le_divisors Qs (fun q hq => hQpos q hq) w hw
    have h2 := hCe w.natAbs (Int.natAbs_pos.2 hw)
    have h3 : (w.natAbs : ℝ) ≤ 4 * (b : ℝ) * xx b N := by
      have h3' : ((w.natAbs : ℤ) : ℝ) ≤ ((2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) : ℤ) : ℝ) := by
        rw [Int.natCast_natAbs]; exact_mod_cast hwle
      have hH' : (H : ℝ) ≤ 2 * b := by exact_mod_cast (by omega : H ≤ 2 * b)
      rw [Int.cast_natCast] at h3'
      push_cast at h3'
      unfold xx
      have hpow : (0 : ℝ) ≤ (b : ℝ) ^ (2 * N + 1) := by positivity
      calc (w.natAbs : ℝ) ≤ 2 * (H : ℝ) * (b : ℝ) ^ (2 * N + 1) := h3'
        _ ≤ 4 * (b : ℝ) * (b : ℝ) ^ (2 * N + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hpow
    calc ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)).card : ℝ) ≤ (#(w.natAbs.divisors) : ℝ) := by
          exact_mod_cast h1
      _ ≤ Ce * (w.natAbs : ℝ) ^ (ε / 2) := h2
      _ ≤ Td := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) h3 (by positivity)) hCe0
  have hTd0 : 0 ≤ Td := mul_nonneg hCe0 (Real.rpow_nonneg (by unfold xx; positivity) _)
  have hL28 := h28 b H N τ (range N) Qs β Td hb2 hH (subset_refl _) hQpos hTd0 hTd
  rw [card_range] at hL28
  have hL29 := h29 b g N j D β hb2 hg.1 hj1 hjN hD1
  -- size bounds
  have hcardQ : (#Qs : ℝ) ≤ D := by
    have : #Qs ≤ D := by
      calc #Qs ≤ #(Ico D (2 * D)) := Finset.card_filter_le _ _
        _ = D := by rw [Nat.card_Ico]; omega
    exact_mod_cast this
  have hsumq : (∑ q ∈ Qs, (q : ℝ)) ≤ 2 * (D : ℝ) ^ 2 := by
    calc (∑ q ∈ Qs, (q : ℝ)) ≤ ∑ _q ∈ Qs, (2 * (D : ℝ)) := by
          apply Finset.sum_le_sum; intro q hq
          simp only [hQs, mem_filter, mem_Ico] at hq
          exact_mod_cast hq.1.2.le
      _ = #Qs * (2 * (D : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * (2 * (D : ℝ)) := mul_le_mul_of_nonneg_right hcardQ (by positivity)
      _ = 2 * (D : ℝ) ^ 2 := by ring
  have hsup : ((Qs.sup id : ℕ) : ℝ) ≤ 2 * D := by
    have : Qs.sup id ≤ 2 * D := Finset.sup_le (fun q hq => by
      simp only [hQs, mem_filter, mem_Ico] at hq; simp only [id]; omega)
    exact_mod_cast this
  have hτN : τ 0 ^ N ≤ Real.exp (N * (lb * (-ψ))) := by
    rw [Real.exp_natCast_mul, ← Real.rpow_def_of_pos hb0]
    exact pow_le_pow_left₀ hτ0.le hτψ N
  have hA0 : 0 ≤ trigMass H τ := by unfold trigMass; positivity
  have hAN : trigMass H τ ^ N ≤ Real.exp (N * (lb * lA)) := by
    rw [Real.exp_natCast_mul, ← Real.rpow_def_of_pos hb0]
    exact pow_le_pow_left₀ hA0 hA N
  have hm0 : 0 ≤ mw4 b g := by unfold mw4; positivity
  have hmN : mw4 b g ^ j ≤ Real.exp (j * (lb * (-(1 + θw)))) := by
    rw [Real.exp_natCast_mul, ← Real.rpow_def_of_pos hb0]
    exact pow_le_pow_left₀ hm0 hm4 j
  have h4D : 6 * (4 * (D : ℝ) ^ 2 + 2 * b * (b : ℝ) ^ (2 * j)) ≤ (24 + 12 * (b : ℝ)) * (D : ℝ) ^ 2 := by
    have : (b : ℝ) ^ (2 * j) ≤ (D : ℝ) ^ 2 := by
      rw [pow_mul']; exact pow_le_pow_left₀ (by positivity) hbjD 2
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * b)
    linarith
  have hS : (∑ q ∈ Qs, ∑ h ∈ range q,
        ∏ k ∈ range N, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) ≤
      2 * (D : ℝ) ^ 2 * Real.exp (N * (lb * (-ψ))) + 2 * D * Td * Real.exp (N * (lb * lA)) := by
    refine hL28.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hsumq hτN (pow_nonneg hτ0.le _) (by positivity)
    · exact mul_le_mul (mul_le_mul_of_nonneg_right hsup hTd0) hAN (pow_nonneg hA0 _) (by positivity)
  have hG : (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJ b g N J ((h : ℝ) / d + β)‖ ^ 4) ≤
      (24 + 12 * (b : ℝ)) * (D : ℝ) ^ 2 * Real.exp (j * (lb * (-(1 + θw)))) :=
    hL29.trans (mul_le_mul h4D hmN (pow_nonneg hm0 _) (by positivity))
  -- exponential forms
  have hτp : τs ^ (1 - p) = Real.exp ((-(θw * δ) / 3 + κ * ℓ / 3) * (1 - p)) := by
    rw [Real.rpow_def_of_pos hτs, hτsdef, Real.log_exp]
  have hτi : τs⁻¹ ^ 3 = Real.exp (3 * -(-(θw * δ) / 3 + κ * ℓ / 3)) := by
    rw [hτsdef, ← Real.exp_neg, ← Real.exp_natCast_mul]; norm_num
  have hD2 : (D : ℝ) ^ 2 = Real.exp (2 * δ) := by
    rw [hDe, ← Real.exp_natCast_mul]; norm_num
  have hTde : Td = Ce * (4 * (b : ℝ)) ^ (ε / 2) * Real.exp (ℓ * (ε / 2)) := by
    rw [hTddef, Real.mul_rpow (by positivity) (by unfold xx; positivity), hxr]; ring
  have hsplit : τs ^ (1 - p) * (2 * (D : ℝ) ^ 2 * Real.exp (N * (lb * (-ψ))) +
        2 * D * Td * Real.exp (N * (lb * lA))) +
      τs⁻¹ ^ 3 * ((24 + 12 * (b : ℝ)) * (D : ℝ) ^ 2 * Real.exp (j * (lb * (-(1 + θw))))) =
      2 * Real.exp ((-(θw * δ) / 3 + κ * ℓ / 3) * (1 - p) + 2 * δ + N * (lb * (-ψ))) +
      2 * Ce * (4 * (b : ℝ)) ^ (ε / 2) *
        Real.exp ((-(θw * δ) / 3 + κ * ℓ / 3) * (1 - p) + δ + ℓ * (ε / 2) + N * (lb * lA)) +
      (24 + 12 * (b : ℝ)) * Real.exp (3 * -(-(θw * δ) / 3 + κ * ℓ / 3) + 2 * δ + j * (lb * (-(1 + θw)))) := by
    rw [hτp, hτi, hD2, hTde, hDe]
    simp only [Real.exp_add]
    ring
  have e1 := Real.exp_le_exp.2 (L10_exp1 p θw δ κ ℓ ψ θ lb N hℓ hp0 hp1 hθw hθw1 hδhi hℓ0 hii)
  have e2 := Real.exp_le_exp.2 (L10_exp2 p θw δ κ ℓ lA θ₀ lb ε N hℓ hp1 hθw hδlo hℓ0 hiii)
  have e3 := Real.exp_le_exp.2 (L10_exp3 θw δ κ ℓ lb j hθw hδj)
  have hC4 : 0 ≤ Ce * (4 * (b : ℝ)) ^ (ε / 2) := by positivity
  have hmono : Real.exp (δ - κ * ℓ) ≤ Real.exp (δ - κ * ℓ + ℓ * (ε / 2)) :=
    Real.exp_le_exp.2 (by have := mul_nonneg hℓ0 (by positivity : (0 : ℝ) ≤ ε / 2); linarith)
  have hCs : C1 + C2 + C3 ≤ Real.exp (ℓ * (ε / 2)) := by
    have h1 : Real.exp (lb * (ε / 2)) ^ n₁ ≤ Real.exp (lb * (ε / 2)) ^ (2 * N + 1) :=
      pow_le_pow_right₀ hr.le (by omega)
    have h2 : Real.exp (lb * (ε / 2)) ^ (2 * N + 1) = Real.exp (ℓ * (ε / 2)) := by
      rw [← Real.exp_natCast_mul, hℓ]; push_cast; ring_nf
    linarith
  have hC10 : 0 ≤ C1 := by positivity
  have hC30 : 0 ≤ C3 := by positivity
  calc blockL1 b g N D β ≤ _ := hblock
    _ ≤ τs ^ (1 - p) * (2 * (D : ℝ) ^ 2 * Real.exp (N * (lb * (-ψ))) +
          2 * D * Td * Real.exp (N * (lb * lA))) +
        τs⁻¹ ^ 3 * ((24 + 12 * (b : ℝ)) * (D : ℝ) ^ 2 * Real.exp (j * (lb * (-(1 + θw))))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hτs.le _)
        · exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = _ := hsplit
    _ ≤ 2 * Real.exp (ψ * lb / 2 + (δ - κ * ℓ)) +
        2 * Ce * (4 * (b : ℝ)) ^ (ε / 2) * Real.exp (-(lA * lb) / 2 + (δ - κ * ℓ + ℓ * (ε / 2))) +
        (24 + 12 * (b : ℝ)) * Real.exp ((1 + θw) * lb + (δ - κ * ℓ)) := by
        have hb4 : (0 : ℝ) ≤ 24 + 12 * (b : ℝ) := by positivity
        have hC4' : 0 ≤ 2 * Ce * (4 * (b : ℝ)) ^ (ε / 2) := by positivity
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
          (mul_le_mul_of_nonneg_left e2 hC4')) (mul_le_mul_of_nonneg_left e3 hb4)
    _ = C1 * Real.exp (δ - κ * ℓ) + C2 * Real.exp (δ - κ * ℓ + ℓ * (ε / 2)) +
        C3 * Real.exp (δ - κ * ℓ) := by
        rw [hC1, hC2, hC3]; simp only [Real.exp_add]; ring
    _ ≤ (C1 + C2 + C3) * Real.exp (δ - κ * ℓ + ℓ * (ε / 2)) := by
        rw [add_mul, add_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmono hC10) le_rfl)
          (mul_le_mul_of_nonneg_left hmono hC30)
    _ ≤ Real.exp (ℓ * (ε / 2)) * Real.exp (δ - κ * ℓ + ℓ * (ε / 2)) :=
        mul_le_mul_of_nonneg_right hCs (Real.exp_pos _).le
    _ = (D : ℝ) * xx b N ^ (-κ + ε) := by
        rw [hDe, hxr, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Omega3
