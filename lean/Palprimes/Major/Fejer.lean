import Palprimes.TL1.Asymp
import Palprimes.Major.LemmaL
import Palprimes.Major.LemmaZ
import Palprimes.Major.FejerTau

/-! # TL¹ for every base `b ≥ 10` through the Fejér family (dossier §2.13)

`T_b = Σ_{M=1}^{m} (ρ ω_M / b) F_M + (1 − ρS/b) F_m`, `m = ⌊7b/10⌋`, `ρ = 201/200`, `b^p = b/ρ`,
`F_M = ψ_M` the normalised Fejér kernel, `ω₁ = 57/50`, `ω_M = 19/25`.
* `fejT_maj`: `T_b ≥ φ_b^p` on `ℝ` (Lemma Z on `|t| < 1/b`, Lemma L on `[1/b, 1/2]`);
* `fejMaj`: `T_b` as a `BlockMaj b 1`, with `A = 1` and `τ₀ = tauF b < b^{−2θ}`;
* `tl1_ge_ten`: `tl1_eventually` with `θ = 0.2608`, `δ = 0.47`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-! ## `ψ_b`: periodicity, evenness and the sine formula -/

theorem ee_intcast (k : ℤ) : ee (k : ℝ) = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * ((k : ℝ) : ℂ) = k * (2 * π * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem phiB_add_int (K : ℕ) (t : ℝ) (k : ℤ) : phiB K (t + k) = phiB K t := by
  unfold phiB; congr 1
  apply Finset.sum_congr rfl; intro d _
  rw [show (d : ℝ) * (t + k) = d * t + ((d * k : ℤ) : ℝ) by push_cast; ring, ee_add, ee_intcast, mul_one]

theorem phiB_neg (K : ℕ) (t : ℝ) : phiB K (-t) = phiB K t := by
  unfold phiB
  have : ∑ d ∈ range K, ee (d * -t) = starRingEnd ℂ (∑ d ∈ range K, ee (d * t)) := by
    rw [map_sum]; apply Finset.sum_congr rfl; intro d _; rw [conj_ee]; ring_nf
  rw [this, Complex.norm_conj]

theorem psiB_red (K : ℕ) (t : ℝ) : psiB K t = psiB K |t - round t| := by
  unfold psiB
  have h1 : phiB K t = phiB K (t - round t) := by
    have e : t = (t - round t) + ((round t : ℤ) : ℝ) := by ring
    conv_lhs => rw [e]
    exact phiB_add_int K _ _
  rw [h1]
  rcases le_total 0 (t - round t) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, phiB_neg]

theorem phiB_sin (K : ℕ) (t : ℝ) (h : Real.sin (π * t) ≠ 0) :
    phiB K t = |Real.sin (π * K * t)| / |Real.sin (π * t)| := by
  have hne : ee t ≠ 1 := by
    intro h1
    have := norm_ee_sub_one t
    rw [h1, sub_self, norm_zero] at this
    have : |Real.sin (π * t)| = 0 := by linarith
    exact h (abs_eq_zero.1 this)
  unfold phiB
  simp_rw [ee_pow]
  rw [geom_sum_eq hne, norm_div, ← ee_pow, norm_ee_sub_one, norm_ee_sub_one, mul_assoc π]
  have : |Real.sin (π * t)| ≠ 0 := abs_ne_zero.2 h
  field_simp

theorem psiB_sin (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (h : Real.sin (π * t) ≠ 0) :
    psiB K t = (Real.sin (π * K * t) / (K * Real.sin (π * t))) ^ 2 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  unfold psiB
  rw [phiB_sin K t h, div_pow, div_pow, div_pow, sq_abs, sq_abs, mul_pow]
  field_simp

theorem psiB_zero (K : ℕ) (hK : 1 ≤ K) : psiB K 0 = 1 := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  unfold psiB; rw [phiB_zero, div_self hK', one_pow]

/-! ## The family -/

noncomputable def rhoF : ℝ := 201 / 200

noncomputable def SB (b : ℕ) : ℝ := ∑ M ∈ range (mB b), omg (M + 1)

noncomputable def wt (b k : ℕ) : ℝ :=
  rhoF * omg k / b + if k = mB b then 1 - rhoF * SB b / b else 0

noncomputable def pB (b : ℕ) : ℝ := 1 - Real.log rhoF / Real.log b

noncomputable def fejT (b : ℕ) (t : ℝ) : ℝ := ∑ M ∈ range (mB b), wt b (M + 1) * psiB (M + 1) t

theorem sum_omg (m : ℕ) (hm : 1 ≤ m) : ∑ M ∈ range m, omg (M + 1) = 19 * (2 * m + 1) / 50 := by
  induction m, hm using Nat.le_induction with
  | base => simp [omg]; norm_num
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih]
    have : m + 1 ≠ 1 := by omega
    simp only [omg, this, ite_false]; push_cast; ring

theorem sum_omg_div (m : ℕ) (hm : 1 ≤ m) :
    ∑ M ∈ range m, omg (M + 1) / ((M : ℝ) + 1) = 19 / 50 + 19 / 25 * Hm m := by
  induction m, hm using Nat.le_induction with
  | base => simp [omg, Hm]; norm_num
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Hm, Finset.sum_range_succ]
    have : m + 1 ≠ 1 := by omega
    simp only [omg, this, ite_false]; ring

theorem rho_SB_le (b : ℕ) (hb : 10 ≤ b) : rhoF * SB b / b ≤ 1 := by
  have hm := mB_ge b hb
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb' : (10 : ℝ) ≤ b := by exact_mod_cast hb
  have h7 : ((10 * mB b : ℕ) : ℝ) ≤ ((7 * b : ℕ) : ℝ) := by exact_mod_cast (by unfold mB; omega)
  push_cast at h7
  rw [SB, sum_omg _ (by omega), rhoF, div_le_one hb0]
  nlinarith

theorem wt_ge (b k : ℕ) (hb : 10 ≤ b) : rhoF * omg k / b ≤ wt b k := by
  unfold wt
  have := rho_SB_le b hb
  split_ifs <;> linarith

theorem wt_nonneg (b k : ℕ) (hb : 10 ≤ b) : 0 ≤ wt b k := by
  refine le_trans ?_ (wt_ge b k hb)
  have := omg_pos k
  unfold rhoF; positivity

/-- `Σ_{M<m} (if M+1 = m then c else 0) g(M+1) = c g(m)`. -/
theorem sum_ite_last (m : ℕ) (hm : 1 ≤ m) (c : ℝ) (g : ℕ → ℝ) :
    ∑ M ∈ range m, (if M + 1 = m then c else 0) * g (M + 1) = c * g m := by
  rw [Finset.sum_eq_single (m - 1)]
  · rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h), show m - 1 + 1 = m by omega]
  · intro M _ hM; rw [ite_eq_right_iff.2 (fun h => absurd (by omega) hM), zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- `Σ_M wt(M+1) g(M+1) = (ρ/b) Σ ω g + (1 − ρS/b) g(m)`. -/
theorem sum_wt_mul (b : ℕ) (hb : 10 ≤ b) (g : ℕ → ℝ) :
    ∑ M ∈ range (mB b), wt b (M + 1) * g (M + 1) =
      rhoF / b * ∑ M ∈ range (mB b), omg (M + 1) * g (M + 1) + (1 - rhoF * SB b / b) * g (mB b) := by
  have hm := mB_ge b hb
  rw [← sum_ite_last (mB b) (by omega), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro M _
  unfold wt; ring

theorem sum_wt (b : ℕ) (hb : 10 ≤ b) : ∑ M ∈ range (mB b), wt b (M + 1) = 1 := by
  have h := sum_wt_mul b hb (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← SB]; ring

theorem log_ten_ge : (1 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

theorem logb_pos' (b : ℕ) (hb : 10 ≤ b) : 1 ≤ Real.log b := by
  refine le_trans log_ten_ge (Real.log_le_log (by norm_num) (by exact_mod_cast hb))

theorem log_rho_pos : 0 < Real.log rhoF := Real.log_pos (by norm_num [rhoF])

theorem log_rho_le : Real.log rhoF ≤ 1 / 200 := by
  have := Real.log_le_sub_one_of_pos (by norm_num [rhoF] : (0 : ℝ) < rhoF)
  unfold rhoF at *; linarith

theorem pB_ge (b : ℕ) (hb : 10 ≤ b) : 98 / 100 ≤ pB b := by
  have h1 := logb_pos' b hb
  have : Real.log rhoF / Real.log b ≤ 1 / 200 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [log_rho_le, log_rho_pos]
  unfold pB; linarith

theorem pB_lt (b : ℕ) (hb : 10 ≤ b) : pB b < 1 := by
  have h1 := logb_pos' b hb
  have : 0 < Real.log rhoF / Real.log b := div_pos log_rho_pos (by linarith)
  unfold pB; linarith

theorem rpow_one_sub_pB (b : ℕ) (hb : 10 ≤ b) : (b : ℝ) ^ (1 - pB b) = rhoF := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have h1 := logb_pos' b hb
  rw [show 1 - pB b = Real.log rhoF / Real.log b by unfold pB; ring, Real.rpow_def_of_pos hb0]
  rw [mul_div_cancel₀ _ (by linarith), Real.exp_log (by norm_num [rhoF])]

/-! ## The majorant inequality -/

theorem fejT_red (b : ℕ) (t : ℝ) : fejT b t = fejT b |t - round t| := by
  unfold fejT; apply Finset.sum_congr rfl; intro M _; rw [psiB_red]

theorem fejT_maj (b : ℕ) (hb : 10 ≤ b) (t : ℝ) : Real.sqrt (psiB b t) ^ pB b ≤ fejT b t := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hm := mB_ge b hb
  have hp0 : 0 < pB b := by linarith [pB_ge b hb]
  have hp1 := (pB_lt b hb).le
  rw [psiB_red, fejT_red]
  set u := |t - round t| with hu
  have hu0 : 0 ≤ u := abs_nonneg _
  have hu1 : u ≤ 1 / 2 := abs_sub_round t
  rcases hu0.eq_or_lt with h0 | h0
  · -- `u = 0`
    rw [← h0, psiB_zero b (by omega), Real.sqrt_one, Real.one_rpow]
    unfold fejT
    rw [← sum_wt b hb]
    apply le_of_eq; apply Finset.sum_congr rfl; intro M _
    rw [psiB_zero _ (by omega), mul_one]
  have hsin : 0 < Real.sin (π * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsqrt : Real.sqrt (psiB b u) = |Real.sin (π * b * u)| / (b * Real.sin (π * u)) := by
    rw [psiB_sin b (by omega) u hsin.ne', Real.sqrt_sq_eq_abs, abs_div, abs_mul, abs_of_pos hb0,
      abs_of_pos hsin]
  rcases lt_or_ge ((b : ℝ) * u) 1 with hbu | hbu
  · -- Lemma Z
    have hsb : 0 < Real.sin (π * b * u) := by
      rw [mul_assoc]
      exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    rw [hsqrt, abs_of_pos hsb]
    have hZ : ∀ M ∈ range (mB b), (Real.sin (π * b * u) / (b * Real.sin (π * u))) ^ pB b ≤ psiB (M + 1) u := by
      intro M hM
      rw [Finset.mem_range] at hM
      rw [psiB_sin (M + 1) (by omega) u hsin.ne']
      apply lemmaZ b (M + 1) (pB b) hp0 hp1 (by omega) _ u h0 hbu
      have h1 : ((10 * (M + 1) : ℕ) : ℝ) ≤ ((7 * b : ℕ) : ℝ) := by
        exact_mod_cast (by unfold mB at hM; omega)
      push_cast at h1 ⊢
      have hp := pB_ge b hb
      nlinarith
    unfold fejT
    calc (Real.sin (π * b * u) / (b * Real.sin (π * u))) ^ pB b
        = ∑ M ∈ range (mB b), wt b (M + 1) * (Real.sin (π * b * u) / (b * Real.sin (π * u))) ^ pB b := by
          rw [← Finset.sum_mul, sum_wt b hb, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun M hM => mul_le_mul_of_nonneg_left (hZ M hM) (wt_nonneg b _ hb))
  · -- Lemma L
    have hm1 : 7 / 10 < ((mB b : ℝ) + 1) * u := by
      have h1 : ((7 * b : ℕ) : ℝ) < ((10 * (mB b + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by unfold mB; omega)
      push_cast at h1
      nlinarith
    have hL := lemmaL u h0 hu1 (mB b) hm1
    set X := 1 / (b * Real.sin (π * u)) with hX
    have hY : 0 < (b : ℝ) * Real.sin (π * u) := by positivity
    -- `T ≥ ρ X`
    have hT : rhoF * X ≤ fejT b u := by
      unfold fejT
      have h1 : ∑ M ∈ range (mB b), rhoF * omg (M + 1) / b * psiB (M + 1) u ≤
          ∑ M ∈ range (mB b), wt b (M + 1) * psiB (M + 1) u :=
        Finset.sum_le_sum (fun M _ => mul_le_mul_of_nonneg_right (wt_ge b _ hb)
          (by unfold psiB; positivity))
      refine le_trans ?_ h1
      have h2 : ∑ M ∈ range (mB b), rhoF * omg (M + 1) / b * psiB (M + 1) u =
          rhoF / (b * Real.sin (π * u) ^ 2) * LamS (mB b) u := by
        unfold LamS lamTerm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro M _
        rw [psiB_sin (M + 1) (by omega) u hsin.ne']
        have : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [h2, hX]
      rw [show rhoF / (b * Real.sin (π * u) ^ 2) * LamS (mB b) u =
          rhoF / (b * Real.sin (π * u)) * (LamS (mB b) u / Real.sin (π * u)) by field_simp]
      rw [mul_one_div]
      apply le_mul_of_one_le_right (by unfold rhoF; positivity)
      rw [le_div_iff₀ hsin]; linarith
    -- `φ^p ≤ X^p ≤ ρ X`
    have h1 : Real.sqrt (psiB b u) ≤ X := by
      rw [hsqrt, hX]
      apply div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hY.le
    have h2 : X ^ pB b ≤ rhoF * X := by
      have hXY : X = ((b : ℝ) * Real.sin (π * u))⁻¹ := by rw [hX, one_div]
      rw [hXY, Real.inv_rpow hY.le]
      have hYp : 0 < ((b : ℝ) * Real.sin (π * u)) ^ pB b := Real.rpow_pos_of_pos hY _
      have hsplit : (b : ℝ) * Real.sin (π * u) =
          ((b : ℝ) * Real.sin (π * u)) ^ (1 - pB b) * ((b : ℝ) * Real.sin (π * u)) ^ pB b := by
        rw [← Real.rpow_add hY, sub_add_cancel, Real.rpow_one]
      have hle : ((b : ℝ) * Real.sin (π * u)) ^ (1 - pB b) ≤ rhoF := by
        rw [← rpow_one_sub_pB b hb]
        apply Real.rpow_le_rpow hY.le _ (by linarith)
        have := Real.sin_le_one (π * u)
        nlinarith
      rw [inv_le_iff_one_le_mul₀ hYp, mul_comm rhoF, mul_assoc]
      have hYi : ((b : ℝ) * Real.sin (π * u))⁻¹ * (rhoF * ((b : ℝ) * Real.sin (π * u)) ^ pB b) =
          rhoF * ((b : ℝ) * Real.sin (π * u)) ^ pB b / ((b : ℝ) * Real.sin (π * u)) := by
        field_simp
      rw [hYi, le_div_iff₀ hY]
      nlinarith
    calc Real.sqrt (psiB b u) ^ pB b ≤ X ^ pB b :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) h1 hp0.le
      _ ≤ rhoF * X := h2
      _ ≤ _ := hT

/-! ## `T_b` as a `BlockMaj b 1` -/

/-- Frequencies `(v, v)`, `|v| < b`. -/
def fejS (b : ℕ) : Finset (ℤ × ℤ) := (Finset.Ioo (-(b : ℤ)) b).image (fun v => (v, v))

/-- `#{(i, j) ∈ [0, K)² : i − j = v}`. -/
def cnt (K : ℕ) (v : ℤ) : ℕ := #((range K ×ˢ range K).filter (fun ij : ℕ × ℕ => (ij.1 : ℤ) - ij.2 = v))

/-- Coefficients: `τ(v, ·) = Σ_M wt(M+1) cnt(M+1, v)/(M+1)²`. -/
noncomputable def fejTau (b : ℕ) (w : ℤ × ℤ) : ℝ :=
  ∑ M ∈ range (mB b), wt b (M + 1) / ((M : ℝ) + 1) ^ 2 * cnt (M + 1) w.1

theorem cnt_neg (K : ℕ) (v : ℤ) : cnt K (-v) = cnt K v := by
  unfold cnt
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro a ha; simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_range] at ha ⊢
    simp only [Prod.fst_swap, Prod.snd_swap]; omega
  · intro a ha; simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_range] at ha ⊢
    simp only [Prod.fst_swap, Prod.snd_swap]; omega
  · intro a _; simp
  · intro a _; simp

theorem cnt_zero (K : ℕ) : cnt K 0 = K := by
  unfold cnt
  have : (range K ×ˢ range K).filter (fun ij : ℕ × ℕ => (ij.1 : ℤ) - ij.2 = 0) =
      (range K).image (fun i => (i, i)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hi, _⟩, h⟩; exact ⟨i, hi, rfl, by omega⟩
    · rintro ⟨a, ha, rfl, rfl⟩; exact ⟨⟨ha, ha⟩, by simp⟩
  rw [this, Finset.card_image_of_injective _ (fun a c h => by simpa using congrArg Prod.fst h), Finset.card_range]

theorem sum_cnt (K b : ℕ) (hK : K ≤ b) (f : ℤ → ℝ) :
    ∑ v ∈ Finset.Ioo (-(b : ℤ)) b, (cnt K v : ℝ) * f v =
      ∑ i ∈ range K, ∑ j ∈ range K, f ((i : ℤ) - j) := by
  have hmaps : ∀ ij ∈ range K ×ˢ range K, (fun ij : ℕ × ℕ => (ij.1 : ℤ) - ij.2) ij ∈ Finset.Ioo (-(b : ℤ)) b := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    simp only [Finset.mem_Ioo]; omega
  rw [show (∑ i ∈ range K, ∑ j ∈ range K, f ((i : ℤ) - j)) =
      ∑ ij ∈ range K ×ˢ range K, f ((ij.1 : ℤ) - ij.2) from
        (Finset.sum_product (range K) (range K) (fun ij : ℕ × ℕ => f ((ij.1 : ℤ) - ij.2))).symm,
    ← Finset.sum_fiberwise_of_maps_to' hmaps f]
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.sum_const, nsmul_eq_mul]; rfl

theorem Tval_fej (b : ℕ) (_hb : 10 ≤ b) (x y : ℝ) : Tval (fejS b) (fejTau b) x y = fejT b (x + y) := by
  unfold Tval fejS
  rw [Finset.sum_image (fun v _ w _ h => by simpa using congrArg Prod.fst h)]
  simp only [fejTau, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold fejT
  apply Finset.sum_congr rfl; intro M hM
  rw [Finset.mem_range] at hM
  have hK : M + 1 ≤ b := by unfold mB at hM; omega
  have h1 : ∑ v ∈ Finset.Ioo (-(b : ℤ)) b, wt b (M + 1) / ((M : ℝ) + 1) ^ 2 * (cnt (M + 1) v : ℝ) *
      Real.cos (2 * π * ((v : ℝ) * x + (v : ℝ) * y)) =
      wt b (M + 1) / ((M : ℝ) + 1) ^ 2 * ∑ v ∈ Finset.Ioo (-(b : ℤ)) b, (cnt (M + 1) v : ℝ) *
        Real.cos (2 * π * ((v : ℝ) * x + (v : ℝ) * y)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
  rw [h1, sum_cnt (M + 1) b hK (fun v => Real.cos (2 * π * ((v : ℝ) * x + (v : ℝ) * y)))]
  have h2 := norm_sq_sum_range_ee (M + 1) (x + y)
  have h3 : ∑ i ∈ range (M + 1), ∑ j ∈ range (M + 1),
      Real.cos (2 * π * ((((i : ℤ) - j : ℤ) : ℝ) * x + (((i : ℤ) - j : ℤ) : ℝ) * y)) =
      phiB (M + 1) (x + y) ^ 2 := by
    unfold phiB; rw [h2]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    congr 1; push_cast; ring
  rw [h3]
  unfold psiB
  have : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [this, div_pow]; ring

theorem fejTau_nonneg (b : ℕ) (hb : 10 ≤ b) (w : ℤ × ℤ) : 0 ≤ fejTau b w := by
  unfold fejTau
  apply Finset.sum_nonneg; intro M _
  have := wt_nonneg b (M + 1) hb
  positivity

theorem fejTau_zero (b : ℕ) (hb : 10 ≤ b) : fejTau b (0, 0) = tauF b := by
  have hm := mB_ge b hb
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hm0 : (0 : ℝ) < mB b := by exact_mod_cast (by omega : 0 < mB b)
  unfold fejTau
  simp only [cnt_zero]
  have e : ∀ M ∈ range (mB b), wt b (M + 1) / ((M : ℝ) + 1) ^ 2 * ((M + 1 : ℕ) : ℝ) =
      wt b (M + 1) * (1 / ((M + 1 : ℕ) : ℝ)) := by
    intro M _; push_cast
    have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    field_simp
  rw [Finset.sum_congr rfl e, sum_wt_mul b hb (fun k => 1 / (k : ℝ))]
  have e2 : ∑ M ∈ range (mB b), omg (M + 1) * (1 / ((M + 1 : ℕ) : ℝ)) =
      ∑ M ∈ range (mB b), omg (M + 1) / ((M : ℝ) + 1) := by
    apply Finset.sum_congr rfl; intro M _; push_cast; ring
  rw [e2, sum_omg_div _ (by omega), SB, sum_omg _ (by omega)]
  unfold tauF rhoF
  field_simp
  ring

theorem fejA (b : ℕ) (hb : 10 ≤ b) : ∑ w ∈ fejS b, |fejTau b w| = 1 := by
  have h := Tval_fej b hb 0 0
  unfold Tval at h
  simp only [mul_zero, add_zero, Real.cos_zero, mul_one] at h
  rw [Finset.sum_congr rfl (fun w _ => abs_of_nonneg (fejTau_nonneg b hb w)), h]
  unfold fejT
  rw [← sum_wt b hb]
  apply Finset.sum_congr rfl; intro M _
  rw [psiB_zero _ (by omega), mul_one]

theorem Gam_one (b : ℕ) (x y : ℝ) : Gam b 1 x y = Dfun b (x + y) := by
  simp [Gam]

/-- **The Fejér family as a block majorant** (`l = 1`). -/
noncomputable def fejMaj (b : ℕ) (hb : 10 ≤ b) : BlockMaj b 1 where
  S := fejS b
  τ := fejTau b
  p := pB b
  hp0 := by linarith [pB_ge b hb]
  hp1 := (pB_lt b hb).le
  h00 := by
    unfold fejS
    exact Finset.mem_image.2 ⟨0, Finset.mem_Ioo.2 ⟨by omega, by omega⟩, rfl⟩
  hS := by
    intro w hw
    unfold fejS at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_Ioo] at hv
    simp only [pow_one]
    exact ⟨abs_lt.2 hv, abs_lt.2 hv⟩
  hneg := by
    intro w hw
    unfold fejS at hw ⊢
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_Ioo] at hv
    exact Finset.mem_image.2 ⟨-v, Finset.mem_Ioo.2 ⟨by omega, by omega⟩, by simp⟩
  hsym := by
    intro w _
    unfold fejTau
    simp only [Prod.fst_neg, cnt_neg]
  hmaj := by
    intro x y
    rw [Gam_one, norm_Dfun b (by omega), Tval_fej b hb]
    exact fejT_maj b hb (x + y)

theorem fejMaj_t00 (b : ℕ) (hb : 10 ≤ b) : (fejMaj b hb).t00 = tauF b := fejTau_zero b hb

theorem fejMaj_A (b : ℕ) (hb : 10 ≤ b) : (fejMaj b hb).A = 1 := fejA b hb

/-! ## TL¹ for `b ≥ 10` -/

/-- **TL¹ for every base `b ≥ 10`** at `θ = 0.2608`, `δ = 0.47`. -/
theorem tl1_ge_ten (b : ℕ) (hb : 10 ≤ b) : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ) := by
  set M := fejMaj b hb with hM
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have ht0 : 0 < tauF b := tauF_pos b hb
  have htau := tauF_lt b hb
  set ψ := -Real.logb b (tauF b) with hψ
  have hψ2 : 2 * (2608 / 10000 : ℝ) < ψ := by
    have := (Real.logb_lt_iff_lt_rpow hb1 ht0).2 htau
    rw [hψ]; linarith
  have hθb := thetaB_pos b (by omega)
  have hp := pB_lt b hb
  have hpθ : 0 < (47 / 100 : ℝ) * thetaB b * (1 - M.p) / 18 := by
    have : M.p = pB b := rfl
    rw [this]
    have : 0 < 1 - pB b := by linarith
    positivity
  set κ := min ((ψ - 2 * (2608 / 10000 : ℝ)) / 4) ((47 / 100 : ℝ) * thetaB b * (1 - M.p) / 18) with hκ
  have hκ0 : 0 < κ := lt_min (by linarith) hpθ
  have hκ1 : κ ≤ (ψ - 2 * (2608 / 10000 : ℝ)) / 4 := min_le_left _ _
  have hκ2 : κ ≤ (47 / 100 : ℝ) * thetaB b * (1 - M.p) / 18 := min_le_right _ _
  have hMp : M.p = pB b := rfl
  have hθb1 := thetaB_le_one b (by omega)
  have hκle : κ ≤ 1 := by
    refine le_trans hκ2 ?_
    rw [hMp]
    have : 0 ≤ pB b := by linarith [pB_ge b hb]
    have : thetaB b * (1 - pB b) ≤ 1 := by nlinarith
    nlinarith
  refine ⟨κ, hκ0, hκle, ?_⟩
  have hpos : 0 ≤ 2 * (2608 / 10000 : ℝ) * thetaB b * (1 - M.p) / 3 := by
    rw [hMp]; have : 0 ≤ 1 - pB b := by linarith
    positivity
  apply tl1_eventually M (by omega) le_rfl ψ 0 (2608 / 10000) (47 / 100) κ κ (by linarith) le_rfl
    (by norm_num) (by norm_num) (by norm_num) hκ0 hκ0 hκle (by rw [hMp]; linarith [pB_ge b hb])
  · rw [fejMaj_t00]; exact ht0.le
  · rw [fejMaj_t00, Nat.cast_one, one_mul, hψ, neg_neg, Real.rpow_logb hb0 hb1.ne' ht0]
  · rw [fejMaj_A, Nat.cast_one, one_mul, Real.rpow_zero]
  · linarith
  · linarith

end Palprimes
