import Omega3.Statements
import Palprimes.TL1.Asymp

/-!
# Q04: Proposition CQ with route E′ (assembly). Sub-blueprint: `Q04_PLAN.md`.
-/

namespace Omega3

open Finset Real Palprimes

lemma Q04_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma Q04_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) : ‖Gg b g t‖ ≤ 1 := by
  unfold Gg
  calc ‖∑ a ∈ range b, (g a : ℂ) * ee (a * t)‖ ≤ ∑ a ∈ range b, ‖(g a : ℂ) * ee (a * t)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ range b, g a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, Q04_norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.1 a)]
    _ = 1 := hg.2

lemma Q04_fg_le_one (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N : ℕ) (α : ℝ) : ‖fg b g N α‖ ≤ 1 := by
  unfold fg; rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => Q04_Gg_norm_le b g hg _)

lemma Q04_F_le_G (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N : ℕ) (J : Finset ℕ)
    (hJ : J ⊆ range (N + 1)) (α : ℝ) : ‖fg b g N α‖ ≤ ‖gJ b g N J α‖ := by
  unfold fg gJ
  rw [← Finset.prod_sdiff hJ, norm_mul]
  have h1 : ‖∏ k ∈ range (N + 1) \ J, Gg b g ((cK b N k : ℝ) * α)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => Q04_Gg_norm_le b g hg _)
  calc _ ≤ 1 * ‖∏ k ∈ J, Gg b g ((cK b N k : ℝ) * α)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

lemma Q04_Fp_le_TK (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp : 0 < p) (H : ℕ)
    (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (N : ℕ) (K : Finset ℕ)
    (hK : K ⊆ range (N + 1)) (α : ℝ) :
    ‖fg b g N α‖ ^ p ≤ ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α) := by
  have h1 := Q04_F_le_G b g hg N K hK α
  unfold gJ at h1
  rw [norm_prod] at h1
  calc ‖fg b g N α‖ ^ p ≤ (∏ k ∈ K, ‖Gg b g ((cK b N k : ℝ) * α)‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp.le
    _ = ∏ k ∈ K, ‖Gg b g ((cK b N k : ℝ) * α)‖ ^ p :=
        (Real.finsetProd_rpow _ _ (fun _ _ => norm_nonneg _) _).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ _ => hT _)

lemma Q04_F_le_TK (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (H : ℕ)
    (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (N : ℕ) (K : Finset ℕ)
    (hK : K ⊆ range (N + 1)) (α : ℝ) :
    ‖fg b g N α‖ ≤ ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α) := by
  have h1 : ‖fg b g N α‖ ≤ ‖fg b g N α‖ ^ p := by
    have := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (fg b g N α)) (Q04_fg_le_one b g hg N α)
      hp.le hp1.le
    rwa [Real.rpow_one] at this
  exact h1.trans (Q04_Fp_le_TK b g hg p hp H τ hT N K hK α)

/-- Telescoping: `Σ_{a < n ≤ M} n⁻² ≤ 1/a`. -/
lemma Q04_inv_sq (a : ℕ) (ha : 1 ≤ a) (M : ℕ) : ∑ n ∈ Ioc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / a := by
  have key : ∀ M, a ≤ M → ∑ n ∈ Ioc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / a - 1 / M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans ha hM
        have h2 : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / M - 1 / ((M + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  rcases le_or_gt a M with h | h
  · have := key M h
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp

/-- Numerics of one block, in exponential form. -/
lemma Q04_num (q α pT σ θw β₁ η₁ L cA cM Qr tr T0 AK M4 ℓ : ℝ) (hq : 0 ≤ q) (hQ : Qr = Real.exp q)
    (ht : tr = Real.exp (-(α * q))) (_hT00 : 0 ≤ T0) (hT0 : T0 ≤ Real.exp (-((1 + σ / 2) * q)))
    (hAK0 : 0 ≤ AK) (hAK : AK ≤ cA * Real.exp (β₁ * q)) (_hM40 : 0 ≤ M4)
    (hM4 : M4 ≤ cM * Real.exp (-((1 + θw) * q))) (hℓ : ℓ ≤ L) (hL : 0 ≤ L) (hcA : 0 ≤ cA) (hcM : 0 ≤ cM)
    (r1 : η₁ ≤ α * (1 - pT) + σ / 2) (r2 : η₁ ≤ α * (1 - pT) - β₁) (r3 : η₁ ≤ θw - 3 * α)
    (r4 : η₁ ≤ 1 + σ / 2) (r5 : η₁ ≤ 1 - β₁) :
    (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 3 * T0 + 4 * Qr ^ 2 * ℓ * AK) + tr⁻¹ ^ 3 * (4 * Qr ^ 3 * M4) +
      (4 * Qr ^ 2 * T0 + 2 * Qr * ℓ * AK)) ≤ (8 + 6 * cA + 4 * cM) * (1 + L) * Real.exp (-(η₁ * q)) := by
  have hQ0 : 0 < Qr := by rw [hQ]; exact Real.exp_pos _
  have htp : tr ^ (1 - pT) = Real.exp (-(α * q) * (1 - pT)) := by
    rw [ht, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hti : tr⁻¹ ^ 3 = Real.exp (3 * (α * q)) := by
    rw [ht, ← Real.exp_neg, neg_neg, ← Real.exp_natCast_mul]; norm_num
  have hE : 0 < Real.exp (-(η₁ * q)) := Real.exp_pos _
  -- the five terms
  have e1 : (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 3 * T0)) ≤ 4 * Real.exp (-(η₁ * q)) := by
    have : (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 3 * T0)) = 4 * (Qr * tr ^ (1 - pT) * T0) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc Qr * tr ^ (1 - pT) * T0 ≤ Real.exp q * Real.exp (-(α * q) * (1 - pT)) *
          Real.exp (-((1 + σ / 2) * q)) := by
          rw [← hQ, ← htp]; exact mul_le_mul_of_nonneg_left hT0 (mul_nonneg hQ0.le (by rw [htp]; positivity))
      _ = Real.exp (-((α * (1 - pT) + σ / 2) * q)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
  have e2 : (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 2 * ℓ * AK)) ≤ 4 * cA * L * Real.exp (-(η₁ * q)) := by
    have : (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 2 * ℓ * AK)) = 4 * ℓ * (tr ^ (1 - pT) * AK) := by
      field_simp
    rw [this]
    have hb : tr ^ (1 - pT) * AK ≤ cA * Real.exp (-(η₁ * q)) := by
      calc tr ^ (1 - pT) * AK ≤ Real.exp (-(α * q) * (1 - pT)) * (cA * Real.exp (β₁ * q)) := by
            rw [← htp]; exact mul_le_mul_of_nonneg_left hAK (by rw [htp]; positivity)
        _ = cA * Real.exp (-((α * (1 - pT) - β₁) * q)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ ≤ cA * Real.exp (-(η₁ * q)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hcA
    have hb0 : 0 ≤ tr ^ (1 - pT) * AK := mul_nonneg (by rw [htp]; positivity) hAK0
    rcases le_or_gt 0 ℓ with hℓ0 | hℓ0
    · calc 4 * ℓ * (tr ^ (1 - pT) * AK) ≤ 4 * L * (cA * Real.exp (-(η₁ * q))) :=
            mul_le_mul (by linarith) hb hb0 (by linarith)
        _ = _ := by ring
    · have : 4 * ℓ * (tr ^ (1 - pT) * AK) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0
      have : 0 ≤ 4 * cA * L * Real.exp (-(η₁ * q)) := by positivity
      linarith
  have e3 : (Qr ^ 2)⁻¹ * (tr⁻¹ ^ 3 * (4 * Qr ^ 3 * M4)) ≤ 4 * cM * Real.exp (-(η₁ * q)) := by
    have : (Qr ^ 2)⁻¹ * (tr⁻¹ ^ 3 * (4 * Qr ^ 3 * M4)) = 4 * (Qr * tr⁻¹ ^ 3 * M4) := by
      field_simp
    rw [this, mul_assoc 4 cM]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc Qr * tr⁻¹ ^ 3 * M4 ≤ Real.exp q * Real.exp (3 * (α * q)) * (cM * Real.exp (-((1 + θw) * q))) := by
          rw [← hQ, ← hti]; exact mul_le_mul_of_nonneg_left hM4 (mul_nonneg hQ0.le (by rw [hti]; positivity))
      _ = cM * Real.exp (-((θw - 3 * α) * q)) := by
          rw [mul_left_comm, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ ≤ cM * Real.exp (-(η₁ * q)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hcM
  have e4 : (Qr ^ 2)⁻¹ * (4 * Qr ^ 2 * T0) ≤ 4 * Real.exp (-(η₁ * q)) := by
    have : (Qr ^ 2)⁻¹ * (4 * Qr ^ 2 * T0) = 4 * T0 := by field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact hT0.trans (Real.exp_le_exp.2 (by nlinarith))
  have e5 : (Qr ^ 2)⁻¹ * (2 * Qr * ℓ * AK) ≤ 2 * cA * L * Real.exp (-(η₁ * q)) := by
    have : (Qr ^ 2)⁻¹ * (2 * Qr * ℓ * AK) = 2 * ℓ * (Qr⁻¹ * AK) := by field_simp
    rw [this]
    have hb : Qr⁻¹ * AK ≤ cA * Real.exp (-(η₁ * q)) := by
      calc Qr⁻¹ * AK ≤ Real.exp (-q) * (cA * Real.exp (β₁ * q)) := by
            rw [hQ, ← Real.exp_neg]; exact mul_le_mul_of_nonneg_left hAK (by positivity)
        _ = cA * Real.exp (-((1 - β₁) * q)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ ≤ cA * Real.exp (-(η₁ * q)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hcA
    have hb0 : 0 ≤ Qr⁻¹ * AK := mul_nonneg (by positivity) hAK0
    rcases le_or_gt 0 ℓ with hℓ0 | hℓ0
    · calc 2 * ℓ * (Qr⁻¹ * AK) ≤ 2 * L * (cA * Real.exp (-(η₁ * q))) :=
            mul_le_mul (by linarith) hb hb0 (by linarith)
        _ = _ := by ring
    · have : 2 * ℓ * (Qr⁻¹ * AK) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hb0
      have : 0 ≤ 2 * cA * L * Real.exp (-(η₁ * q)) := by positivity
      linarith
  have hsum : (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 3 * T0 + 4 * Qr ^ 2 * ℓ * AK) +
      tr⁻¹ ^ 3 * (4 * Qr ^ 3 * M4) + (4 * Qr ^ 2 * T0 + 2 * Qr * ℓ * AK)) =
      (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 3 * T0)) + (Qr ^ 2)⁻¹ * (tr ^ (1 - pT) * (4 * Qr ^ 2 * ℓ * AK)) +
      (Qr ^ 2)⁻¹ * (tr⁻¹ ^ 3 * (4 * Qr ^ 3 * M4)) + (Qr ^ 2)⁻¹ * (4 * Qr ^ 2 * T0) +
      (Qr ^ 2)⁻¹ * (2 * Qr * ℓ * AK) := by ring
  rw [hsum]
  have hfin : 4 * Real.exp (-(η₁ * q)) + 4 * cA * L * Real.exp (-(η₁ * q)) +
      4 * cM * Real.exp (-(η₁ * q)) + 4 * Real.exp (-(η₁ * q)) + 2 * cA * L * Real.exp (-(η₁ * q)) ≤
      (8 + 6 * cA + 4 * cM) * (1 + L) * Real.exp (-(η₁ * q)) := by
    have h1 : 0 ≤ cA * Real.exp (-(η₁ * q)) := by positivity
    have h2 : 0 ≤ cM * L * Real.exp (-(η₁ * q)) := by positivity
    have h3 : 0 ≤ L * Real.exp (-(η₁ * q)) := by positivity
    nlinarith
  linarith

set_option maxHeartbeats 800000 in
/-- One dyadic block of primes `[Q, 2Q)`: the large/small cut with route E′. -/
lemma Q04_block (b : ℕ) (g : ℕ → ℝ) (hb : 2 ≤ b) (hg : IsDigitWeight b g) (pT : ℝ) (hp0 : 0 < pT)
    (hp1 : pT < 1) (H : ℕ) (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ pT ≤ trigEval H τ t)
    (hH : H ≤ 2 * b - 2) (hτ0 : 0 ≤ τ 0) (N Q j kK : ℕ) (hQ2 : 2 ≤ Q) (hbQ : b < Q) (hj1 : 1 ≤ j)
    (hjN : j < N) (hjQ : 2 * b ^ (2 * j + 1) ≤ Q ^ 2) (hkK : kK + 1 ≤ N) (β t : ℝ) (ht : 0 < t)
    (hDiag : SqDiagStmt) (hPars : SqParsevalStmt) :
    ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹ *
        ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + β)‖) +
          ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + β)‖) ≤
      ((Q : ℝ) ^ 2)⁻¹ * (t ^ (1 - pT) * (4 * (Q : ℝ) ^ 3 * τ 0 ^ kK +
          4 * (Q : ℝ) ^ 2 * (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) * trigMass H τ ^ kK) +
        t⁻¹ ^ 3 * (4 * (Q : ℝ) ^ 3 * mw4 b g ^ j) +
        (4 * (Q : ℝ) ^ 2 * τ 0 ^ kK +
          2 * (Q : ℝ) * (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) * trigMass H τ ^ kK)) := by
  classical
  set K := Ico 1 (kK + 1) with hKdef
  have hK1 : K ⊆ Ico 1 N := by intro k hk; simp only [hKdef, mem_Ico] at hk ⊢; omega
  have hK : K ⊆ range (N + 1) := by intro k hk; simp only [hKdef, mem_Ico, mem_range] at hk ⊢; omega
  have hKc : K.card = kK := by rw [hKdef, Nat.card_Ico]; omega
  set J := Ico (N - j) N with hJdef
  have hJ : J ⊆ range (N + 1) := by intro k hk; simp only [hJdef, mem_Ico, mem_range] at hk ⊢; omega
  set TK : ℝ → ℝ := fun α => ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * α) with hTK
  have hTK0 : ∀ α, 0 ≤ TK α := fun α =>
    (Real.rpow_nonneg (norm_nonneg _) _).trans (Q04_Fp_le_TK b g hg pT hp0 H τ hT N K hK α)
  have hcut : ∀ α, ‖fg b g N α‖ ≤ t ^ (1 - pT) * TK α + t⁻¹ ^ 3 * ‖gJ b g N J α‖ ^ 4 := fun α =>
    cut_pointwise _ _ _ _ _ (norm_nonneg _) (Q04_F_le_G b g hg N J hJ α) ht hp0 hp1.le
      (Q04_Fp_le_TK b g hg pT hp0 H τ hT N K hK α)
  have hcut0 : ∀ α, 0 ≤ t ^ (1 - pT) * TK α + t⁻¹ ^ 3 * ‖gJ b g N J α‖ ^ 4 := fun α => by
    have := hTK0 α; positivity
  set P := (Ico Q (2 * Q)).filter Nat.Prime with hP
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have hpQ : ∀ p ∈ P, Q ≤ p ∧ p < 2 * Q ∧ p.Prime := by
    intro p hp; simp only [hP, mem_filter, mem_Ico] at hp; exact ⟨hp.1.1, hp.1.2, hp.2⟩
  -- per prime
  have hper : ∀ p ∈ P, ((p : ℝ) ^ 2)⁻¹ *
      ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + β)‖) +
        ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + β)‖) ≤
      ((Q : ℝ) ^ 2)⁻¹ * (t ^ (1 - pT) * ∑ h ∈ range (p ^ 2), TK ((h : ℝ) / (p ^ 2 : ℕ) + β) +
        t⁻¹ ^ 3 * ∑ h ∈ range (p ^ 2), ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 +
        ∑ h ∈ range p, TK ((h : ℝ) / p + β)) := by
    intro p hp
    have hQp : (Q : ℝ) ≤ p := by exact_mod_cast (hpQ p hp).1
    have hinv : ((p : ℝ) ^ 2)⁻¹ ≤ ((Q : ℝ) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hQp 2)
    have h1 : (∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + β)‖) ≤
        t ^ (1 - pT) * ∑ h ∈ range (p ^ 2), TK ((h : ℝ) / (p ^ 2 : ℕ) + β) +
        t⁻¹ ^ 3 * ∑ h ∈ range (p ^ 2), ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      calc _ ≤ ∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            (t ^ (1 - pT) * TK ((h : ℝ) / (p ^ 2 : ℕ) + β) +
              t⁻¹ ^ 3 * ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4) :=
            Finset.sum_le_sum (fun h _ => hcut _)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun h _ _ => hcut0 _)
    have h2 : ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + β)‖ ≤ ∑ h ∈ range p, TK ((h : ℝ) / p + β) := by
      calc _ ≤ ∑ h ∈ Ico 1 p, TK ((h : ℝ) / p + β) :=
            Finset.sum_le_sum (fun h _ => Q04_F_le_TK b g hg pT hp0 hp1 H τ hT N K hK _)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (by intro h hh; simp only [mem_Ico, mem_range] at hh ⊢; omega) (fun h _ _ => hTK0 _)
    have h0 : 0 ≤ (∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + β)‖) +
        ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + β)‖ :=
      add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    calc _ ≤ ((Q : ℝ) ^ 2)⁻¹ * ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + β)‖) + ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + β)‖) :=
          mul_le_mul_of_nonneg_right hinv h0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the three sums over primes
  obtain ⟨hD1, hD2⟩ := hDiag b H N Q τ K β hb hH hτ0 hK1 hQ2
  rw [hKc] at hD1 hD2
  have hPc : (P.card : ℝ) ≤ Q := by
    have : P.card ≤ Q := by
      calc P.card ≤ (Ico Q (2 * Q)).card := Finset.card_filter_le _ _
        _ = Q := by rw [Nat.card_Ico]; omega
    exact_mod_cast this
  have hG : ∑ p ∈ P, ∑ h ∈ range (p ^ 2), ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 ≤
      4 * (Q : ℝ) ^ 3 * mw4 b g ^ j := by
    have hm0 : 0 ≤ mw4 b g := by unfold mw4; positivity
    calc _ = ∑ p ∈ P, (p : ℝ) ^ 2 * mw4 b g ^ j := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          obtain ⟨hQp, hp2, hpr⟩ := hpQ p hp
          refine hPars b g N j p β hb hj1 hjN hpr ?_ ?_
          · intro hdiv; have := Nat.le_of_dvd (by omega) hdiv; omega
          · calc 2 * b ^ (2 * j + 1) ≤ Q ^ 2 := hjQ
              _ ≤ p ^ 2 := Nat.pow_le_pow_left hQp 2
      _ ≤ ∑ _p ∈ P, 4 * (Q : ℝ) ^ 2 * mw4 b g ^ j := by
          apply Finset.sum_le_sum; intro p hp
          have : (p : ℝ) ≤ 2 * Q := by exact_mod_cast (hpQ p hp).2.1.le
          have hp0' : (0 : ℝ) ≤ p := by positivity
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          nlinarith
      _ = P.card * (4 * (Q : ℝ) ^ 2 * mw4 b g ^ j) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q * (4 * (Q : ℝ) ^ 2 * mw4 b g ^ j) := mul_le_mul_of_nonneg_right hPc (by positivity)
      _ = 4 * (Q : ℝ) ^ 3 * mw4 b g ^ j := by ring
  have ht1 : 0 ≤ t ^ (1 - pT) := Real.rpow_nonneg ht.le _
  have ht3 : 0 ≤ t⁻¹ ^ 3 := by positivity
  calc _ ≤ ∑ p ∈ P, ((Q : ℝ) ^ 2)⁻¹ * (t ^ (1 - pT) * ∑ h ∈ range (p ^ 2), TK ((h : ℝ) / (p ^ 2 : ℕ) + β) +
        t⁻¹ ^ 3 * ∑ h ∈ range (p ^ 2), ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 +
        ∑ h ∈ range p, TK ((h : ℝ) / p + β)) := Finset.sum_le_sum hper
    _ = ((Q : ℝ) ^ 2)⁻¹ * (t ^ (1 - pT) * ∑ p ∈ P, ∑ h ∈ range (p ^ 2), TK ((h : ℝ) / (p ^ 2 : ℕ) + β) +
        t⁻¹ ^ 3 * ∑ p ∈ P, ∑ h ∈ range (p ^ 2), ‖gJ b g N J ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 +
        ∑ p ∈ P, ∑ h ∈ range p, TK ((h : ℝ) / p + β)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hD1 ht1) (mul_le_mul_of_nonneg_left hG ht3)) hD2

/-- `Σ_s (g ∗ g)(s) = (Σ g)²`. -/
lemma Q04_conv_total (b : ℕ) (hb : 1 ≤ b) (g : ℕ → ℝ) :
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

lemma Q04_thw_lt_one (b : ℕ) (hb : 2 ≤ b) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (θw : ℝ)
    (hm4 : mw4 b g ≤ (b : ℝ) ^ (-(1 + θw))) : θw < 1 := by
  by_contra hcon
  push Not at hcon
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : 1 ≤ (2 * (b : ℝ) - 1) * mw4 b g := by
    have h := sq_sum_le_card_mul_sum_sq (s := range (2 * b - 1))
      (f := fun s => ∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0)
    rw [Q04_conv_total b (by omega) g, ← Finset.sum_mul, hg.2, one_mul, one_pow, card_range] at h
    unfold mw4
    have hc : ((2 * b - 1 : ℕ) : ℝ) = 2 * (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc] at h
    exact h
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

lemma Q04_XW_nonneg (b : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (N : ℕ) : 0 ≤ XW b g N := by
  unfold XW AW
  apply Finset.sum_nonneg; intro d _
  split_ifs
  · unfold wDig; exact Finset.prod_nonneg (fun k _ => hg _)
  · exact le_refl 0

set_option maxHeartbeats 8000000 in
theorem itemQ04 : ItemQ04 := by
  intro b g pT H τ ψ lA θw c₀ c₁ hb hg hp0 hp1 hH hT hτ0 hτψ hA hm4 hθw hc₀ hc₀₁ hc₁ hQ1 hQ2 hRed hDiag hPars
  classical
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  obtain ⟨lb, hlb⟩ : ∃ lb, lb = Real.log b := ⟨_, rfl⟩
  have hlbpos : 0 < lb := by rw [hlb]; exact Real.log_pos hb1
  have hθw1 := Q04_thw_lt_one b hb2 g hg θw hm4
  have hc₁pos : 0 < c₁ := lt_trans hc₀ hc₀₁
  have hψ : 0 < ψ := by linarith
  have h1p : 0 < 1 - pT := by linarith
  obtain ⟨lA', hlA'⟩ : ∃ l, l = max lA 0 := ⟨_, rfl⟩
  have hlA'0 : 0 ≤ lA' := by rw [hlA']; exact le_max_right _ _
  have hA' : trigMass H τ ≤ (b : ℝ) ^ lA' :=
    hA.trans (Real.rpow_le_rpow_of_exponent_le hb1.le (by rw [hlA']; exact le_max_left _ _))
  have hpos3 : 0 < (1 - pT) * ψ * θw := by positivity
  have hQ2' : 3 * lA' < (1 - pT) * ψ * θw := by
    rcases le_total lA 0 with h | h
    · rw [hlA', max_eq_right h]; linarith
    · rw [hlA', max_eq_left h]; exact hQ2
  obtain ⟨s₁, hs₁⟩ : ∃ s, s = ψ - 2 * c₁ := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s, s = (1 - pT) * ψ * θw - 3 * lA' := ⟨_, rfl⟩
  obtain ⟨Dσ, hDσ⟩ : ∃ s, s = 3 * lA' / 2 + (1 - pT) * ψ * θw := ⟨_, rfl⟩
  have hs₁p : 0 < s₁ := by rw [hs₁]; linarith
  have hs₂p : 0 < s₂ := by rw [hs₂]; linarith
  have hDσp : 0 < Dσ := by rw [hDσ]; linarith
  obtain ⟨σ, hσ⟩ : ∃ s, s = min (min (1 / 2) (s₁ / (2 * c₁))) (s₂ / (2 * Dσ)) := ⟨_, rfl⟩
  have hσpos : 0 < σ := by rw [hσ]; exact lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  have hσh : σ ≤ 1 / 2 := by rw [hσ]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hσ1 : σ * (2 * c₁) ≤ s₁ := by
    have : σ ≤ s₁ / (2 * c₁) := by rw [hσ]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  have hσ2 : σ * (2 * Dσ) ≤ s₂ := by
    have : σ ≤ s₂ / (2 * Dσ) := by rw [hσ]; exact min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨α, hα⟩ : ∃ a, a = (1 - σ) * θw / 3 := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁⟩ : ∃ a, a = lA' * (1 + σ / 2) / ψ := ⟨_, rfl⟩
  have h1σ : 0 ≤ 1 - σ := by linarith
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hr2 : 0 < α * (1 - pT) - β₁ := by
    have key : 3 * ψ * (α * (1 - pT) - β₁) = s₂ - σ * Dσ := by
      rw [hα, hβ₁, hs₂, hDσ]; field_simp; ring
    have : 0 < 3 * ψ * (α * (1 - pT) - β₁) := by rw [key]; linarith
    by_contra hc; push Not at hc
    have : 3 * ψ * (α * (1 - pT) - β₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hβ₁1 : β₁ < 1 := by
    have h1 : α * (1 - pT) ≤ θw / 3 := by
      rw [hα]
      have h2 : (1 - σ) * (1 - pT) ≤ 1 := mul_le_one₀ (by linarith) h1p.le (by linarith)
      have h3 : (1 - σ) * θw / 3 * (1 - pT) = θw / 3 * ((1 - σ) * (1 - pT)) := by ring
      rw [h3]; exact mul_le_of_le_one_right (by positivity) h2
    linarith
  obtain ⟨η₁, hη₁⟩ : ∃ e, e = min (min (σ / 2) (α * (1 - pT) - β₁)) (min (σ * θw) (1 - β₁)) := ⟨_, rfl⟩
  have hη₁pos : 0 < η₁ := by
    rw [hη₁]; exact lt_min (lt_min (by positivity) hr2) (lt_min (by positivity) (by linarith))
  have hη_a : η₁ ≤ σ / 2 := by rw [hη₁]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη_b : η₁ ≤ α * (1 - pT) - β₁ := by rw [hη₁]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hη_c : η₁ ≤ σ * θw := by rw [hη₁]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_d : η₁ ≤ 1 - β₁ := by rw [hη₁]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hαp : 0 ≤ α * (1 - pT) := by positivity
  have r1 : η₁ ≤ α * (1 - pT) + σ / 2 := by linarith
  have r3 : η₁ ≤ θw - 3 * α := by rw [hα]; linarith
  have r4 : η₁ ≤ 1 + σ / 2 := by linarith
  obtain ⟨cA, hcA⟩ : ∃ c, c = Real.exp (lA' * lb) := ⟨_, rfl⟩
  obtain ⟨cM, hcM⟩ : ∃ c, c = Real.exp (2 * (1 + θw) * lb) := ⟨_, rfl⟩
  have hcA0 : 0 ≤ cA := by rw [hcA]; positivity
  have hcM0 : 0 ≤ cM := by rw [hcM]; positivity
  obtain ⟨Cb, hCb⟩ : ∃ c, c = 8 + 6 * cA + 4 * cM := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  obtain ⟨ν, hν⟩ : ∃ v, v = (1 + σ / 2) * (2 * c₁) / ψ := ⟨_, rfl⟩
  have hν1 : ν < 1 := by
    rw [hν, div_lt_one hψ]
    have : (1 + σ / 2) * (2 * c₁) = 2 * c₁ + σ * (2 * c₁) / 2 := by ring
    rw [this]; linarith
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  obtain ⟨Bb, hBb⟩ : ∃ c : ℝ, c = (b : ℝ) ^ 2 + (bigB b : ℝ) := ⟨_, rfl⟩
  have hexpc : 1 < Real.exp (c₀ * lb) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by positivity)
  obtain ⟨Nc, hNc⟩ := pow_unbounded_of_one_lt (2 * Bb) hexpc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4b : 0 ≤ Real.log (4 * b) := Real.log_nonneg (by linarith)
  obtain ⟨C₂, hC₂⟩ : ∃ c, c = 1 + (Real.log (4 * b) + 2 * lb) / Real.log 2 := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  obtain ⟨Cf, hCf⟩ : ∃ c, c = ((bigB b).divisors.card : ℝ) * (bigB b : ℝ) * b * Cb *
      Real.exp (η₁ * Real.log 2) * 2 * C₂ := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ r, r = Real.exp (-(η₁ * c₀ * lb)) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by
    have : 0 < η₁ * c₀ * lb := by positivity
    linarith)
  obtain ⟨Nd, hNd⟩ := eventually_poly_geom Cf 2 ρ hρ0 hρ1 1 one_pos
  obtain ⟨Nb, hNb⟩ : ∃ n : ℕ, n = ⌈(ν / 2 + 2) / (1 - ν)⌉₊ := ⟨_, rfl⟩
  refine ⟨η₁ * c₀ / 2, by positivity, max (max Nb Nc) (max Nd 1), ?_⟩
  intro N hN
  have hNb' : Nb ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNc' : Nc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNd' : Nd ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  -- x and its powers
  obtain ⟨ℓx, hℓx⟩ : ∃ l, l = (2 * (N : ℝ) + 1) * lb := ⟨_, rfl⟩
  have hℓx0 : 0 ≤ ℓx := by rw [hℓx]; positivity
  have hx : xx b N = Real.exp ℓx := by
    unfold xx
    rw [hℓx, hlb, show (2 * (N : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_natCast_mul,
      Real.exp_log hb0]
  have hxr : ∀ a : ℝ, xx b N ^ a = Real.exp (ℓx * a) := by
    intro a; rw [hx, ← Real.exp_mul]
  have hx0 : 0 ≤ xx b N := by rw [hx]; positivity
  have hx1 : 1 ≤ xx b N := by rw [hx]; exact Real.one_le_exp hℓx0
  -- the large-N facts
  have hNbR : (ν / 2 + 2) ≤ (1 - ν) * N := by
    have h1 : (ν / 2 + 2) / (1 - ν) ≤ (Nb : ℝ) := by rw [hNb]; exact Nat.le_ceil _
    have h2 : (Nb : ℝ) ≤ N := by exact_mod_cast hNb'
    have := (div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ν)).1 (h1.trans h2)
    linarith
  have hP0big : 2 * Bb < xx b N ^ c₀ := by
    rw [hxr]
    calc 2 * Bb < Real.exp (c₀ * lb) ^ Nc := hNc
      _ ≤ Real.exp (c₀ * lb) ^ (2 * N + 1) := pow_le_pow_right₀ hexpc.le (by omega)
      _ = Real.exp (ℓx * c₀) := by
          rw [← Real.exp_natCast_mul, hℓx]; push_cast; ring_nf
  have hBbge : (b : ℝ) ^ 2 + (bigB b : ℝ) ≤ Bb := by rw [hBb]
  have hbigB0 : (0 : ℝ) ≤ (bigB b : ℝ) := by positivity
  have hb2R : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_pow₀ hb1.le
  have h4bx : (1 : ℝ) ≤ 4 * (b : ℝ) * xx b N := by
    have := mul_le_mul (by linarith : (1 : ℝ) ≤ 4 * b) hx1 zero_le_one (by positivity)
    linarith
  -- the sets
  obtain ⟨P0, hP0⟩ : ∃ t, t = xx b N ^ c₀ := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ t, t = xx b N ^ c₁ := ⟨_, rfl⟩
  have hP0e : P0 = Real.exp (ℓx * c₀) := by rw [hP0, hxr]
  have hP1e : P1 = Real.exp (ℓx * c₁) := by rw [hP1, hxr]
  have hP0b : 2 * Bb < P0 := by rw [hP0]; exact hP0big
  have hP0two : 2 ≤ P0 := by linarith
  have hP1x : P1 ≤ xx b N := by
    rw [hP1]; calc xx b N ^ c₁ ≤ xx b N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = xx b N := Real.rpow_one _
  have hP11 : 1 ≤ P1 := by rw [hP1e]; exact Real.one_le_exp (by positivity)
  obtain ⟨a₀, ha₀⟩ : ∃ n : ℕ, n = ⌊P0⌋₊ := ⟨_, rfl⟩
  obtain ⟨Y1, hY1⟩ : ∃ n : ℕ, n = ⌊P1⌋₊ := ⟨_, rfl⟩
  have ha₀le : (a₀ : ℝ) ≤ P0 := by rw [ha₀]; exact Nat.floor_le (by linarith)
  have ha₀gt : P0 < a₀ + 1 := by rw [ha₀]; exact Nat.lt_floor_add_one P0
  have ha₀1 : 1 ≤ a₀ := by rw [ha₀]; exact Nat.one_le_floor_iff _ |>.2 (by linarith)
  have hY1le : (Y1 : ℝ) ≤ P1 := by rw [hY1]; exact Nat.floor_le (by linarith)
  have hY11 : 1 ≤ Y1 := by rw [hY1]; exact Nat.one_le_floor_iff _ |>.2 hP11
  obtain ⟨i₀, hi₀⟩ : ∃ n : ℕ, n = Nat.log 2 a₀ := ⟨_, rfl⟩
  obtain ⟨i₁, hi₁⟩ : ∃ n : ℕ, n = Nat.log 2 Y1 + 1 := ⟨_, rfl⟩
  have hi₁b : i₁ ≤ b * (2 * N + 1) := by
    have hYx : Y1 ≤ b ^ (2 * N + 1) := by
      have : (Y1 : ℝ) ≤ ((b ^ (2 * N + 1) : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact hY1le.trans (by unfold xx at hP1x; exact hP1x)
      exact_mod_cast this
    have h2 : b ^ (2 * N + 1) < 2 ^ (b * (2 * N + 1)) := by
      rw [pow_mul]; exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
    have := Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt hYx h2)
    omega
  set S := (Icc 1 ⌊xx b N ^ c₁⌋₊).filter (fun p : ℕ => p.Prime ∧ xx b N ^ c₀ < (p : ℝ)) with hS
  have hSmem : ∀ p ∈ S, p.Prime ∧ P0 < p ∧ p ≤ Y1 := by
    intro p hp
    simp only [hS, mem_filter, mem_Icc] at hp
    refine ⟨hp.2.1, by rw [hP0]; exact hp.2.2, by rw [hY1, hP1]; exact hp.1.2⟩
  have hndvd : ∀ p ∈ S, ¬ p ∣ bigB b := by
    intro p hp hdvd
    have hB0 : 0 < bigB b := by
      unfold bigB
      have : b < b ^ 3 := by
        calc b = b ^ 1 := (pow_one b).symm
          _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    have h1 := Nat.le_of_dvd hB0 hdvd
    have h2 : (p : ℝ) ≤ bigB b := by exact_mod_cast h1
    have h3 := (hSmem p hp).2.1
    linarith
  -- reduction
  set Fk : ℕ → ℕ → ℝ := fun k p => ((p : ℝ) ^ 2)⁻¹ *
        ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖) with hFk
  have hFk0 : ∀ k p, 0 ≤ Fk k p := fun k p => mul_nonneg (by positivity)
    (add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hAWp : ∀ p ∈ S, AW b g N (p ^ 2) ≤ XW b g N * (1 / (p : ℝ) ^ 2) +
      ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), Fk k p := by
    intro p hp
    have h := hRed b g N p hb2 (hSmem p hp).1 (hndvd p hp)
    have := (abs_sub_le_iff.1 h).1
    rw [mul_one_div]
    linarith
  -- one block
  obtain ⟨Lst, hLst⟩ : ∃ l, l = Real.log (4 * b * xx b N) / Real.log 2 := ⟨_, rfl⟩
  have hLst0 : 0 ≤ Lst := by rw [hLst]; exact div_nonneg (Real.log_nonneg h4bx) hlog2.le
  obtain ⟨Bfix, hBfix⟩ : ∃ c, c = Cb * (1 + Lst) * Real.exp (η₁ * Real.log 2) *
      Real.exp (-(η₁ * c₀ * ℓx)) := ⟨_, rfl⟩
  have hblock : ∀ i ∈ Ico i₀ i₁, ∀ k : ℕ,
      ∑ p ∈ (Ico (2 ^ i) (2 * 2 ^ i)).filter Nat.Prime, Fk k p ≤ Bfix := by
    intro i hi k
    simp only [mem_Ico] at hi
    obtain ⟨Q, hQ⟩ : ∃ n : ℕ, n = 2 ^ i := ⟨_, rfl⟩
    rw [← hQ]
    have hQpos : 0 < Q := by rw [hQ]; positivity
    have hQR0 : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hP0Q : P0 < 2 * (Q : ℝ) := by
      have h1 : a₀ < 2 ^ (i₀ + 1) := by rw [hi₀]; exact Nat.lt_pow_succ_log_self (by norm_num) a₀
      have h2 : 2 ^ i₀ ≤ Q := by rw [hQ]; exact Nat.pow_le_pow_right (by norm_num) hi.1
      have h3 : a₀ + 1 ≤ 2 * Q := by rw [pow_succ] at h1; omega
      have h4 : ((a₀ : ℝ) + 1) ≤ 2 * (Q : ℝ) := by exact_mod_cast h3
      linarith
    have hQP1 : (Q : ℝ) ≤ P1 := by
      have h1 : Q ≤ Y1 := by
        rw [hQ]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_log_le_self 2 (by omega))
      exact le_trans (by exact_mod_cast h1) hY1le
    have hbQsq : b ^ 2 < Q := by
      have : ((b ^ 2 : ℕ) : ℝ) < Q := by push_cast; linarith
      exact_mod_cast this
    have hbQ : b < Q := lt_of_le_of_lt (Nat.le_self_pow (by norm_num) b) hbQsq
    have hQ2 : 2 ≤ Q := by omega
    obtain ⟨q, hq⟩ : ∃ t, t = Real.log Q := ⟨_, rfl⟩
    have hQe : (Q : ℝ) = Real.exp q := by rw [hq, Real.exp_log hQR0]
    have hq0 : 0 ≤ q := by rw [hq]; exact Real.log_nonneg (by exact_mod_cast hQpos)
    have hqle : q ≤ ℓx * c₁ := by
      rw [hq, ← Real.log_exp (ℓx * c₁), ← hP1e]; exact Real.log_le_log hQR0 hQP1
    have hqge : ℓx * c₀ < Real.log 2 + q := by
      have : P0 < Real.exp (Real.log 2 + q) := by
        rw [Real.exp_add, Real.exp_log (by norm_num), ← hQe]; exact hP0Q
      rw [hP0e] at this; exact Real.exp_lt_exp.1 this
    -- j
    obtain ⟨j, hj⟩ : ∃ n : ℕ, n = Nat.log b Q - 1 := ⟨_, rfl⟩
    have hlogQ : 2 ≤ Nat.log b Q := Nat.le_log_of_pow_le (by omega) hbQsq.le
    have hj1 : 1 ≤ j := by omega
    have hbj : b ^ (j + 1) ≤ Q := by
      rw [show j + 1 = Nat.log b Q by omega]; exact Nat.pow_log_le_self b (by omega)
    have hbj2 : Q < b ^ (j + 2) := by
      rw [show j + 2 = Nat.log b Q + 1 by omega]; exact Nat.lt_pow_succ_log_self (by omega) Q
    have hjQ : 2 * b ^ (2 * j + 1) ≤ Q ^ 2 := by
      calc 2 * b ^ (2 * j + 1) ≤ b * b ^ (2 * j + 1) := Nat.mul_le_mul_right _ hb2
        _ = (b ^ (j + 1)) ^ 2 := by ring
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hbj 2
    have hbe : ∀ n : ℕ, ((b ^ n : ℕ) : ℝ) = Real.exp (n * lb) := by
      intro n; rw [Nat.cast_pow, Real.exp_natCast_mul, hlb, Real.exp_log hb0]
    have hjlb1 : ((j : ℝ) + 1) * lb ≤ q := by
      have : ((b ^ (j + 1) : ℕ) : ℝ) ≤ Q := by exact_mod_cast hbj
      rw [hbe, hQe] at this
      have := Real.exp_le_exp.1 this; push_cast at this; linarith
    have hjlb2 : q < ((j : ℝ) + 2) * lb := by
      have : (Q : ℝ) < ((b ^ (j + 2) : ℕ) : ℝ) := by exact_mod_cast hbj2
      rw [hbe, hQe] at this
      have := Real.exp_lt_exp.1 this; push_cast at this; linarith
    have hjN : j < N := by
      have h1 : ((j : ℝ) + 1) * lb < ((N : ℝ) + 1) * lb := by
        have : ℓx * c₁ < ((N : ℝ) + 1) * lb := by
          rw [hℓx]
          have h3 : (2 * (N : ℝ) + 1) * c₁ < (2 * (N : ℝ) + 1) * (1 / 2) :=
            mul_lt_mul_of_pos_left hc₁ (by positivity)
          have : (2 * (N : ℝ) + 1) * c₁ < (N : ℝ) + 1 := by linarith
          rw [show (2 * (N : ℝ) + 1) * lb * c₁ = ((2 * (N : ℝ) + 1) * c₁) * lb by ring]
          exact mul_lt_mul_of_pos_right this hlbpos
        linarith
      have h2 : (j : ℝ) + 1 < (N : ℝ) + 1 := lt_of_mul_lt_mul_right h1 hlbpos.le
      have : (j : ℝ) < N := by linarith
      exact_mod_cast this
    -- K
    obtain ⟨kK, hkK⟩ : ∃ n : ℕ, n = ⌈(1 + σ / 2) * q / (ψ * lb)⌉₊ := ⟨_, rfl⟩
    have hψlb : 0 < ψ * lb := by positivity
    have hkK1 : (1 + σ / 2) * q ≤ ψ * lb * kK := by
      have : (1 + σ / 2) * q / (ψ * lb) ≤ (kK : ℝ) := by rw [hkK]; exact Nat.le_ceil _
      rw [div_le_iff₀ hψlb] at this; linarith
    have hkK2 : (kK : ℝ) < (1 + σ / 2) * q / (ψ * lb) + 1 := by
      rw [hkK]; exact Nat.ceil_lt_add_one (by positivity)
    have hkKN : kK + 1 ≤ N := by
      have h1 : (1 + σ / 2) * q / (ψ * lb) ≤ ν * (2 * (N : ℝ) + 1) / 2 := by
        rw [div_le_iff₀ hψlb, hν]
        have : (1 + σ / 2) * q ≤ (1 + σ / 2) * (ℓx * c₁) := mul_le_mul_of_nonneg_left hqle (by positivity)
        rw [hℓx] at this
        have e : (1 + σ / 2) * (2 * c₁) / ψ * (2 * (N : ℝ) + 1) / 2 * (ψ * lb) =
            (1 + σ / 2) * ((2 * (N : ℝ) + 1) * lb * c₁) := by field_simp
        rw [e]; exact this
      have h2 : (kK : ℝ) + 1 < (N : ℝ) + 1 := by linarith
      have : (kK : ℝ) < N := by linarith
      have : kK < N := by exact_mod_cast this
      omega
    -- the block lemma
    obtain ⟨t, ht⟩ : ∃ s, s = Real.exp (-(α * q)) := ⟨_, rfl⟩
    have htpos : 0 < t := by rw [ht]; exact Real.exp_pos _
    have hB := Q04_block b g hb2 hg pT hp0 hp1 H τ hT hH hτ0.le N Q j kK hQ2 hbQ hj1 hjN hjQ hkKN
      ((k : ℝ) / (bigB b : ℝ)) t htpos hDiag hPars
    -- the numerics
    have hT0 : τ 0 ^ kK ≤ Real.exp (-((1 + σ / 2) * q)) := by
      calc τ 0 ^ kK ≤ ((b : ℝ) ^ (-ψ)) ^ kK := pow_le_pow_left₀ hτ0.le hτψ kK
        _ = Real.exp (kK * (lb * (-ψ))) := by rw [Real.rpow_def_of_pos hb0, ← hlb, Real.exp_natCast_mul]
        _ ≤ _ := Real.exp_le_exp.2 (by linarith)
    have hA0 : 0 ≤ trigMass H τ := by unfold trigMass; positivity
    have hAK : trigMass H τ ^ kK ≤ cA * Real.exp (β₁ * q) := by
      calc trigMass H τ ^ kK ≤ ((b : ℝ) ^ lA') ^ kK := pow_le_pow_left₀ hA0 hA' kK
        _ = Real.exp (kK * (lb * lA')) := by rw [Real.rpow_def_of_pos hb0, ← hlb, Real.exp_natCast_mul]
        _ ≤ Real.exp (lA' * lb + β₁ * q) := by
            apply Real.exp_le_exp.2
            have h1 : (kK : ℝ) * (lb * lA') ≤ ((1 + σ / 2) * q / (ψ * lb) + 1) * (lb * lA') :=
              mul_le_mul_of_nonneg_right hkK2.le (by positivity)
            have e : ((1 + σ / 2) * q / (ψ * lb) + 1) * (lb * lA') = lA' * lb + β₁ * q := by
              rw [hβ₁]; field_simp; ring
            linarith
        _ = cA * Real.exp (β₁ * q) := by rw [Real.exp_add, hcA]
    have hm0 : 0 ≤ mw4 b g := by unfold mw4; positivity
    have hM4 : mw4 b g ^ j ≤ cM * Real.exp (-((1 + θw) * q)) := by
      calc mw4 b g ^ j ≤ ((b : ℝ) ^ (-(1 + θw))) ^ j := pow_le_pow_left₀ hm0 hm4 j
        _ = Real.exp (j * (lb * (-(1 + θw)))) := by
            rw [Real.rpow_def_of_pos hb0, ← hlb, Real.exp_natCast_mul]
        _ ≤ Real.exp (2 * (1 + θw) * lb + -((1 + θw) * q)) := by
            apply Real.exp_le_exp.2
            have : (1 + θw) * (q - 2 * lb) ≤ (1 + θw) * (j * lb) :=
              mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            linarith
        _ = cM * Real.exp (-((1 + θw) * q)) := by rw [Real.exp_add, hcM]
    have hℓ : Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q ≤ Lst := by
      have hlq : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) (by exact_mod_cast hQ2)
      have hnum0 : 0 ≤ Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) := by
        rcases Nat.eq_zero_or_pos H with h0 | h0
        · rw [h0]; simp
        · apply Real.log_nonneg
          have h6 : (1 : ℝ) ≤ H := by exact_mod_cast h0
          have h5 : (1 : ℝ) ≤ 2 * H := by linarith
          exact one_le_mul_of_one_le_of_one_le h5 (one_le_pow₀ hb1.le)
      have hnum : Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) ≤ Real.log (4 * b * xx b N) := by
        rcases Nat.eq_zero_or_pos H with h0 | h0
        · rw [h0]; simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.log_zero]
          exact Real.log_nonneg h4bx
        · apply Real.log_le_log (by positivity)
          unfold xx
          have hH' : (H : ℝ) ≤ 2 * b := by exact_mod_cast (by omega : H ≤ 2 * b)
          have : (0 : ℝ) ≤ (b : ℝ) ^ (2 * N + 1) := by positivity
          have := mul_le_mul_of_nonneg_right (by linarith : 2 * (H : ℝ) ≤ 4 * b) this
          linarith
      rw [hLst]
      calc Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q
          ≤ Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log 2 :=
            div_le_div_of_nonneg_left hnum0 hlog2 hlq
        _ ≤ _ := div_le_div_of_nonneg_right hnum hlog2.le
    have hnum := Q04_num q α pT σ θw β₁ η₁ Lst cA cM Q t (τ 0 ^ kK) (trigMass H τ ^ kK) (mw4 b g ^ j)
      (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) hq0 hQe (by rw [ht])
      (pow_nonneg hτ0.le _) hT0 (pow_nonneg hA0 _) hAK (pow_nonneg hm0 _) hM4 hℓ hLst0 hcA0 hcM0
      r1 hη_b r3 r4 hη_d
    have hexpq : Real.exp (-(η₁ * q)) ≤ Real.exp (η₁ * Real.log 2) * Real.exp (-(η₁ * c₀ * ℓx)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      have : η₁ * (ℓx * c₀) < η₁ * (Real.log 2 + q) := mul_lt_mul_of_pos_left hqge hη₁pos
      linarith
    have hB' : ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, Fk k p ≤
        (8 + 6 * cA + 4 * cM) * (1 + Lst) * Real.exp (-(η₁ * q)) := hB.trans hnum
    rw [hBfix, ← hCb] at *
    calc _ ≤ _ := hB'
      _ ≤ Cb * (1 + Lst) * (Real.exp (η₁ * Real.log 2) * Real.exp (-(η₁ * c₀ * ℓx))) :=
          mul_le_mul_of_nonneg_left hexpq (by positivity)
      _ = _ := by ring
  -- sum over the blocks for one shift
  have hshift : ∀ k : ℕ, ∑ p ∈ S, Fk k p ≤ (b * (2 * N + 1) : ℕ) * Bfix := by
    intro k
    have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ Ico i₀ i₁ := by
      intro p hp
      obtain ⟨_, hpP0, hpY⟩ := hSmem p hp
      have hap : a₀ ≤ p := by
        have : (a₀ : ℝ) < p := lt_of_le_of_lt ha₀le hpP0
        exact_mod_cast this.le
      simp only [mem_Ico]
      exact ⟨by rw [hi₀]; exact Nat.log_mono_right hap,
        by rw [hi₁]; exact Nat.lt_succ_of_le (Nat.log_mono_right hpY)⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hBfix0 : 0 ≤ Bfix := by rw [hBfix]; positivity
    calc _ ≤ ∑ i ∈ Ico i₀ i₁, ∑ p ∈ (Ico (2 ^ i) (2 * 2 ^ i)).filter Nat.Prime, Fk k p := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => hFk0 k p)
          intro p hp
          simp only [mem_filter] at hp
          obtain ⟨hpr, _, _⟩ := hSmem p hp.1
          simp only [mem_filter, mem_Ico]
          refine ⟨⟨?_, ?_⟩, hpr⟩
          · rw [← hp.2]; exact Nat.pow_log_le_self 2 hpr.ne_zero
          · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
            rw [hp.2, pow_succ] at this; omega
      _ ≤ ∑ _i ∈ Ico i₀ i₁, Bfix := Finset.sum_le_sum (fun i hi => hblock i hi k)
      _ = (Ico i₀ i₁).card * Bfix := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (b * (2 * N + 1) : ℕ) * Bfix := by
          apply mul_le_mul_of_nonneg_right _ hBfix0
          have : (Ico i₀ i₁).card ≤ b * (2 * N + 1) := by rw [Nat.card_Ico]; omega
          exact_mod_cast this
  -- the main term
  have hXW0 := Q04_XW_nonneg b g hg.1 N
  have hmainS : ∑ p ∈ S, XW b g N * (1 / (p : ℝ) ^ 2) ≤ 2 * XW b g N * xx b N ^ (-c₀) := by
    rw [← Finset.mul_sum]
    have h1 : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ n ∈ Ioc a₀ Y1, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro p hp
      obtain ⟨_, hpP0, hpY⟩ := hSmem p hp
      have : (a₀ : ℝ) < p := lt_of_le_of_lt ha₀le hpP0
      have : a₀ < p := by exact_mod_cast this
      exact mem_Ioc.2 ⟨this, hpY⟩
    have h2 := Q04_inv_sq a₀ ha₀1 Y1
    have h3 : (1 : ℝ) / a₀ ≤ 2 * xx b N ^ (-c₀) := by
      rw [Real.rpow_neg hx0, ← hP0]
      have ha₀pos : (0 : ℝ) < a₀ := by exact_mod_cast ha₀1
      rw [div_le_iff₀ ha₀pos]
      have hP0pos : 0 < P0 := by linarith
      rw [show 2 * P0⁻¹ * (a₀ : ℝ) = 2 * a₀ / P0 by field_simp, le_div_iff₀ hP0pos]
      linarith
    calc XW b g N * ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ XW b g N * (2 * xx b N ^ (-c₀)) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hXW0
      _ = _ := by ring
  -- the error term
  have herr : ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ p ∈ S, Fk k p ≤
      xx b N ^ (-(η₁ * c₀ / 2)) := by
    have hBfix0 : 0 ≤ Bfix := by rw [hBfix]; positivity
    have h1 : ∑ k ∈ range (bigB b), ∑ p ∈ S, Fk k p ≤ (bigB b : ℝ) * ((b * (2 * N + 1) : ℕ) * Bfix) := by
      calc _ ≤ ∑ _k ∈ range (bigB b), ((b * (2 * N + 1) : ℕ) * Bfix) := Finset.sum_le_sum (fun k _ => hshift k)
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have hLstN : 1 + Lst ≤ C₂ * ((N : ℝ) + 1) := by
      rw [hLst, hC₂, Real.log_mul (by positivity) (by positivity), hx, Real.log_exp, hℓx]
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have e1 : (Real.log (4 * b) + (2 * (N : ℝ) + 1) * lb) / Real.log 2 ≤
          (Real.log (4 * b) + 2 * lb) / Real.log 2 * ((N : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
        linarith [mul_nonneg hlog4b hN0, mul_nonneg hlbpos.le hN0]
      have e2 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
      have hY0 := div_nonneg (by linarith : 0 ≤ Real.log (4 * b) + 2 * lb) hlog2.le
      have := mul_nonneg hY0 hN0
      linarith
    have hρN : Real.exp (-(η₁ * c₀ * ℓx)) ≤ ρ ^ N * Real.exp (ℓx * (-(η₁ * c₀ / 2))) := by
      rw [hρ, ← Real.exp_natCast_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [hℓx]
      have : 0 ≤ η₁ * c₀ * lb := by positivity
      linarith
    have hfin := hNd N hNd'
    have hdiv0 : (0 : ℝ) ≤ ((bigB b).divisors.card : ℝ) := by positivity
    calc ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ p ∈ S, Fk k p
        ≤ ((bigB b).divisors.card : ℝ) * ((bigB b : ℝ) * ((b * (2 * N + 1) : ℕ) * Bfix)) :=
          mul_le_mul_of_nonneg_left h1 hdiv0
      _ ≤ ((bigB b).divisors.card : ℝ) * ((bigB b : ℝ) * ((b : ℝ) * (2 * ((N : ℝ) + 1)) *
            (Cb * (C₂ * ((N : ℝ) + 1)) * Real.exp (η₁ * Real.log 2) *
              (ρ ^ N * Real.exp (ℓx * (-(η₁ * c₀ / 2))))))) := by
          apply mul_le_mul_of_nonneg_left _ hdiv0
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hBfix]
          have hb2N : ((b * (2 * N + 1) : ℕ) : ℝ) ≤ (b : ℝ) * (2 * ((N : ℝ) + 1)) := by
            push_cast
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e1 : Cb * (1 + Lst) ≤ Cb * (C₂ * ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hLstN hCb0
          apply mul_le_mul hb2N _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul_of_nonneg_right e1 (by positivity)) hρN (by positivity) (by positivity)
      _ = Cf * ((N : ℝ) + 1) ^ 2 * ρ ^ N * xx b N ^ (-(η₁ * c₀ / 2)) := by
          rw [hCf, hxr]; ring
      _ ≤ 1 * xx b N ^ (-(η₁ * c₀ / 2)) :=
          mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hx0 _)
      _ = _ := one_mul _
  -- assembly
  unfold SqW
  rw [← hS]
  calc ∑ p ∈ S, AW b g N (p ^ 2) ≤ ∑ p ∈ S, (XW b g N * (1 / (p : ℝ) ^ 2) +
        ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), Fk k p) := Finset.sum_le_sum hAWp
    _ = ∑ p ∈ S, XW b g N * (1 / (p : ℝ) ^ 2) +
        ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ p ∈ S, Fk k p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (s := S) (t := range (bigB b))]
    _ ≤ _ := add_le_add hmainS herr

end Omega3
