import Omega3.Statements
import Palprimes.TL1.Asymp

/-!
# L15: Lemma W_w, the ranges (r238 §2.8). Sub-blueprint: `L15_PLAN.md`.
-/

namespace Omega3

open Finset Real Palprimes

lemma L15_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma L15_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) : ‖Gg b g t‖ ≤ 1 := by
  unfold Gg
  calc ‖∑ a ∈ range b, (g a : ℂ) * ee (a * t)‖ ≤ ∑ a ∈ range b, ‖(g a : ℂ) * ee (a * t)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ range b, g a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, L15_norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.1 a)]
    _ = 1 := hg.2

lemma L15_fg_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N M : ℕ) (hM : M ≤ N) (α : ℝ) :
    ‖fg b g N α‖ ≤ ∏ n ∈ Icc 1 M, ‖Gg b g ((cK b N n : ℝ) * α)‖ := by
  unfold fg
  have hJ : Icc 1 M ⊆ range (N + 1) := by
    intro k hk; simp only [mem_Icc, mem_range] at hk ⊢; omega
  rw [← Finset.prod_sdiff hJ, norm_mul, norm_prod (Icc 1 M)]
  have h1 : ‖∏ k ∈ range (N + 1) \ Icc 1 M, Gg b g ((cK b N k : ℝ) * α)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => L15_Gg_norm_le b g hg _)
  calc _ ≤ 1 * ∏ k ∈ Icc 1 M, ‖Gg b g ((cK b N k : ℝ) * α)‖ :=
        mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := one_mul _

/-- Small moduli: Lemma K gives `L1*(q) ≤ q · E` for `q < b^{L₁}`. -/
lemma L15_small (b : ℕ) (g : ℕ → ℝ) (hb : 2 ≤ b) (hg : IsDigitWeight b g) (hK : LemmaKStmt b g)
    (N q L₁ k : ℕ) (hN : 3 ≤ N) (hq : 2 ≤ q) (hqL : q < b ^ L₁) (hL : 1 ≤ L₁)
    (hqB : Nat.Coprime q (bigB b)) :
    L1farey b g N q ((k : ℝ) / (bigB b : ℝ)) ≤
      q * Real.exp (-(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / ((b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2)) := by
  set E := Real.exp (-(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / ((b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold L1farey
  have hterm : ∀ h ∈ redRes q, ‖fg b g N ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))‖ ≤ E := by
    intro h hh
    simp only [redRes, mem_filter, mem_range] at hh
    have hco : Nat.Coprime q ((h : ℤ).natAbs * bigB b) := by
      rw [Int.natAbs_natCast]; exact Nat.Coprime.mul_right hh.2.symm hqB
    have hKq := hK N q (N - 1) (h : ℤ) (k : ℤ) hq hco (by omega) (by omega)
    simp only [Int.cast_natCast] at hKq
    have h1 := L15_fg_le b g hg N (N - 1) (by omega) ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))
    refine (h1.trans hKq).trans ?_
    apply Real.exp_le_exp.2
    have hLq : max 1 (Nat.log b q) ≤ L₁ := max_le hL (Nat.log_lt_of_lt_pow (by omega) hqL).le
    have hdiv : (N - 2) / L₁ ≤ (N - 1 - 1) / max 1 (Nat.log b q) := by
      rw [show N - 1 - 1 = N - 2 by omega]
      exact Nat.div_le_div_left hLq (by omega)
    have hdivR : (((N - 2) / L₁ : ℕ) : ℝ) ≤ (((N - 1 - 1) / max 1 (Nat.log b q) : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    have hgg : 0 ≤ g 0 * g 1 := mul_nonneg (hg.1 0) (hg.1 1)
    have hBc : 0 < (b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_div_iff_of_pos_right hBc]
    nlinarith
  calc ∑ h ∈ redRes q, ‖fg b g N ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))‖ ≤ ∑ _h ∈ redRes q, E :=
        Finset.sum_le_sum hterm
    _ = #(redRes q) * E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q * E := by
        apply mul_le_mul_of_nonneg_right _ hE0
        have : #(redRes q) ≤ q := by
          calc #(redRes q) ≤ #(range q) := Finset.card_filter_le _ _
            _ = q := card_range q
        exact_mod_cast this

/-- Middle and window moduli: one dyadic block, weighted by `3^ω(q)/q`. -/
lemma L15_block (b : ℕ) (g : ℕ → ℝ) (N i : ℕ) (β C3 η e : ℝ) (hC3 : 0 ≤ C3) (hη : 0 ≤ η)
    (hC3w : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n ≤ C3 * (n : ℝ) ^ η)
    (hL1 : ∀ d, 0 ≤ L1farey b g N d β)
    (hSS : blockL1 b g N (2 ^ i) β ≤ ((2 ^ i : ℕ) : ℝ) * ((2 ^ i : ℕ) : ℝ) ^ e)
    (c₅ : ℝ) (he : η + e ≤ -c₅) :
    ∑ q ∈ (Ico (2 ^ i) (2 * 2 ^ i)).filter (fun d => Nat.Coprime d b),
        (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1farey b g N q β ≤
      C3 * (2 : ℝ) ^ η * ((2 : ℝ) ^ (-c₅)) ^ i := by
  set D : ℕ := 2 ^ i with hD
  have hD1 : 1 ≤ D := Nat.one_le_two_pow
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDpos : (0 : ℝ) < D := by linarith
  set w : ℝ := C3 * (2 * (D : ℝ)) ^ η / D with hw
  have hterm : ∀ q ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b),
      (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1farey b g N q β ≤ w * L1farey b g N q β := by
    intro q hq
    simp only [mem_filter, mem_Ico] at hq
    apply mul_le_mul_of_nonneg_right _ (hL1 q)
    have hq1 : 1 ≤ q := le_trans hD1 hq.1.1
    have hqR : (D : ℝ) ≤ q := by exact_mod_cast hq.1.1
    have hq2 : (q : ℝ) ≤ 2 * D := by exact_mod_cast hq.1.2.le
    have hqpos : (0 : ℝ) < q := by linarith
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤ C3 * (q : ℝ) ^ η / q :=
          div_le_div_of_nonneg_right (hC3w q hq1) hqpos.le
      _ ≤ C3 * (2 * (D : ℝ)) ^ η / q :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hqpos.le hq2 hη) hC3) hqpos.le
      _ ≤ w := div_le_div_of_nonneg_left (by positivity) hDpos hqR
  calc _ ≤ ∑ q ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), w * L1farey b g N q β :=
        Finset.sum_le_sum hterm
    _ = w * blockL1 b g N D β := by rw [← Finset.mul_sum]; rfl
    _ ≤ w * ((D : ℝ) * (D : ℝ) ^ e) := mul_le_mul_of_nonneg_left hSS (by positivity)
    _ = C3 * (2 : ℝ) ^ η * (D : ℝ) ^ (η + e) := by
        rw [hw, Real.mul_rpow (by norm_num) hDpos.le, Real.rpow_add hDpos]
        field_simp
    _ ≤ C3 * (2 : ℝ) ^ η * (D : ℝ) ^ (-c₅) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hDR he) (by positivity)
    _ = C3 * (2 : ℝ) ^ η * ((2 : ℝ) ^ (-c₅)) ^ i := by
        congr 1
        rw [hD, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]

lemma L15_nat_aux (r N : ℕ) (hN : 3 ≤ N) (hr : r * r ≤ N) : (r - 3) * r ≤ N - 2 := by
  rcases Nat.lt_or_ge r 3 with h | h
  · have : r - 3 = 0 := by omega
    rw [this]; omega
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
    rw [show t + 3 - 3 = t by omega]
    have : t * (t + 3) + 2 ≤ (t + 3) * (t + 3) := by nlinarith
    omega

set_option maxHeartbeats 1000000 in
theorem itemL15 : ItemL15 := by
  intro b g θ κ θ₀ hb hg hg0 hg1 hθ₀ hθ₀θ hθ hκ hK hSS _hTL A
  classical
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hθpos : 0 < θ := lt_trans hθ₀ hθ₀θ
  -- constants
  set η : ℝ := min (κ / (4 * θ)) 1 with hηdef
  have hηpos : 0 < η := lt_min (by positivity) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηk : η ≤ κ / (4 * θ) := min_le_left _ _
  obtain ⟨C3, hC3⟩ := three_pow_omega_le_rpow η hηpos
  have hC30 : 0 ≤ C3 := by
    have := hC3 1 le_rfl
    simp at this; linarith
  obtain ⟨D₀, hD₀⟩ := hSS (κ / (4 * θ)) (by positivity)
  set c₅ : ℝ := κ / (2 * θ) with hc₅
  have hc₅pos : 0 < c₅ := by positivity
  set ρ₂ : ℝ := (2 : ℝ) ^ (-c₅) with hρ₂
  have hρ₂0 : 0 < ρ₂ := by positivity
  have hρ₂1 : ρ₂ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set Bc : ℝ := (b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2 with hBc
  have hBcpos : 0 < Bc := by positivity
  set cK : ℝ := g 0 * g 1 / Bc with hcK
  have hcKpos : 0 < cK := by positivity
  set lnb : ℝ := Real.log b with hlnb
  have hlnbpos : 0 < lnb := Real.log_pos hb1
  set m : ℕ := ⌈(2 * lnb + 1) / cK⌉₊ + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmc : 2 * lnb + 1 ≤ cK * m := by
    have h1 : (2 * lnb + 1) / cK ≤ (⌈(2 * lnb + 1) / cK⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2 * lnb + 1) / cK⌉₊ : ℝ) ≤ m := by rw [hmdef]; push_cast; linarith
    rw [div_le_iff₀ hcKpos] at h1
    nlinarith
  set ρ₄ : ℝ := max (Real.exp (-1)) ρ₂ with hρ₄
  have hρ₄0 : 0 ≤ ρ₄ := le_trans hρ₂0.le (le_max_right _ _)
  have hρ₄1 : ρ₄ < 1 := max_lt (by have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this) hρ₂1
  set Kt : ℝ := C3 * Real.exp (3 * cK * m) + C3 * (2 : ℝ) ^ η / (1 - ρ₂) with hKt
  have hKt0 : 0 ≤ Kt := by
    have : 0 < 1 - ρ₂ := by linarith
    positivity
  obtain ⟨n₀, hn₀⟩ := eventually_poly_geom (Kt * (2 * (m : ℝ) ^ 2 * lnb) ^ A) (2 * A) ρ₄ hρ₄0 hρ₄1 1 one_pos
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt (2 * D₀) hb1
  set Lr : ℕ := max (max 1 n₀) L₀ with hLr
  refine ⟨max 3 (m * Lr * (m * Lr)), ?_⟩
  intro N hN k hk
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  set r := Nat.sqrt N with hr
  set L₁ := r / m with hL₁
  have hmLr : m * Lr ≤ r := Nat.le_sqrt.2 (le_trans (le_max_right _ _) hN)
  have hLrL : Lr ≤ L₁ := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hmLr)
  have hL1 : 1 ≤ L₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLrL
  have hLn₀ : n₀ ≤ L₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLrL
  have hLL₀ : L₀ ≤ L₁ := le_trans (le_max_right _ _) hLrL
  set Q₁ : ℕ := b ^ L₁ with hQ₁
  have hQ₁R : ((Q₁ : ℕ) : ℝ) = Real.exp (L₁ * lnb) := by
    rw [hQ₁, Nat.cast_pow, Real.exp_natCast_mul, Real.exp_log hb0]
  have hD₀Q : 2 * D₀ < (Q₁ : ℝ) := by
    calc 2 * D₀ < (b : ℝ) ^ L₀ := hL₀
      _ ≤ (b : ℝ) ^ L₁ := pow_le_pow_right₀ hb1.le hLL₀
      _ = (Q₁ : ℝ) := by rw [hQ₁, Nat.cast_pow]
  set x := xx b N with hx
  have hx1 : 1 ≤ x := by rw [hx]; unfold xx; exact one_le_pow₀ hb1.le
  set Y := ⌊x ^ θ⌋₊ with hY
  have hY1 : 1 ≤ Y := Nat.one_le_floor_iff _ |>.2 (Real.one_le_rpow hx1 hθpos.le)
  have hYx : (Y : ℝ) ≤ x ^ θ := Nat.floor_le (by positivity)
  set β : ℝ := (k : ℝ) / (bigB b : ℝ) with hβ
  have hL1f : ∀ d, 0 ≤ L1farey b g N d β := fun d => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set E : ℝ := Real.exp (-(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / Bc) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set S := (Icc 2 Y).filter (fun q => Nat.Coprime q (bigB b)) with hS
  set w : ℕ → ℝ := fun q => (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1farey b g N q β with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q => mul_nonneg (by positivity) (hL1f q)
  have hFW : FareyW b g N Y β = ∑ q ∈ S, w q := rfl
  -- small moduli
  have hsmall : ∑ q ∈ S.filter (fun q => q < Q₁), w q ≤ (Q₁ : ℝ) * (C3 * Q₁ * E) := by
    have hpt : ∀ q ∈ S.filter (fun q => q < Q₁), w q ≤ C3 * Q₁ * E := by
      intro q hq
      simp only [hS, mem_filter, mem_Icc] at hq
      have hq1 : 1 ≤ q := by omega
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hsm := L15_small b g hb2 hg hK N q L₁ k hN3 hq.1.1.1 hq.2 hL1 hq.1.2
      have h3 := hC3 q hq1
      have hqη : (q : ℝ) ^ η ≤ q := rpow_le_self_of_one_le _ _ (by exact_mod_cast hq1) hηpos.le hη1
      have hqQ : (q : ℝ) ≤ Q₁ := by exact_mod_cast hq.2.le
      calc w q ≤ (C3 * (q : ℝ) ^ η / q) * (q * E) := by
            apply mul_le_mul (div_le_div_of_nonneg_right h3 hqpos.le) hsm (hL1f q) (by positivity)
        _ = C3 * (q : ℝ) ^ η * E := by field_simp
        _ ≤ C3 * Q₁ * E := by
            apply mul_le_mul_of_nonneg_right _ hE0
            exact mul_le_mul_of_nonneg_left (hqη.trans hqQ) hC30
    calc _ ≤ ∑ _q ∈ S.filter (fun q => q < Q₁), C3 * Q₁ * E := Finset.sum_le_sum hpt
      _ ≤ ∑ _q ∈ range Q₁, C3 * Q₁ * E := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq; simp only [mem_filter] at hq; exact mem_range.2 hq.2
          · intro _ _ _; positivity
      _ = (Q₁ : ℝ) * (C3 * Q₁ * E) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
  -- middle and window moduli
  set i₀ := Nat.log 2 Q₁ with hi₀
  set I := Nat.log 2 Y + 1 with hI
  have hmaps : ∀ q ∈ S.filter (fun q => ¬ q < Q₁), Nat.log 2 q ∈ Ico i₀ I := by
    intro q hq
    simp only [hS, mem_filter, mem_Icc, not_lt] at hq
    simp only [mem_Ico]
    exact ⟨Nat.log_mono_right hq.2, Nat.lt_succ_of_le (Nat.log_mono_right hq.1.1.2)⟩
  have hi₀L : L₁ ≤ i₀ := by
    have : Nat.log 2 (2 ^ L₁) ≤ Nat.log 2 Q₁ :=
      Nat.log_mono_right (Nat.pow_le_pow_left (by omega) L₁)
    rwa [Nat.log_pow (by norm_num)] at this
  have hfib : ∀ i ∈ Ico i₀ I, ∑ q ∈ (S.filter (fun q => ¬ q < Q₁)).filter (fun q => Nat.log 2 q = i), w q ≤
      C3 * (2 : ℝ) ^ η * ρ₂ ^ i := by
    intro i hi
    simp only [mem_Ico] at hi
    have hsub : (S.filter (fun q => ¬ q < Q₁)).filter (fun q => Nat.log 2 q = i) ⊆
        (Ico (2 ^ i) (2 * 2 ^ i)).filter (fun d => Nat.Coprime d b) := by
      intro q hq
      simp only [hS, mem_filter, mem_Icc, not_lt] at hq
      simp only [mem_filter, mem_Ico]
      have hq0 : q ≠ 0 := by omega
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hq.2]; exact Nat.pow_log_le_self 2 hq0
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
        rw [hq.2, pow_succ] at this; omega
      · exact Nat.Coprime.coprime_dvd_right (by unfold bigB; exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl) hq.1.1.2
    have hDlo : D₀ ≤ ((2 ^ i : ℕ) : ℝ) := by
      have h1 : Q₁ < 2 ^ (i₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) Q₁
      have h2 : 2 ^ i₀ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
      have h3 : (Q₁ : ℝ) < 2 * ((2 ^ i : ℕ) : ℝ) := by
        have : Q₁ < 2 * 2 ^ i := by rw [pow_succ] at h1; omega
        exact_mod_cast this
      linarith
    have hDhi : ((2 ^ i : ℕ) : ℝ) ≤ x ^ θ := by
      have h1 : 2 ^ i ≤ Y :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_log_le_self 2 (by omega))
      calc ((2 ^ i : ℕ) : ℝ) ≤ Y := by exact_mod_cast h1
        _ ≤ x ^ θ := hYx
    have hSSi := hD₀ N (2 ^ i) ⟨i, rfl⟩ hDlo hDhi β
    have hblk := L15_block b g N i β C3 η (-κ / θ + κ / (4 * θ)) hC30 hηpos.le hC3 hL1f hSSi c₅ (by
      rw [hc₅]
      have : κ / (4 * θ) + (-κ / θ + κ / (4 * θ)) = -(κ / (2 * θ)) := by field_simp; ring
      linarith)
    calc _ ≤ ∑ q ∈ (Ico (2 ^ i) (2 * 2 ^ i)).filter (fun d => Nat.Coprime d b), w q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)
      _ ≤ _ := hblk
  have hmid : ∑ q ∈ S.filter (fun q => ¬ q < Q₁), w q ≤ C3 * (2 : ℝ) ^ η / (1 - ρ₂) * ρ₂ ^ L₁ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ i ∈ Ico i₀ I, C3 * (2 : ℝ) ^ η * ρ₂ ^ i := Finset.sum_le_sum hfib
      _ = C3 * (2 : ℝ) ^ η * ∑ i ∈ Ico i₀ I, ρ₂ ^ i := by rw [Finset.mul_sum]
      _ ≤ C3 * (2 : ℝ) ^ η * (ρ₂ ^ i₀ / (1 - ρ₂)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hρ₂0.le hρ₂1) (by positivity)
      _ ≤ C3 * (2 : ℝ) ^ η * (ρ₂ ^ L₁ / (1 - ρ₂)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hρ₂0.le hρ₂1.le hi₀L)
            (by linarith)
      _ = C3 * (2 : ℝ) ^ η / (1 - ρ₂) * ρ₂ ^ L₁ := by ring
  -- the small-moduli exponent
  have hsdiv : m * (r - 3) ≤ (N - 2) / L₁ := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have h1 : m * L₁ ≤ r := Nat.mul_div_le r m
    have h2 : r * r ≤ N := Nat.sqrt_le N
    have h3 := L15_nat_aux r N hN3 h2
    calc m * (r - 3) * L₁ = (r - 3) * (m * L₁) := by ring
      _ ≤ (r - 3) * r := Nat.mul_le_mul_left _ h1
      _ ≤ N - 2 := h3
  have hLr' : L₁ ≤ r := Nat.div_le_self r m
  have hexpo : 2 * ((L₁ : ℝ) * lnb) + (-(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / Bc) ≤
      3 * cK * m + -(L₁ : ℝ) := by
    have hs : ((m : ℝ) * ((r : ℝ) - 3)) ≤ (((N - 2) / L₁ : ℕ) : ℝ) := by
      have h1 : ((m * (r - 3) : ℕ) : ℝ) ≤ (((N - 2) / L₁ : ℕ) : ℝ) := by exact_mod_cast hsdiv
      have h2 : ((r : ℝ) - 3) ≤ ((r - 3 : ℕ) : ℝ) := by
        rcases Nat.lt_or_ge r 3 with h | h
        · have : (r : ℝ) < 3 := by exact_mod_cast h
          have : (0 : ℝ) ≤ ((r - 3 : ℕ) : ℝ) := by positivity
          linarith
        · rw [Nat.cast_sub h]; norm_num
      push_cast at h1
      nlinarith [(by positivity : (0 : ℝ) ≤ m)]
    have hcKs : -(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / Bc = -cK * (((N - 2) / L₁ : ℕ) : ℝ) := by
      rw [hcK]; ring
    rw [hcKs]
    have hLrR : (L₁ : ℝ) ≤ r := by exact_mod_cast hLr'
    have h5 : cK * ((m : ℝ) * ((r : ℝ) - 3)) ≤ cK * (((N - 2) / L₁ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hs hcKpos.le
    have h6 : (2 * lnb + 1) * (r : ℝ) ≤ cK * m * r := mul_le_mul_of_nonneg_right hmc (by positivity)
    have h7 : (L₁ : ℝ) * lnb ≤ r * lnb := mul_le_mul_of_nonneg_right hLrR hlnbpos.le
    nlinarith
  have hsmall' : (Q₁ : ℝ) * (C3 * Q₁ * E) ≤ C3 * Real.exp (3 * cK * m) * Real.exp (-1) ^ L₁ := by
    have : (Q₁ : ℝ) * (C3 * Q₁ * E) = C3 * Real.exp (2 * ((L₁ : ℝ) * lnb) +
        (-(g 0 * g 1) * (((N - 2) / L₁ : ℕ) : ℝ) / Bc)) := by
      rw [hQ₁R, hE, Real.exp_add, show 2 * ((L₁ : ℝ) * lnb) = (L₁ : ℝ) * lnb + (L₁ : ℝ) * lnb by ring,
        Real.exp_add]; ring
    rw [this, ← Real.exp_natCast_mul, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC30
    apply Real.exp_le_exp.2
    linarith
  have hρ₄a : Real.exp (-1) ^ L₁ ≤ ρ₄ ^ L₁ :=
    pow_le_pow_left₀ (Real.exp_pos _).le (le_max_left _ _) L₁
  have hρ₄b : ρ₂ ^ L₁ ≤ ρ₄ ^ L₁ := pow_le_pow_left₀ hρ₂0.le (le_max_right _ _) L₁
  have htot : FareyW b g N Y β ≤ Kt * ρ₄ ^ L₁ := by
    rw [hFW, ← Finset.sum_filter_add_sum_filter_not S (fun q => q < Q₁)]
    have h1 : 0 ≤ C3 * Real.exp (3 * cK * m) := by positivity
    have h2 : 0 ≤ C3 * (2 : ℝ) ^ η / (1 - ρ₂) := by
      have : 0 < 1 - ρ₂ := by linarith
      positivity
    calc _ ≤ C3 * Real.exp (3 * cK * m) * Real.exp (-1) ^ L₁ +
          C3 * (2 : ℝ) ^ η / (1 - ρ₂) * ρ₂ ^ L₁ := add_le_add (hsmall.trans hsmall') hmid
      _ ≤ C3 * Real.exp (3 * cK * m) * ρ₄ ^ L₁ + C3 * (2 : ℝ) ^ η / (1 - ρ₂) * ρ₄ ^ L₁ :=
          add_le_add (mul_le_mul_of_nonneg_left hρ₄a h1) (mul_le_mul_of_nonneg_left hρ₄b h2)
      _ = Kt * ρ₄ ^ L₁ := by rw [hKt]; ring
  -- log x is polynomial in L₁
  have hlogx : Real.log x = (2 * (N : ℝ) + 1) * lnb := by
    rw [hx]; unfold xx; rw [Real.log_pow]; push_cast; ring
  have hlogpos : 0 < Real.log x := by rw [hlogx]; positivity
  have hNL : 2 * (N : ℝ) + 1 ≤ 2 * (m : ℝ) ^ 2 * ((L₁ : ℝ) + 1) ^ 2 := by
    have h1 : N < (r + 1) * (r + 1) := Nat.lt_succ_sqrt N
    have h2 : r < m * (L₁ + 1) := by
      have := Nat.lt_mul_div_succ r (by omega : 0 < m); rw [hL₁]; linarith
    have h3 : r + 1 ≤ m * (L₁ + 1) := h2
    have h4 : (r + 1) * (r + 1) ≤ (m * (L₁ + 1)) * (m * (L₁ + 1)) := Nat.mul_le_mul h3 h3
    have h5 : N + 1 ≤ (m * (L₁ + 1)) * (m * (L₁ + 1)) := by omega
    have h6 : ((N : ℝ) + 1) ≤ ((m : ℝ) * ((L₁ : ℝ) + 1)) * ((m : ℝ) * ((L₁ : ℝ) + 1)) := by
      exact_mod_cast h5
    nlinarith
  have hlogA : Real.log x ^ A ≤ (2 * (m : ℝ) ^ 2 * lnb) ^ A * ((L₁ : ℝ) + 1) ^ (2 * A) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ hlogpos.le
    rw [hlogx]
    have := mul_le_mul_of_nonneg_right hNL hlnbpos.le
    nlinarith
  have hfin := hn₀ L₁ hLn₀
  rw [le_div_iff₀ (pow_pos hlogpos A)]
  calc FareyW b g N Y β * Real.log x ^ A ≤ Kt * ρ₄ ^ L₁ * Real.log x ^ A :=
        mul_le_mul_of_nonneg_right htot (pow_nonneg hlogpos.le _)
    _ ≤ Kt * ρ₄ ^ L₁ * ((2 * (m : ℝ) ^ 2 * lnb) ^ A * ((L₁ : ℝ) + 1) ^ (2 * A)) :=
        mul_le_mul_of_nonneg_left hlogA (mul_nonneg hKt0 (pow_nonneg hρ₄0 _))
    _ = Kt * (2 * (m : ℝ) ^ 2 * lnb) ^ A * ((L₁ : ℝ) + 1) ^ (2 * A) * ρ₄ ^ L₁ := by ring
    _ ≤ 1 := hfin

end Omega3
