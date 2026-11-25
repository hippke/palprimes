import KappaOmega2.Items.QK04_Aux

/-!
# QK04_Cut: square moduli `p² > x^θ/2` by the cut (route E′ for the large values, Lemma 2.8_κ for the small ones)
-/

namespace KappaOmega2

open Finset Real Palprimes

set_option maxHeartbeats 4000000 in
lemma QK04_cut (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ a η η₁ c₁ Ce : ℝ)
    (hb : 3 ≤ b) (hg : IsDigitWeight b g) (hp1 : 1 / 2 ≤ p) (hp2 : p < 1) (hH : H ≤ b * (b - 1))
    (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (hτ0 : 0 < τ 0) (hτψ : τ 0 ≤ (b : ℝ) ^ (-ψ))
    (hψ : 0 ≤ ψ) (hA : trigMass H τ ≤ 1) (hm4 : mw4 b g ≤ 1 / (b : ℝ)) (ha : 0 < a) (hη : 0 < η)
    (hB1 : 4 * a + η < 3 / 20) (hD1 : c₁ + η < 7 / 20 * ψ + 3 / 10 * p + a * (1 - p))
    (hE1 : η < a * (1 - p)) (hη₁ : η₁ ≤ η / 2)
    (hCe0 : 0 ≤ Ce) (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ (η / 4))
    (h28 : Lemma28KStmt) (hPar : SqParsevalKStmt) (hKm : KmidStmt)
    (N : ℕ) (hN : 5 ≤ N) (β : ℝ) (i : ℕ) (B : Finset ℕ)
    (hB : ∀ q ∈ B, q.Prime ∧ ¬ q ∣ bigB b ∧ 2 ^ i ≤ q ∧ q < 2 * 2 ^ i ∧ (q : ℝ) ≤ xx b N ^ c₁ ∧
      6 * WK b N ≤ q ^ 2 ∧ q ^ 2 < b ^ (2 * N + 1)) :
    ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖ ≤
      (400 * Real.exp (Real.log b * (2 * ψ + 2)) / min (η / 2) 1 + 400 * Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) +
        3 * b) * Real.exp (-(η₁ * ((2 * (N : ℝ) + 1) * Real.log b))) := by
  classical
  have hb1 : 1 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1R : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set lb := Real.log b with hlb
  have hlbpos : 0 < lb := Real.log_pos hb1R
  set n : ℝ := 2 * (N : ℝ) + 1 with hn
  have hn0 : 0 ≤ n := by positivity
  set L := n * lb with hL
  have hL0 : 0 ≤ L := by positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  have hxx : xx b N = Real.exp L := by rw [hL, hn, hlb]; exact LK10_xx_exp b N hb1
  obtain ⟨hs1, hs2, hs3⟩ := LK10_shape N
  set m := mK N with hm
  set ℓ := ellK N with hℓ
  have hm1 : 1 ≤ m := by omega
  have hℓ4 : 4 ≤ ℓ := by omega
  have hW : WK b N = b ^ ℓ := rfl
  have hW16 : 16 ≤ WK b N := by
    rw [hW]
    calc 16 ≤ 3 ^ 4 := by norm_num
      _ ≤ b ^ 4 := Nat.pow_le_pow_left hb 4
      _ ≤ b ^ ℓ := Nat.pow_le_pow_right (by omega) hℓ4
  have hW1 : 1 ≤ WK b N := by omega
  have hW0 : (0 : ℝ) < WK b N := by exact_mod_cast hW1
  have hWR : (WK b N : ℝ) = (b : ℝ) ^ ℓ := by rw [hW, Nat.cast_pow]
  obtain ⟨S, κ, hS, hκ0, hκM, hκ00, hκA⟩ := hKm (WK b N) p hW16 hp1 hp2
  obtain ⟨hWge, _⟩ := QK04_W_bounds b N hb1
  rw [← hlb, ← hn, ← hL] at hWge
  -- the shape in ℝ
  have hmR1 : 20 * (m : ℝ) ≤ 7 * n := by
    have h : ((20 * m : ℕ) : ℝ) ≤ ((7 * (2 * N + 1) : ℕ) : ℝ) := by exact_mod_cast hs1
    push_cast at h; rw [hn]; linarith
  have hmR2 : 7 * n < 20 * (m : ℝ) + 20 := by
    have h : ((7 * (2 * N + 1) : ℕ) : ℝ) < ((20 * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hs2
    push_cast at h; rw [hn]; linarith
  have hℓR : (ℓ : ℝ) + 2 * m = n := by
    have h : ((ℓ + 2 * m : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast hs3
    push_cast at h; rw [hn]; linarith
  have hlogW : Real.log (WK b N) = ℓ * lb := by rw [hWR, Real.log_pow]
  have hℓL : 3 / 10 * L ≤ ℓ * lb := by
    rw [← hlogW, ← Real.log_exp (3 / 10 * L)]; exact Real.log_le_log (Real.exp_pos _) hWge
  -- empty case
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · rw [hBe, Finset.sum_empty]; positivity
  set Q : ℕ := 2 ^ i with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  set δ := Real.log Q with hδ
  have hQe : (Q : ℝ) = Real.exp δ := (Real.exp_log hQpos).symm
  have hδ0 : 0 ≤ δ := Real.log_nonneg (by exact_mod_cast hQ1)
  have hδhi : δ ≤ L * c₁ := by
    obtain ⟨q, hq⟩ := hBne
    obtain ⟨_, _, hq1, _, hqx, _⟩ := hB q hq
    have h1 : (Q : ℝ) ≤ xx b N ^ c₁ := le_trans (by exact_mod_cast hq1) hqx
    rw [hxr, hQe] at h1; exact Real.exp_le_exp.1 h1
  have hcardB : (#B : ℝ) ≤ Q := by
    have hsub : B ⊆ Ico Q (2 * Q) := by
      intro q hq; obtain ⟨_, _, hq1, hq2, _⟩ := hB q hq; exact mem_Ico.2 ⟨hq1, hq2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast (show #B ≤ Q by omega)
  -- the inner block lengths
  have hjex : ∀ q ∈ B, ∃ j : ℕ, 6 * WK b N * b ^ (2 * j) ≤ q ^ 2 ∧ q ^ 2 < 6 * WK b N * b ^ (2 * j + 2) :=
    fun q hq => QK04_jchoice b (WK b N) (q ^ 2) (by omega) hW1 (hB q hq).2.2.2.2.2.1
  choose! jf hjf1 hjf2 using hjex
  have hjm : ∀ q ∈ B, jf q < m := by
    intro q hq
    have h1 := hjf1 q hq
    have h2 := (hB q hq).2.2.2.2.2.2
    have h3 : WK b N * b ^ (2 * jf q) < WK b N * b ^ (2 * m) := by
      calc WK b N * b ^ (2 * jf q) ≤ 6 * WK b N * b ^ (2 * jf q) := by
            rw [mul_assoc 6]; exact Nat.le_mul_of_pos_left _ (by norm_num)
        _ ≤ q ^ 2 := h1
        _ < b ^ (2 * N + 1) := h2
        _ = WK b N * b ^ (2 * m) := by rw [hW, ← pow_add]; congr 1; omega
    have h4 := Nat.lt_of_mul_lt_mul_left h3
    have h5 := (Nat.pow_lt_pow_iff_right (by omega : 1 < b)).1 h4
    omega
  -- the cut, modulus by modulus
  set t : ℝ := Real.exp (-(a * L)) with ht
  have htpos : 0 < t := Real.exp_pos _
  set Sm : ℕ → ℝ := fun q' => ∑ h ∈ range q',
      (∏ k ∈ Ico 1 m, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q' + β))) *
        trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q' + β)) with hSm
  have hSm0 : ∀ q', 0 ≤ Sm q' := by
    intro q'; apply Finset.sum_nonneg; intro h _
    exact (Real.rpow_nonneg (norm_nonneg _) p).trans (LK10_fKp_le b g hg p (by linarith) H τ hT S κ N hκM hm1 _)
  have hm0 := LK10_mw4_nonneg b g
  have hM4 := LK10_mM4_le (WK b N) hW1
  have hper : ∀ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖ ≤
      t ^ (1 - p) * (((Q : ℝ) ^ 2)⁻¹ * Sm (q ^ 2)) +
        t⁻¹ ^ 3 * (((b : ℝ)⁻¹) ^ jf q * (1 / (WK b N : ℝ))) := by
    intro q hq
    obtain ⟨hqp, hqB, hq1, _, _, _, _⟩ := hB q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hcut := QK04_cut_mod b g hg p (by linarith) hp2.le H τ hT S κ N hκM hm1 (jf q) (hjm q hq).le
      (q ^ 2) ((range (q ^ 2)).filter (fun h => ¬ q ∣ h)) (Finset.filter_subset _ _) β t htpos
    have hqb : ¬ q ∣ b := fun hd => hqB (dvd_trans hd (by
      unfold bigB; exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl))
    have hpar := hPar b g N (jf q) q β hb (hjm q hq) hqp hqb (hjf1 q hq)
    rw [hpar] at hcut
    have hQq : ((Q : ℝ) ^ 2)⁻¹ ≥ ((q : ℝ) ^ 2)⁻¹ := by
      have : (Q : ℝ) ≤ q := by exact_mod_cast hq1
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hQpos.le this 2)
    have hq2 : 0 < ((q : ℝ) ^ 2)⁻¹ := by positivity
    calc ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
          ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖
        ≤ ((q : ℝ) ^ 2)⁻¹ * (t ^ (1 - p) * Sm (q ^ 2) +
            t⁻¹ ^ 3 * ((q : ℝ) ^ 2 * mw4 b g ^ jf q * mM4 (WK b N))) := mul_le_mul_of_nonneg_left hcut hq2.le
      _ = t ^ (1 - p) * (((q : ℝ) ^ 2)⁻¹ * Sm (q ^ 2)) + t⁻¹ ^ 3 * (mw4 b g ^ jf q * mM4 (WK b N)) := by
          field_simp
      _ ≤ _ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQq (hSm0 _))
              (Real.rpow_nonneg htpos.le _)
          · apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (pow_le_pow_left₀ hm0 (by rw [← one_div]; exact hm4) _) hM4
              (LK10_mM4_nonneg _) (by positivity)
  -- small values: Lemma 2.8_κ on the squares of the block
  set Qs := B.image (fun q => q ^ 2) with hQs
  have hinj : ∀ x ∈ B, ∀ y ∈ B, x ^ 2 = y ^ 2 → x = y := fun x _ y _ hxy =>
    Nat.pow_left_injective (by norm_num : 2 ≠ 0) hxy
  have hSmQ : ∑ q ∈ B, Sm (q ^ 2) = ∑ q' ∈ Qs, Sm q' := by
    rw [hQs, Finset.sum_image hinj]
  have hQspos : ∀ q' ∈ Qs, 1 ≤ q' := by
    intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
    exact Nat.one_le_pow _ _ (hB q hq).1.pos
  set Td : ℝ := Ce * (2 * (b : ℝ) ^ 2 * xx b N) ^ (η / 4) with hTddef
  have hxpos : 0 < xx b N := by rw [hxx]; exact Real.exp_pos _
  have hTd0 : 0 ≤ Td := mul_nonneg hCe0 (Real.rpow_nonneg (by positivity) _)
  have hTd := QK04_Td b H N hb1 hH Qs hQspos (η / 4) Ce (by positivity) hCe0 hCe
  have hL28 := h28 b H N S τ κ (Ico 1 m) Qs β Td hb hH hm1 (subset_refl _) (by omega) hQspos hTd0 hTd
  rw [Nat.card_Ico] at hL28
  have hsumq : (∑ q' ∈ Qs, (q' : ℝ)) ≤ 4 * (Q : ℝ) ^ 3 := by
    rw [hQs, Finset.sum_image (f := fun q' : ℕ => (q' : ℝ)) hinj]
    calc ∑ q ∈ B, ((q ^ 2 : ℕ) : ℝ) ≤ ∑ _q ∈ B, 4 * (Q : ℝ) ^ 2 := by
          apply Finset.sum_le_sum; intro q hq
          obtain ⟨_, _, _, hq2, _⟩ := hB q hq
          have : (q : ℝ) ≤ 2 * Q := by exact_mod_cast hq2.le
          push_cast; nlinarith [(by positivity : (0 : ℝ) ≤ q)]
      _ = #B * (4 * (Q : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q * (4 * (Q : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcardB (by positivity)
      _ = 4 * (Q : ℝ) ^ 3 := by ring
  have hsup : ((Qs.sup id : ℕ) : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by
    have : Qs.sup id ≤ 4 * Q ^ 2 := Finset.sup_le (fun q' hq' => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
      obtain ⟨_, _, _, hq2, _⟩ := hB q hq
      simp only [id]
      calc q ^ 2 ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left hq2.le 2
        _ = 4 * Q ^ 2 := by ring)
    exact_mod_cast this
  have hτN : τ 0 ^ (m - 1) ≤ Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) := by
    rw [Real.exp_natCast_mul, ← Real.rpow_def_of_pos hb0]
    exact pow_le_pow_left₀ hτ0.le hτψ _
  have hA0 : 0 ≤ trigMass H τ := by unfold trigMass; positivity
  have hAN : trigMass H τ ^ (m - 1) ≤ 1 := pow_le_one₀ hA0 hA
  have hκA0 : 0 ≤ trigMass S κ := by unfold trigMass; positivity
  have hκ0' : 0 ≤ κ 0 := hκ0 0
  set ε₂ := min (η / 2) 1 with hε₂
  have hε₂pos : 0 < ε₂ := lt_min (by positivity) one_pos
  have hε₂1 : ε₂ ≤ 1 := min_le_right _ _
  have hε₂2 : ε₂ ≤ η / 2 := min_le_left _ _
  have hWp : (WK b N : ℝ) ^ (-p) = Real.exp (ℓ * lb * (-p)) := by
    rw [Real.rpow_def_of_pos hW0, hlogW]
  have h1W : 1 + Real.log (WK b N) ≤ Real.exp (ε₂ * L) / ε₂ := by
    have h1 : 1 + Real.log (WK b N) ≤ 1 + L := by
      rw [hlogW, hL]
      have : (ℓ : ℝ) ≤ n := by have := (by positivity : (0 : ℝ) ≤ m); linarith
      have := mul_le_mul_of_nonneg_right this hlbpos.le
      linarith
    exact h1.trans (LK10_one_add_le ε₂ L hε₂pos hε₂1 hL0)
  have hκ0b : κ 0 ≤ 100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p)) := by
    rw [← hWp]
    calc κ 0 ≤ 100 * (1 + Real.log (WK b N)) * (WK b N : ℝ) ^ (-p) := hκ00
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW0.le _)
          exact mul_le_mul_of_nonneg_left h1W (by norm_num)
  have hSmall : ((Q : ℝ) ^ 2)⁻¹ * ∑ q' ∈ Qs, Sm q' ≤
      4 * Real.exp δ * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) + 400 * Td := by
    have h1 : ∑ q' ∈ Qs, Sm q' ≤ 4 * (Q : ℝ) ^ 3 * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) + 4 * (Q : ℝ) ^ 2 * Td * 1 * 100 := by
      refine hL28.trans (add_le_add ?_ ?_)
      · exact mul_le_mul (mul_le_mul hsumq hτN (pow_nonneg hτ0.le _) (by positivity)) hκ0b hκ0'
          (by positivity)
      · exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hsup hTd0) hAN (pow_nonneg hA0 _)
          (by positivity)) hκA hκA0 (by positivity)
    have hQ2 : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by positivity
    calc ((Q : ℝ) ^ 2)⁻¹ * ∑ q' ∈ Qs, Sm q' ≤ ((Q : ℝ) ^ 2)⁻¹ * (4 * (Q : ℝ) ^ 3 *
          Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) + 4 * (Q : ℝ) ^ 2 * Td * 1 * 100) :=
          mul_le_mul_of_nonneg_left h1 hQ2.le
      _ = _ := by rw [← hQe]; field_simp; ring
  -- large values
  have hLarge : ∀ q ∈ B, t⁻¹ ^ 3 * (((b : ℝ)⁻¹) ^ jf q * (1 / (WK b N : ℝ))) ≤
      3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) / Q := by
    intro q hq
    obtain ⟨_, _, hq1, _⟩ := hB q hq
    have h2 := hjf2 q hq
    set u : ℝ := (b : ℝ) ^ jf q with hu
    have hupos : 0 < u := by positivity
    have h2R : (q : ℝ) ^ 2 < 6 * (WK b N : ℝ) * (u ^ 2 * (b : ℝ) ^ 2) := by
      have : ((q ^ 2 : ℕ) : ℝ) < ((6 * WK b N * b ^ (2 * jf q + 2) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      rw [hu, ← pow_mul, ← pow_add, mul_comm (jf q) 2]; exact this
    have hQq : (Q : ℝ) ≤ q := by exact_mod_cast hq1
    set sW : ℝ := Real.exp (ℓ * lb / 2) with hsW
    have hsW0 : 0 < sW := Real.exp_pos _
    have hsW2 : sW ^ 2 = (WK b N : ℝ) := by
      rw [hsW, ← Real.exp_natCast_mul, ← hlogW]
      rw [show ((2 : ℕ) : ℝ) * (Real.log (WK b N) / 2) = Real.log (WK b N) by push_cast; ring]
      exact Real.exp_log hW0
    have hti : t⁻¹ ^ 3 = Real.exp (3 * (a * L)) := by
      rw [ht, Real.exp_neg, inv_inv, ← Real.exp_natCast_mul]; norm_num
    have key : (Q : ℝ) * sW ≤ 3 * b * u * (WK b N : ℝ) := by
      have hsq : ((Q : ℝ) * sW) ^ 2 ≤ (3 * b * u * (WK b N : ℝ)) ^ 2 := by
        have e1 : ((Q : ℝ) * sW) ^ 2 = (Q : ℝ) ^ 2 * (WK b N : ℝ) := by rw [mul_pow, hsW2]
        have e2 : (3 * b * u * (WK b N : ℝ)) ^ 2 = 9 * (b : ℝ) ^ 2 * u ^ 2 * (WK b N : ℝ) * (WK b N : ℝ) := by
          ring
        rw [e1, e2]
        have hQ2 : (Q : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ hQpos.le hQq 2
        have : (q : ℝ) ^ 2 ≤ 9 * (b : ℝ) ^ 2 * u ^ 2 * (WK b N : ℝ) := by nlinarith
        exact mul_le_mul_of_nonneg_right (hQ2.trans this) hW0.le
      have h0 : 0 ≤ (Q : ℝ) * sW := by positivity
      have h0' : 0 ≤ 3 * b * u * (WK b N : ℝ) := by positivity
      nlinarith
    rw [hti, inv_pow, ← hu]
    have e : Real.exp (3 * (a * L) - ℓ * lb / 2) = Real.exp (3 * (a * L)) / sW := by
      rw [hsW, Real.exp_sub]
    rw [e, le_div_iff₀ hQpos]
    have h5 : (u⁻¹ * (1 / (WK b N : ℝ))) * (Q : ℝ) ≤ 3 * b / sW := by
      rw [le_div_iff₀ hsW0]
      rw [show (u⁻¹ * (1 / (WK b N : ℝ))) * (Q : ℝ) * sW = ((Q : ℝ) * sW) / (u * (WK b N : ℝ)) by
        field_simp]
      rw [div_le_iff₀ (by positivity)]; linarith
    calc Real.exp (3 * (a * L)) * (u⁻¹ * (1 / (WK b N : ℝ))) * (Q : ℝ)
        = Real.exp (3 * (a * L)) * ((u⁻¹ * (1 / (WK b N : ℝ))) * (Q : ℝ)) := by ring
      _ ≤ Real.exp (3 * (a * L)) * (3 * b / sW) := mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      _ = 3 * b * (Real.exp (3 * (a * L)) / sW) := by ring
  -- assembly
  have hsum : ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖ ≤
      t ^ (1 - p) * (((Q : ℝ) ^ 2)⁻¹ * ∑ q' ∈ Qs, Sm q') + 3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) := by
    calc _ ≤ ∑ q ∈ B, (t ^ (1 - p) * (((Q : ℝ) ^ 2)⁻¹ * Sm (q ^ 2)) +
          t⁻¹ ^ 3 * (((b : ℝ)⁻¹) ^ jf q * (1 / (WK b N : ℝ)))) := Finset.sum_le_sum hper
      _ ≤ ∑ q ∈ B, (t ^ (1 - p) * (((Q : ℝ) ^ 2)⁻¹ * Sm (q ^ 2)) +
          3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) / Q) :=
          Finset.sum_le_sum (fun q hq => add_le_add le_rfl (hLarge q hq))
      _ = t ^ (1 - p) * (((Q : ℝ) ^ 2)⁻¹ * ∑ q ∈ B, Sm (q ^ 2)) +
          #B * (3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) / Q) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          rw [hSmQ]
          apply add_le_add le_rfl
          calc (#B : ℝ) * (3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) / Q)
              ≤ Q * (3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) / Q) :=
                mul_le_mul_of_nonneg_right hcardB (by positivity)
            _ = _ := by field_simp
  -- numerics
  have htp : t ^ (1 - p) = Real.exp (-(a * L) * (1 - p)) := by rw [ht, ← Real.exp_mul]
  have hpm : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1]; norm_num
  set Ef := Real.exp (-(η₁ * L)) with hEf
  have hA' : Real.exp (-(a * L) * (1 - p)) * (4 * Real.exp δ * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p)))) ≤
      400 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * Ef := by
    have ex := LK10_expA n m ℓ lb δ a p ψ η c₁ ε₂ η hlbpos hn0 hℓR hmR1 hmR2 (by rw [← hL]; linarith)
      hD1 hψ (by linarith) hε₂2
    rw [hpm]
    have e1 : Real.exp (-(a * L) * (1 - p)) * (4 * Real.exp δ * Real.exp ((m - 1) * (lb * -ψ)) *
        (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * -p))) =
        400 / ε₂ * Real.exp (-(a * (n * lb)) * (1 - p) + δ + (m - 1) * (lb * (-ψ)) + ε₂ * (n * lb) +
          ℓ * lb * (-p)) := by
      rw [hL]; simp only [Real.exp_add]; field_simp; ring
    have e2 : 400 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * Ef =
        400 / ε₂ * Real.exp (lb * (2 * ψ + 2) + (-(η₁ * (n * lb)))) := by
      rw [hEf, hL]; simp only [Real.exp_add]; ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hη₁ (by positivity : (0 : ℝ) ≤ n * lb)
    nlinarith
  have hB' : Real.exp (-(a * L) * (1 - p)) * (400 * Td) ≤ 400 * Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) * Ef := by
    have hTde : Td = Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) * Real.exp (L * (η / 4)) := by
      rw [hTddef, Real.mul_rpow (by positivity) hxpos.le, hxr]; ring
    rw [hTde]
    have e1 : Real.exp (-(a * L) * (1 - p)) * (400 * (Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) * Real.exp (L * (η / 4))))
        = 400 * Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) * Real.exp (-(a * L) * (1 - p) + L * (η / 4)) := by
      rw [Real.exp_add]; ring
    rw [e1, hEf]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_left hE1.le hL0
    have h2 := mul_le_mul_of_nonneg_left hη₁ hL0
    nlinarith
  have hC' : 3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) ≤ 3 * b * Ef := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have h1 := mul_le_mul_of_nonneg_left (by linarith : 3 * a + η ≤ 3 / 20) hL0
    have h2 := mul_le_mul_of_nonneg_left hη₁ hL0
    nlinarith
  have htp0 : 0 ≤ t ^ (1 - p) := Real.rpow_nonneg htpos.le _
  calc _ ≤ _ := hsum
    _ ≤ t ^ (1 - p) * (4 * Real.exp δ * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) + 400 * Td) +
        3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) := add_le_add (mul_le_mul_of_nonneg_left hSmall htp0) le_rfl
    _ = Real.exp (-(a * L) * (1 - p)) * (4 * Real.exp δ * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p)))) +
        Real.exp (-(a * L) * (1 - p)) * (400 * Td) + 3 * b * Real.exp (3 * (a * L) - ℓ * lb / 2) := by
        rw [htp]; ring
    _ ≤ 400 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * Ef + 400 * Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) * Ef +
        3 * b * Ef := add_le_add (add_le_add hA' hB') hC'
    _ = _ := by rw [hEf, hL, hn]; ring

end KappaOmega2
