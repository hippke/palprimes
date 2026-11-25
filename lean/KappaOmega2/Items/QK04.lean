import KappaOmega2.Items.QK04_Blk

/-!
# QK04: Proposition CQ_κ (assembly)

Reduction `SqRedKStmt`, main term `Σ X/p² ≤ 2X x^{−c₀}`, the error by dyadic blocks of primes (`QK04_Blk`, `QK04_Cut`):
each block is `≤ C x^{−η₁}`, `η₁ = min(η/2, 3/40)`, there are `≤ b(2N+1)` blocks, so the error is `≤ x^{−η₁/2}`.
-/

namespace KappaOmega2

open Finset Real Palprimes

set_option maxHeartbeats 8000000 in
theorem itemQK04 : ItemQK04 := by
  intro b g p H τ ψ a η θ θ₀ c₀ c₁ hb hg hp1 hp2 hH hT hτ0 hτψ hA hm4 ha hη hB1 hD1 hE1 hc₀ hc₀₁ hc₁
    hθ₀ hθ₀3 hθ3 hc₁θ hθ1 hTL hRed hPar h28 hKm
  classical
  have hb1 : 1 ≤ b := by omega
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1R : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set lb := Real.log b with hlb
  have hlbpos : 0 < lb := Real.log_pos hb1R
  -- ψ⁺
  set ψ' := max ψ 0 with hψ'
  have hψ'0 : 0 ≤ ψ' := le_max_right _ _
  have hτψ' : τ 0 ≤ (b : ℝ) ^ (-ψ') := by
    rcases le_total ψ 0 with h | h
    · rw [hψ', max_eq_right h, neg_zero, Real.rpow_zero]
      have : τ 0 ≤ trigMass H τ := by
        unfold trigMass
        have : 0 ≤ 2 * ∑ u ∈ Icc 1 H, |τ u| := by positivity
        linarith [le_abs_self (τ 0)]
      linarith
    · rw [hψ', max_eq_left h]; exact hτψ
  have hD1' : c₁ + η < 7 / 20 * ψ' + 3 / 10 * p + a * (1 - p) := by
    have : ψ ≤ ψ' := le_max_left _ _
    linarith
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow (η / 4) (by positivity)
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl; simp at this; linarith
  obtain ⟨N₁, hN₁⟩ := hTL (η / 2) (by positivity)
  set η₁ : ℝ := min (η / 2) (3 / 40) with hη₁
  have hη₁pos : 0 < η₁ := lt_min (by positivity) (by norm_num)
  have hη₁a : η₁ ≤ η / 2 := min_le_left _ _
  have hη₁b : η₁ ≤ 3 / 40 := min_le_right _ _
  set r := bigB b with hr
  have hr1 : 1 ≤ r := QK04_bigB_pos b hb2
  set Ccut : ℝ := 400 * Real.exp (Real.log b * (2 * ψ' + 2)) / min (η / 2) 1 +
    400 * Ce * (2 * (b : ℝ) ^ 2) ^ (η / 4) + 3 * b with hCcut
  have hCcut0 : 0 ≤ Ccut := by
    have : 0 < min (η / 2) 1 := lt_min (by positivity) one_pos
    positivity
  set Cb : ℝ := (1 + (r : ℝ)) + 2 * r + 3 + Ccut with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set Bb : ℝ := (b : ℝ) ^ 2 + (r : ℝ) with hBb
  have hexpc : 1 < Real.exp (c₀ * lb) := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by positivity)
  obtain ⟨Nc, hNc⟩ := pow_unbounded_of_one_lt (2 * Bb) hexpc
  have hexpθ : 1 < Real.exp ((θ - 3 / 10) * lb) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (mul_pos (by linarith) hlbpos)
  obtain ⟨Nθ, hNθ⟩ := pow_unbounded_of_one_lt (12 * (b : ℝ) ^ 2) hexpθ
  set Cf : ℝ := ((r.divisors.card : ℕ) : ℝ) * r * (2 * b) * Cb with hCf
  set ρ : ℝ := Real.exp (-(η₁ * lb)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, ← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : 0 < η₁ * lb := by positivity
    linarith
  obtain ⟨Nd, hNd⟩ := eventually_poly_geom Cf 1 ρ hρ0 hρ1 1 one_pos
  refine ⟨η₁ / 2, by positivity, max (max (max N₁ Nc) (max Nθ Nd)) 5, ?_⟩
  intro N hN
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hNc' : Nc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hNθ' : Nθ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hNd' : Nd ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hN5 : 5 ≤ N := le_trans (le_max_right _ _) hN
  have hTLN := hN₁ N hN₁'
  -- x and its powers
  set L : ℝ := (2 * (N : ℝ) + 1) * lb with hL
  have hL0 : 0 ≤ L := by positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  have hxx : xx b N = Real.exp L := LK10_xx_exp b N hb1
  have hx0 : 0 ≤ xx b N := by rw [hxx]; positivity
  have hx1 : 1 ≤ xx b N := by rw [hxx]; exact Real.one_le_exp hL0
  have hx1' : 1 < xx b N := by
    rw [hxx, ← Real.exp_zero]; apply Real.exp_lt_exp.2; rw [hL]; positivity
  have hP0big : 2 * Bb < xx b N ^ c₀ := by
    rw [hxr]
    calc 2 * Bb < Real.exp (c₀ * lb) ^ Nc := hNc
      _ ≤ Real.exp (c₀ * lb) ^ (2 * N + 1) := pow_le_pow_right₀ hexpc.le (by omega)
      _ = Real.exp (L * c₀) := by
          rw [← Real.exp_natCast_mul, hL]; push_cast; ring_nf
  have h12 : 12 * (b : ℝ) ^ 2 ≤ Real.exp ((θ - 3 / 10) * L) := by
    calc 12 * (b : ℝ) ^ 2 ≤ Real.exp ((θ - 3 / 10) * lb) ^ Nθ := hNθ.le
      _ ≤ Real.exp ((θ - 3 / 10) * lb) ^ (2 * N + 1) := pow_le_pow_right₀ hexpθ.le (by omega)
      _ = Real.exp ((θ - 3 / 10) * L) := by
          rw [← Real.exp_natCast_mul, hL]; push_cast; ring_nf
  have h12W : 12 * (WK b N : ℝ) ≤ xx b N ^ θ := by
    obtain ⟨_, hWle⟩ := QK04_W_bounds b N hb1
    rw [← hlb, ← hL] at hWle
    rw [hxr]
    calc 12 * (WK b N : ℝ) ≤ 12 * ((b : ℝ) ^ 2 * Real.exp (3 / 10 * L)) :=
          mul_le_mul_of_nonneg_left hWle (by norm_num)
      _ = 12 * (b : ℝ) ^ 2 * Real.exp (3 / 10 * L) := by ring
      _ ≤ Real.exp ((θ - 3 / 10) * L) * Real.exp (3 / 10 * L) :=
          mul_le_mul_of_nonneg_right h12 (Real.exp_pos _).le
      _ = Real.exp (L * θ) := by rw [← Real.exp_add]; ring_nf
  have hBbge : (b : ℝ) ^ 2 + (r : ℝ) ≤ Bb := le_refl _
  -- the sets
  set P0 := xx b N ^ c₀ with hP0
  set P1 := xx b N ^ c₁ with hP1
  have hP0e : P0 = Real.exp (L * c₀) := hxr c₀
  have hP0two : 2 ≤ P0 := by
    have : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_pow₀ hb1R.le
    linarith
  have hP1x : P1 ≤ xx b N := by
    calc xx b N ^ c₁ ≤ xx b N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = xx b N := Real.rpow_one _
  have hP11 : 1 ≤ P1 := Real.one_le_rpow hx1 (by linarith)
  set a₀ := ⌊P0⌋₊ with ha₀
  set Y1 := ⌊P1⌋₊ with hY1
  have ha₀le : (a₀ : ℝ) ≤ P0 := Nat.floor_le (by linarith)
  have ha₀gt : P0 < a₀ + 1 := Nat.lt_floor_add_one P0
  have ha₀1 : 1 ≤ a₀ := Nat.one_le_floor_iff _ |>.2 (by linarith)
  have hY1le : (Y1 : ℝ) ≤ P1 := Nat.floor_le (by linarith)
  set S := (Icc 1 ⌊xx b N ^ c₁⌋₊).filter (fun p : ℕ => p.Prime ∧ xx b N ^ c₀ < (p : ℝ)) with hS
  have hSmem : ∀ q ∈ S, q.Prime ∧ P0 < q ∧ q ≤ Y1 := by
    intro q hq
    simp only [hS, mem_filter, mem_Icc] at hq
    exact ⟨hq.2.1, hq.2.2, hq.1.2⟩
  have hndvd : ∀ q ∈ S, ¬ q ∣ bigB b := by
    intro q hq hdvd
    have h1 := Nat.le_of_dvd (by omega) hdvd
    have h2 : (q : ℝ) ≤ r := by exact_mod_cast h1
    have h3 := (hSmem q hq).2.1
    have : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_pow₀ hb1R.le
    linarith
  -- reduction
  set Fk : ℕ → ℕ → ℝ := fun k q => ((q : ℝ) ^ 2)⁻¹ *
        ((∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
            ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 q, ‖fK b g N ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))‖) with hFk
  have hFk0 : ∀ k q, 0 ≤ Fk k q := fun k q => mul_nonneg (by positivity)
    (add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hAKp : ∀ q ∈ S, AK b g N (q ^ 2) ≤ XK b g N * (1 / (q : ℝ) ^ 2) +
      ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), Fk k q := by
    intro q hq
    have h := hRed b g N q hb (hSmem q hq).1 (hndvd q hq)
    have := (abs_sub_le_iff.1 h).1
    rw [mul_one_div]
    linarith
  -- one block
  set Ef := Real.exp (-(η₁ * L)) with hEf
  have hblock : ∀ i k : ℕ, ∑ q ∈ S.filter (fun q => Nat.log 2 q = i), Fk k q ≤ Cb * Ef := by
    intro i k
    set B := S.filter (fun q => Nat.log 2 q = i) with hB
    have hBh : QK04_blockHyp b N i c₁ B := by
      intro q hq
      obtain ⟨hq, hqi⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqp, _, hqY⟩ := hSmem q hq
      refine ⟨hqp, hndvd q hq, ?_, ?_, ?_⟩
      · rw [← hqi]; exact Nat.pow_log_le_self 2 hqp.ne_zero
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
        rw [hqi, pow_succ] at this; omega
      · exact le_trans (by exact_mod_cast hqY) hY1le
    have hsplit : ∑ q ∈ B, Fk k q =
        ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
            ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖ +
        ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ Ico 1 q, ‖fK b g N ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q _
      rw [hFk]; simp only; ring
    have hEE1 := QK04_E1 b g hb hg N θ θ₀ c₁ η η₁ hη hη₁a hη₁b hθ₀3 hc₁θ hTLN k i B hBh
    rw [← hlb, ← hL, ← hEf] at hEE1
    have hE2 : ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖ ≤ (2 * r + 3 + Ccut) * Ef := by
      have hEf0 : 0 ≤ Ef := (Real.exp_pos _).le
      by_cases h1 : ((2 ^ i : ℕ) : ℝ) ^ 2 ≤ xx b N ^ θ₀
      · have := QK04_E2mid b g hb hg N θ₀ c₁ η₁ hη₁b hθ₀3 k i B hBh h1
        rw [← hlb, ← hL, ← hEf] at this
        have : 0 ≤ (3 + Ccut) * Ef := by positivity
        nlinarith
      push Not at h1
      by_cases h2 : 2 * ((2 ^ i : ℕ) : ℝ) ^ 2 ≤ xx b N ^ θ
      · have := QK04_E2tl b g hb N θ θ₀ c₁ η η₁ hη hη₁a hTLN k i B hBh h1 h2
        rw [← hlb, ← hL, ← hEf] at this
        have : 0 ≤ (2 * r + Ccut) * Ef := by positivity
        nlinarith
      push Not at h2
      have hBc : ∀ q ∈ B, q.Prime ∧ ¬ q ∣ bigB b ∧ 2 ^ i ≤ q ∧ q < 2 * 2 ^ i ∧ (q : ℝ) ≤ xx b N ^ c₁ ∧
          6 * WK b N ≤ q ^ 2 ∧ q ^ 2 < b ^ (2 * N + 1) := by
        intro q hq
        obtain ⟨hqp, hqB, hq1, hq2, hqx⟩ := hBh q hq
        refine ⟨hqp, hqB, hq1, hq2, hqx, ?_, ?_⟩
        · have hQq : ((2 ^ i : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq1) 2
          have : ((6 * WK b N : ℕ) : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        · have hq0 : (0 : ℝ) ≤ q := by positivity
          have h3 : (q : ℝ) ^ 2 ≤ xx b N ^ (2 * c₁) := by
            calc (q : ℝ) ^ 2 ≤ (xx b N ^ c₁) ^ 2 := pow_le_pow_left₀ hq0 hqx 2
              _ = xx b N ^ (2 * c₁) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; ring_nf
          have h4 : xx b N ^ (2 * c₁) < xx b N := by
            calc xx b N ^ (2 * c₁) < xx b N ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hx1' (by linarith)
              _ = xx b N := Real.rpow_one _
          have h5 : (q : ℝ) ^ 2 < xx b N := lt_of_le_of_lt h3 h4
          have : ((q ^ 2 : ℕ) : ℝ) < ((b ^ (2 * N + 1) : ℕ) : ℝ) := by
            push_cast; unfold xx at h5; exact h5
          exact_mod_cast this
      have := QK04_cut b g p H τ ψ' a η η₁ c₁ Ce hb hg hp1 hp2 hH hT hτ0 hτψ' hψ'0 hA hm4 ha hη hB1 hD1' hE1
        hη₁a hCe0 hCe h28 hPar hKm N hN5 ((k : ℝ) / (bigB b : ℝ)) i B hBc
      rw [← hlb, ← hL, ← hEf, ← hCcut] at this
      have : 0 ≤ (2 * r + 3) * Ef := by positivity
      nlinarith
    rw [hsplit]
    calc _ ≤ (2 * r + 3 + Ccut) * Ef + (1 + (r : ℝ)) * Ef := add_le_add hE2 hEE1
      _ = Cb * Ef := by rw [hCb]; ring
  -- sum over the blocks for one shift
  set I := Nat.log 2 Y1 + 1 with hI
  have hIb : I ≤ b * (2 * N + 1) := QK04_log_le b N Y1 hb2 (hY1le.trans hP1x)
  have hshift : ∀ k : ℕ, ∑ q ∈ S, Fk k q ≤ (b * (2 * N + 1) : ℕ) * (Cb * Ef) := by
    intro k
    have hmaps : ∀ q ∈ S, Nat.log 2 q ∈ range I := by
      intro q hq
      exact mem_range.2 (Nat.lt_succ_of_le (Nat.log_mono_right (hSmem q hq).2.2))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _i ∈ range I, Cb * Ef := Finset.sum_le_sum (fun i _ => hblock i k)
      _ = (I : ℝ) * (Cb * Ef) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hIb) (by positivity)
  -- the main term
  have hXK0 := QK04_XK_nonneg b g hg.1 N
  have hmainS : ∑ q ∈ S, XK b g N * (1 / (q : ℝ) ^ 2) ≤ 2 * XK b g N * xx b N ^ (-c₀) := by
    rw [← Finset.mul_sum]
    have h1 : ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2 ≤ ∑ n ∈ Ioc a₀ Y1, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro q hq
      obtain ⟨_, hqP0, hqY⟩ := hSmem q hq
      have : (a₀ : ℝ) < q := lt_of_le_of_lt ha₀le hqP0
      have : a₀ < q := by exact_mod_cast this
      exact mem_Ioc.2 ⟨this, hqY⟩
    have h2 := QK04_inv_sq a₀ ha₀1 Y1
    have h3 : (1 : ℝ) / a₀ ≤ 2 * xx b N ^ (-c₀) := by
      rw [Real.rpow_neg hx0, ← hP0]
      have ha₀pos : (0 : ℝ) < a₀ := by exact_mod_cast ha₀1
      rw [div_le_iff₀ ha₀pos]
      have hP0pos : 0 < P0 := by linarith
      rw [show 2 * P0⁻¹ * (a₀ : ℝ) = 2 * a₀ / P0 by field_simp, le_div_iff₀ hP0pos]
      linarith
    calc XK b g N * ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2 ≤ XK b g N * (2 * xx b N ^ (-c₀)) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3)) hXK0
      _ = _ := by ring
  -- the error term
  have herr : ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ q ∈ S, Fk k q ≤
      xx b N ^ (-(η₁ / 2)) := by
    have hCbE0 : 0 ≤ Cb * Ef := by positivity
    have h1 : ∑ k ∈ range (bigB b), ∑ q ∈ S, Fk k q ≤ (r : ℝ) * ((b * (2 * N + 1) : ℕ) * (Cb * Ef)) := by
      calc _ ≤ ∑ _k ∈ range (bigB b), ((b * (2 * N + 1) : ℕ) * (Cb * Ef)) :=
            Finset.sum_le_sum (fun k _ => hshift k)
        _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
    have hEfN : Ef ≤ ρ ^ N * xx b N ^ (-(η₁ / 2)) := by
      rw [hρ, hEf, hxr, ← Real.exp_natCast_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [hL]
      have : 0 ≤ η₁ * lb := by positivity
      nlinarith
    have hfin := hNd N hNd'
    have hdiv0 : (0 : ℝ) ≤ ((bigB b).divisors.card : ℝ) := by positivity
    have hb2N : ((b * (2 * N + 1) : ℕ) : ℝ) ≤ (2 * b) * ((N : ℝ) + 1) := by
      push_cast; nlinarith [(by positivity : (0 : ℝ) ≤ b)]
    calc ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ q ∈ S, Fk k q
        ≤ ((bigB b).divisors.card : ℝ) * ((r : ℝ) * ((b * (2 * N + 1) : ℕ) * (Cb * Ef))) :=
          mul_le_mul_of_nonneg_left h1 hdiv0
      _ ≤ ((bigB b).divisors.card : ℝ) * ((r : ℝ) * (((2 * b) * ((N : ℝ) + 1)) *
            (Cb * (ρ ^ N * xx b N ^ (-(η₁ / 2)))))) := by
          apply mul_le_mul_of_nonneg_left _ hdiv0
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hb2N (mul_le_mul_of_nonneg_left hEfN hCb0) hCbE0 (by positivity)
      _ = Cf * ((N : ℝ) + 1) ^ 1 * ρ ^ N * xx b N ^ (-(η₁ / 2)) := by rw [hCf]; ring
      _ ≤ 1 * xx b N ^ (-(η₁ / 2)) :=
          mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hx0 _)
      _ = _ := one_mul _
  -- assembly
  unfold SqK
  rw [← hS]
  calc ∑ q ∈ S, AK b g N (q ^ 2) ≤ ∑ q ∈ S, (XK b g N * (1 / (q : ℝ) ^ 2) +
        ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), Fk k q) := Finset.sum_le_sum hAKp
    _ = ∑ q ∈ S, XK b g N * (1 / (q : ℝ) ^ 2) +
        ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ∑ q ∈ S, Fk k q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (s := S) (t := range (bigB b))]
    _ ≤ _ := add_le_add hmainS herr

end KappaOmega2
