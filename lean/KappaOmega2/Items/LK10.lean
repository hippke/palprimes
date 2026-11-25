import KappaOmega2.Items.LK10_Aux

/-!
# LK10: Proposition C_κ (the scalar conditions give `TL¹_κ(θ, η, θ₀)`)

Cut at `|f| = x^{−a}`. Small values: `|f| ≤ x^{−a(1−p)}|f|^p ≤ x^{−a(1−p)} Π_{k∈[1,m)} T(c_k α) K̃(b^m α)`, expanded by
Lemma 2.8_κ with the middle majorant `K̃` of `KmidStmt` (diagonal `2D² τ₀^{m−1} κ₀`, off-diagonal `2D · Td · 100` with the
divisor bound for `Td`). Large values: Chebyshev with the fourth power and Lemma 2.9_κ, `j` from `LK10_large_choice`.
-/

namespace KappaOmega2

open Finset Real Palprimes

set_option maxHeartbeats 4000000 in
lemma LK10_core (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ a η θ θ₀ ε Ce : ℝ)
    (hb : 3 ≤ b) (hg : IsDigitWeight b g) (hp1 : 1 / 2 ≤ p) (hp2 : p < 1) (hH : H ≤ b * (b - 1))
    (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (hτ0 : 0 < τ 0) (hτψ : τ 0 ≤ (b : ℝ) ^ (-ψ))
    (hψ : 0 ≤ ψ) (hA : trigMass H τ ≤ 1) (hm4 : mw4 b g ≤ 1 / (b : ℝ)) (ha : 0 < a) (hη : 0 < η)
    (hA1 : 4 * a + η < θ₀) (hB1 : 4 * a + η < 3 / 20) (hC1 : θ + 4 * a + η < 13 / 20)
    (hD1 : θ + η < 7 / 20 * ψ + 3 / 10 * p + a * (1 - p)) (hE1 : η < a * (1 - p))
    (hε : 0 < ε) (hCe0 : 0 ≤ Ce) (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ (ε / 2))
    (h28 : Lemma28KStmt) (h29 : Lemma29KStmt) (hKm : KmidStmt)
    (N D : ℕ) (hN : 5 ≤ N) (hDlo : xx b N ^ θ₀ < D) (hDhi : (D : ℝ) ≤ xx b N ^ θ) (β : ℝ) :
    blockL1K b g N D β ≤ (200 * Real.exp (Real.log b * (2 * ψ + 2)) / min (ε / 2) 1 +
        200 * Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) + 16 * ((b : ℝ) ^ 4 + 3 * b + 2 * (b : ℝ) ^ 3)) *
      Real.exp (Real.log D - η * ((2 * (N : ℝ) + 1) * Real.log b) +
        ε / 2 * ((2 * (N : ℝ) + 1) * Real.log b)) := by
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
  have hℓ2 : (ℓ : ℝ) ≤ 2 * ((ℓ / 2 : ℕ) : ℝ) + 1 := by
    have h : ℓ ≤ 2 * (ℓ / 2) + 1 := by omega
    exact_mod_cast h
  -- D
  have hx0 : 0 < xx b N ^ θ₀ := by rw [hxr]; exact Real.exp_pos _
  have hDpos : (0 : ℝ) < D := lt_trans hx0 hDlo
  have hD1n : 1 ≤ D := by
    have : 0 < D := by exact_mod_cast hDpos
    omega
  set δ := Real.log D with hδ
  have hDe : (D : ℝ) = Real.exp δ := (Real.exp_log hDpos).symm
  have hδhi : δ ≤ L * θ := by
    have h := hDhi; rw [hxr, hDe] at h; exact Real.exp_le_exp.1 h
  have hδlo : L * θ₀ < δ := by
    have h := hDlo; rw [hxr, hDe] at h; exact Real.exp_lt_exp.1 h
  have hD2e : (D : ℝ) ^ 2 = Real.exp (2 * δ) := by
    rw [hDe, ← Real.exp_natCast_mul]; norm_num
  -- the block and its split
  set Qs := (Ico D (2 * D)).filter (fun d => Nat.Coprime d b) with hQs
  obtain ⟨j, hjm, hjb⟩ := LK10_large_choice b m ℓ D (by omega) hm1 hD1n
  set t : ℝ := Real.exp (-(a * L)) with ht
  have htpos : 0 < t := Real.exp_pos _
  have hsplit := LK10_block_split b g hg p (by linarith) hp2.le H τ hT S κ N hκM hm1 j hjm.le Qs β t htpos
  have hblk : blockL1K b g N D β = ∑ d ∈ Qs, ∑ h ∈ redRes d, ‖fK b g N ((h : ℝ) / d + β)‖ := rfl
  -- small values: Lemma 2.8_κ
  have hQpos : ∀ q ∈ Qs, 1 ≤ q := by
    intro q hq; simp only [hQs, mem_filter, mem_Ico] at hq; omega
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
  set Td : ℝ := Ce * (2 * (b : ℝ) ^ 2 * xx b N) ^ (ε / 2) with hTddef
  have hxpos : 0 < xx b N := by rw [hxx]; exact Real.exp_pos _
  have hTd0 : 0 ≤ Td := mul_nonneg hCe0 (Real.rpow_nonneg (by positivity) _)
  have hHb : 2 * (H : ℝ) + 1 ≤ 2 * (b : ℝ) ^ 2 := by
    have e : b * (b - 1) + b = b * b := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h : 2 * H + 1 ≤ 2 * (b * b) := by omega
    have h' : ((2 * H + 1 : ℕ) : ℝ) ≤ ((2 * (b * b) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; nlinarith
  have hTd : ∀ v : ℤ, v ≠ 0 → |v| ≤ (2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) →
      ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ v)).card : ℝ) ≤ Td := by
    intro v hv hvle
    have h1 := card_filter_dvd_le_divisors Qs (fun q hq => hQpos q hq) v hv
    have h2 := hCe v.natAbs (Int.natAbs_pos.2 hv)
    have h3 : (v.natAbs : ℝ) ≤ 2 * (b : ℝ) ^ 2 * xx b N := by
      have h3' : ((v.natAbs : ℤ) : ℝ) ≤ (((2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) : ℤ) : ℝ) := by
        rw [Int.natCast_natAbs]; exact_mod_cast hvle
      rw [Int.cast_natCast] at h3'
      push_cast at h3'
      unfold xx
      have hpow : (0 : ℝ) ≤ (b : ℝ) ^ (2 * N + 1) := by positivity
      calc (v.natAbs : ℝ) ≤ (2 * (H : ℝ) + 1) * (b : ℝ) ^ (2 * N + 1) := h3'
        _ ≤ 2 * (b : ℝ) ^ 2 * (b : ℝ) ^ (2 * N + 1) := mul_le_mul_of_nonneg_right hHb hpow
    calc ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ v)).card : ℝ) ≤ (#(v.natAbs.divisors) : ℝ) := by
          exact_mod_cast h1
      _ ≤ Ce * (v.natAbs : ℝ) ^ (ε / 2) := h2
      _ ≤ Td := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) h3 (by positivity)) hCe0
  have hL28 := h28 b H N S τ κ (Ico 1 m) Qs β Td hb hH hm1 (subset_refl _) (by omega) hQpos hTd0 hTd
  rw [Nat.card_Ico] at hL28
  -- the factors
  have hτN : τ 0 ^ (m - 1) ≤ Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) := by
    rw [Real.exp_natCast_mul, ← Real.rpow_def_of_pos hb0]
    exact pow_le_pow_left₀ hτ0.le hτψ _
  have hA0 : 0 ≤ trigMass H τ := by unfold trigMass; positivity
  have hAN : trigMass H τ ^ (m - 1) ≤ 1 := pow_le_one₀ hA0 hA
  have hκA0 : 0 ≤ trigMass S κ := by unfold trigMass; positivity
  have hκ0' : 0 ≤ κ 0 := hκ0 0
  set ε₂ := min (ε / 2) 1 with hε₂
  have hε₂pos : 0 < ε₂ := lt_min (by positivity) one_pos
  have hε₂1 : ε₂ ≤ 1 := min_le_right _ _
  have hε₂2 : ε₂ ≤ ε / 2 := min_le_left _ _
  have hlogW : Real.log (WK b N) = ℓ * lb := by rw [hWR, Real.log_pow]
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
  have hSmall : (∑ q ∈ Qs, ∑ h ∈ range q,
        (∏ k ∈ Ico 1 m, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
          trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q + β))) ≤
      2 * (D : ℝ) ^ 2 * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) +
        2 * D * Td * 100 := by
    refine hL28.trans (add_le_add ?_ ?_)
    · exact mul_le_mul (mul_le_mul hsumq hτN (pow_nonneg hτ0.le _) (by positivity)) hκ0b hκ0'
        (by positivity)
    · have e1 : ((Qs.sup id : ℕ) : ℝ) * Td * trigMass H τ ^ (m - 1) ≤ 2 * D * Td * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hsup hTd0) hAN (pow_nonneg hA0 _) (by positivity)
      calc ((Qs.sup id : ℕ) : ℝ) * Td * trigMass H τ ^ (m - 1) * trigMass S κ
          ≤ 2 * D * Td * 1 * 100 := mul_le_mul e1 hκA (hκA0) (by positivity)
        _ = 2 * D * Td * 100 := by ring
  -- large values: Lemma 2.9_κ
  have hL29 := h29 b g N j D β hb hg.1 hjm hD1n
  have hm0 := LK10_mw4_nonneg b g
  have hmj : mw4 b g ^ j ≤ ((b : ℝ)⁻¹) ^ j := pow_le_pow_left₀ hm0 (by rw [← one_div]; exact hm4) j
  have hM4 := LK10_mM4_le (WK b N) hW1
  have hLarge : (∑ d ∈ Qs, ∑ h ∈ redRes d, ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4) ≤
      16 * (((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
        2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2)) := by
    refine hL29.trans ?_
    have e : 16 * ((D : ℝ) ^ 2 + b * (WK b N : ℝ) * (b : ℝ) ^ (2 * j)) * ((b : ℝ)⁻¹) ^ j * (1 / (WK b N : ℝ))
        = 16 * (((D : ℝ) ^ 2 + b * (b : ℝ) ^ ℓ * (b : ℝ) ^ (2 * j)) * ((b : ℝ)⁻¹) ^ j / (b : ℝ) ^ ℓ) := by
      rw [hWR]; ring
    calc 16 * ((D : ℝ) ^ 2 + b * (WK b N : ℝ) * (b : ℝ) ^ (2 * j)) * mw4 b g ^ j * mM4 (WK b N)
        ≤ 16 * ((D : ℝ) ^ 2 + b * (WK b N : ℝ) * (b : ℝ) ^ (2 * j)) * ((b : ℝ)⁻¹) ^ j * (1 / (WK b N : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmj (by positivity)) hM4 (LK10_mM4_nonneg _) (by positivity)
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left hjb (by norm_num)
  -- exponents
  set E := Real.exp (δ - η * L + ε / 2 * L) with hE
  have htp : t ^ (1 - p) = Real.exp (-(a * L) * (1 - p)) := by rw [ht, ← Real.exp_mul]
  have hti : t⁻¹ ^ 3 = Real.exp (3 * (a * L)) := by
    rw [ht, Real.exp_neg, inv_inv, ← Real.exp_natCast_mul]; norm_num
  have hpm : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1]; norm_num
  have hTA : t ^ (1 - p) * (2 * (D : ℝ) ^ 2 * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p)))) ≤
      200 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * E := by
    have ex := LK10_expA n m ℓ lb δ a p ψ η θ ε₂ ε hlbpos hn0 hℓR hmR1 hmR2 (by rw [← hL]; linarith)
      hD1 hψ (by linarith) hε₂2
    rw [htp, hD2e, hpm]
    have e1 : Real.exp (-(a * L) * (1 - p)) * (2 * Real.exp (2 * δ) * Real.exp ((m - 1) * (lb * -ψ)) *
        (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * -p))) =
        200 / ε₂ * Real.exp (-(a * (n * lb)) * (1 - p) + 2 * δ + (m - 1) * (lb * (-ψ)) + ε₂ * (n * lb) +
          ℓ * lb * (-p)) := by
      rw [hL]; simp only [Real.exp_add]; field_simp; ring
    have e2 : 200 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * E =
        200 / ε₂ * Real.exp (lb * (2 * ψ + 2) + (δ - η * (n * lb) + ε / 2 * (n * lb))) := by
      rw [hE, hL]; simp only [Real.exp_add, Real.exp_sub]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ex) (by positivity)
  have hTB : t ^ (1 - p) * (2 * D * Td * 100) ≤ 200 * Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) * E := by
    have hTde : Td = Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) * Real.exp (L * (ε / 2)) := by
      rw [hTddef, Real.mul_rpow (by positivity) hxpos.le, hxr]; ring
    rw [htp, hTde, hDe]
    have e1 : Real.exp (-(a * L) * (1 - p)) * (2 * Real.exp δ * (Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) *
        Real.exp (L * (ε / 2))) * 100) = 200 * Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) *
          Real.exp (-(a * L) * (1 - p) + δ + L * (ε / 2)) := by
      simp only [Real.exp_add]; ring
    rw [e1, hE]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hE1.le hL0
    nlinarith
  have hEb : Real.exp (δ - η * L) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.2
    have : 0 ≤ ε / 2 * L := by positivity
    linarith
  have hTC : t⁻¹ ^ 3 * (16 * (((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
        2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2))) ≤
      16 * ((b : ℝ) ^ 4 + 3 * b + 2 * (b : ℝ) ^ 3) * E := by
    rw [hti]
    have c1 : Real.exp (3 * (a * L)) * ((b : ℝ) ^ 4 + b) ≤ ((b : ℝ) ^ 4 + b) * Real.exp (δ - η * L) := by
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (by linarith : 3 * a + η ≤ θ₀) hL0
      nlinarith
    have c2 : Real.exp (3 * (a * L)) * (2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ)) ≤
        2 * b * Real.exp (δ - η * L) := by
      rw [hD2e, LK10_pow_exp b hb1, LK10_pow_exp b hb1, ← hlb, ← Real.exp_add]
      have e : Real.exp (3 * (a * L)) * (2 * b * Real.exp (2 * δ) / Real.exp (m * lb + ℓ * lb)) =
          2 * b * Real.exp (3 * (a * L) + 2 * δ - (m * lb + ℓ * lb)) := by
        simp only [Real.exp_sub, Real.exp_add]; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.2
      have h1 : (m : ℝ) * lb + ℓ * lb = (n - m) * lb := by rw [← hℓR]; ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_right hmR1 hlbpos.le
      have h3 := mul_le_mul_of_nonneg_left (by linarith : θ + 3 * a + η ≤ 13 / 20) hL0
      rw [hL] at hδhi h3 ⊢
      nlinarith
    have c3 : Real.exp (3 * (a * L)) * (2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2)) ≤
        2 * (b : ℝ) ^ 3 * Real.exp (δ - η * L) := by
      rw [hDe, LK10_pow_exp b hb1 (ℓ / 2), ← hlb]
      have e : Real.exp (3 * (a * L)) * (2 * (b : ℝ) ^ 2 * Real.exp δ / Real.exp (((ℓ / 2 : ℕ) : ℝ) * lb)) =
          2 * (b : ℝ) ^ 2 * Real.exp (3 * (a * L) + δ - ((ℓ / 2 : ℕ) : ℝ) * lb) := by
        simp only [Real.exp_sub, Real.exp_add]; ring
      rw [e]
      have hbe : (b : ℝ) = Real.exp lb := (Real.exp_log hb0).symm
      have e2 : 2 * (b : ℝ) ^ 3 * Real.exp (δ - η * L) = 2 * (b : ℝ) ^ 2 * Real.exp (lb + (δ - η * L)) := by
        rw [Real.exp_add, ← hbe]; ring
      rw [e2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.2
      have h1 := mul_le_mul_of_nonneg_right hℓ2 hlbpos.le
      have h2 := mul_le_mul_of_nonneg_right hmR1 hlbpos.le
      have h3 := mul_le_mul_of_nonneg_left (by linarith : 3 * a + η ≤ 3 / 20) hL0
      rw [hL] at h3 ⊢
      have h4 : (ℓ : ℝ) * lb = (n - 2 * m) * lb := by rw [← hℓR]; ring
      nlinarith
    have hE0 : 0 ≤ Real.exp (δ - η * L) := (Real.exp_pos _).le
    calc Real.exp (3 * (a * L)) * (16 * (((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
          2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2)))
        = 16 * (Real.exp (3 * (a * L)) * ((b : ℝ) ^ 4 + b) +
            Real.exp (3 * (a * L)) * (2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ)) +
            Real.exp (3 * (a * L)) * (2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2))) := by ring
      _ ≤ 16 * (((b : ℝ) ^ 4 + b) * Real.exp (δ - η * L) + 2 * b * Real.exp (δ - η * L) +
            2 * (b : ℝ) ^ 3 * Real.exp (δ - η * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact add_le_add (add_le_add c1 c2) c3
      _ = 16 * ((b : ℝ) ^ 4 + 3 * b + 2 * (b : ℝ) ^ 3) * Real.exp (δ - η * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEb (by positivity)
  -- assembly
  have htp0 : 0 ≤ t ^ (1 - p) := Real.rpow_nonneg htpos.le _
  have hti0 : 0 ≤ t⁻¹ ^ 3 := by positivity
  rw [hblk]
  calc _ ≤ _ := hsplit
    _ ≤ t ^ (1 - p) * (2 * (D : ℝ) ^ 2 * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p))) + 2 * D * Td * 100) +
        t⁻¹ ^ 3 * (16 * (((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
          2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2))) :=
        add_le_add (mul_le_mul_of_nonneg_left hSmall htp0) (mul_le_mul_of_nonneg_left hLarge hti0)
    _ = t ^ (1 - p) * (2 * (D : ℝ) ^ 2 * Real.exp (((m - 1 : ℕ) : ℝ) * (lb * (-ψ))) *
          (100 * (Real.exp (ε₂ * L) / ε₂) * Real.exp (ℓ * lb * (-p)))) + t ^ (1 - p) * (2 * D * Td * 100) +
        t⁻¹ ^ 3 * (16 * (((b : ℝ) ^ 4 + b) + 2 * b * (D : ℝ) ^ 2 / ((b : ℝ) ^ m * (b : ℝ) ^ ℓ) +
          2 * (b : ℝ) ^ 2 * D / (b : ℝ) ^ (ℓ / 2))) := by ring
    _ ≤ 200 * Real.exp (lb * (2 * ψ + 2)) / ε₂ * E + 200 * Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) * E +
        16 * ((b : ℝ) ^ 4 + 3 * b + 2 * (b : ℝ) ^ 3) * E := add_le_add (add_le_add hTA hTB) hTC
    _ = _ := by rw [hE, hL, hn]; ring

set_option maxHeartbeats 1000000 in
theorem itemLK10 : ItemLK10 := by
  intro b g p H τ ψ a η θ θ₀ hb hg hp1 hp2 hH hT hτ0 hτψ hA hm4 ha hη hθ₀ hθ₀θ hθ1 hA1 hB1 hC1 hD1 hE1
    h28 h29 hKm ε hε
  have hb1 : 1 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1R : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
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
  have hD1' : θ + η < 7 / 20 * ψ' + 3 / 10 * p + a * (1 - p) := by
    have : ψ ≤ ψ' := le_max_left _ _
    linarith
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow (ε / 2) (by positivity)
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl; simp at this; linarith
  set Ctot : ℝ := 200 * Real.exp (Real.log b * (2 * ψ' + 2)) / min (ε / 2) 1 +
      200 * Ce * (2 * (b : ℝ) ^ 2) ^ (ε / 2) + 16 * ((b : ℝ) ^ 4 + 3 * b + 2 * (b : ℝ) ^ 3) with hCtot
  have hr : (1 : ℝ) < Real.exp (Real.log b * (ε / 2)) := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (mul_pos (Real.log_pos hb1R) (by positivity))
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt Ctot hr
  refine ⟨max n₁ 5, ?_⟩
  intro N hN D _hdy hDlo hDhi β
  have hN5 : 5 ≤ N := le_trans (le_max_right _ _) hN
  have hcore := LK10_core b g p H τ ψ' a η θ θ₀ ε Ce hb hg hp1 hp2 hH hT hτ0 hτψ' hψ'0 hA hm4 ha hη hA1 hB1
    hC1 hD1' hE1 hε hCe0 hCe h28 h29 hKm N D hN5 hDlo hDhi β
  rw [← hCtot] at hcore
  have hCt : Ctot ≤ Real.exp (ε / 2 * ((2 * (N : ℝ) + 1) * Real.log b)) := by
    have h1 : Real.exp (Real.log b * (ε / 2)) ^ n₁ ≤ Real.exp (Real.log b * (ε / 2)) ^ (2 * N + 1) :=
      pow_le_pow_right₀ hr.le (by omega)
    have h2 : Real.exp (Real.log b * (ε / 2)) ^ (2 * N + 1) =
        Real.exp (ε / 2 * ((2 * (N : ℝ) + 1) * Real.log b)) := by
      rw [← Real.exp_natCast_mul]; push_cast; ring_nf
    linarith
  have hDpos : (0 : ℝ) < D := lt_trans (Real.rpow_pos_of_pos (by unfold xx; positivity) _) hDlo
  calc blockL1K b g N D β ≤ _ := hcore
    _ ≤ Real.exp (ε / 2 * ((2 * (N : ℝ) + 1) * Real.log b)) *
        Real.exp (Real.log D - η * ((2 * (N : ℝ) + 1) * Real.log b) +
          ε / 2 * ((2 * (N : ℝ) + 1) * Real.log b)) := mul_le_mul_of_nonneg_right hCt (Real.exp_pos _).le
    _ = (D : ℝ) * xx b N ^ (-η + ε) := by
        rw [LK10_xx_rpow b N hb1, ← Real.exp_add]
        conv_rhs => rw [← Real.exp_log hDpos]
        rw [← Real.exp_add]; congr 1; ring

end KappaOmega2
