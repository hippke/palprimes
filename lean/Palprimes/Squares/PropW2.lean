import Palprimes.Squares.PropW

/-! # Proposition W up to `x^{0.2499}` (for the Ω ≤ 4 sieve) -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- **Prop W for the b-adic block `[b^j, b^{j+1})`** with `m = ⌊N/10000⌋` (primes up to `x^{0.2499}`). -/
theorem block_bound2 (b N j : ℕ) (hb : 2 ≤ b) (hN : 20000 ≤ N) (hj1 : 2 * N + 1 < 40 * (j + 1))
    (hj2 : 10000 * j ≤ 2499 * (2 * N + 1)) :
    ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime,
        (#((univ : Finset (DigVec b N)).filter
          (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) : ℝ) ≤
      27 * (b : ℝ) ^ (N + 1) * (16 * b * (N + 1) + 3) * gam b ^ (N / 10000) := by
  set m := N / 10000 with hm
  set S := (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime with hSdef
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hmℓ : m ≤ j + 1 := by omega
  have hlen : 2 * (j + 1) + m ≤ N + 1 := by omega
  have hj2' : 2 ≤ j := by omega
  have hbP : b < b ^ j := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ j := Nat.pow_lt_pow_right (by omega) (by omega)
  have hS : ∀ p ∈ S, p.Prime ∧ b ^ j ≤ p := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    exact ⟨h2, (Finset.mem_Ico.1 h1).1⟩
  have hK : (#S : ℝ) ≤ (b : ℝ) ^ (j + 1) := by
    have : #S ≤ b ^ (j + 1) := (card_filter_le _ _).trans (by rw [Nat.card_Ico]; omega)
    exact_mod_cast this
  have hD : ∀ w : ℤ, w ≠ 0 → |w| ≤ (wmax b N : ℤ) →
      (#(S.filter (fun p => p.Prime ∧ b ^ j ≤ p ∧ (p : ℤ) ^ 2 ∣ w)) : ℝ) ≤ 80 := by
    intro w hw hwm
    have hP2 : 2 ≤ b ^ j := by omega
    have h := card_prime_sq_dvd_le S w hw (b ^ j) hP2
    refine h.trans ?_
    have hwm' : (|w| : ℝ) ≤ ((b : ℝ) ^ (4 * N + 2)) := by
      have h12 := twelve_le_pow b N hb (by omega)
      have : wmax b N ≤ b ^ (4 * N + 2) := by
        unfold wmax
        calc 6 * ((N + 1) * (2 * b ^ (2 * N + 1))) = (12 * (N + 1)) * b ^ (2 * N + 1) := by ring
          _ ≤ b ^ (2 * N + 1) * b ^ (2 * N + 1) := Nat.mul_le_mul_right _ h12
          _ = b ^ (4 * N + 2) := by rw [← pow_add]; ring_nf
      have h' : ((|w| : ℤ) : ℝ) ≤ ((wmax b N : ℕ) : ℝ) := by exact_mod_cast hwm
      calc (|w| : ℝ) = ((|w| : ℤ) : ℝ) := by push_cast; rfl
        _ ≤ ((wmax b N : ℕ) : ℝ) := h'
        _ ≤ _ := by exact_mod_cast this
    have hwpos : (0 : ℝ) < |(w : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hw
    have hlogb : 0 < Real.log b := Real.log_pos hb1
    have hl1 : Real.log |(w : ℝ)| ≤ (4 * N + 2) * Real.log b := by
      calc Real.log |(w : ℝ)| ≤ Real.log ((b : ℝ) ^ (4 * N + 2)) :=
            Real.log_le_log hwpos (by simpa using hwm')
        _ = _ := by rw [Real.log_pow]; push_cast; ring
    have hl2 : Real.log ((b ^ j : ℕ) : ℝ) = j * Real.log b := by
      push_cast; rw [Real.log_pow]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hpos : 0 < 2 * ((j : ℝ) * Real.log b) := by positivity
    rw [hl2, div_le_iff₀ hpos]
    have hjN : (4 * (N : ℝ) + 2) ≤ 160 * j := by
      have : 4 * N + 2 ≤ 160 * j := by omega
      exact_mod_cast this
    nlinarith
  have hmain := propW_block b N (j + 1) m (b ^ j) (8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1)
    hb hmℓ hlen hbP le_rfl S hS ((b : ℝ) ^ (j + 1)) hK 80 (by norm_num) hD
  refine hmain.trans ?_
  -- the three terms
  set g : ℝ := (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) with hg
  have hg0 : 0 ≤ g := by positivity
  have hg1 : g ≤ 1 := by
    rw [hg, div_le_one (by positivity)]; nlinarith
  have hKρ : (b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) = g ^ m := by
    have hpow : (b : ℝ) ^ (j + 1) = (b : ℝ) ^ m * (b : ℝ) ^ (j + 1 - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, hg]
    have hne : (b : ℝ) ^ (j + 1 - m) ≠ 0 := by positivity
    field_simp
    rw [← mul_pow]
    congr 1
    field_simp
  have hT1 : (b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ + 80 ≤ 81 := by
    have : (b : ℝ) ^ (j + 1) ≤ (b : ℝ) ^ (N + 1 - (j + 1) - m) :=
      pow_le_pow_right₀ hb1.le (by omega)
    have h' : (b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact this
    linarith
  have hT3 : (b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80 ≤ 81 := by
    rw [hKρ]; linarith [pow_le_one₀ hg0 hg1 (n := m)]
  set A : ℝ := 16 * b * (N + 1) + 3 with hA
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 16 * b * (N + 1) := by positivity
    rw [hA]; linarith
  have hT2 : (b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) ≤ A * g ^ m := by
    have e : (b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) = (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * g ^ m := by rw [← hKρ]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hNj : N - (N + 1 - (j + 1)) = j := by omega
    rw [hNj]
    push_cast
    have hbj : (1 : ℝ) ≤ (b : ℝ) ^ j := one_le_pow₀ hb1.le
    have hjN : (j : ℝ) + 1 ≤ N + 1 := by
      have : j ≤ N := by omega
      have : (j : ℝ) ≤ N := by exact_mod_cast this
      linarith
    have : 2 * (8 * (b : ℝ) * (j + 1) * (b : ℝ) ^ (2 * j) + 1) / ((b : ℝ) ^ j) ^ 2 =
        16 * b * (j + 1) + 2 / ((b : ℝ) ^ j) ^ 2 := by
      field_simp; ring
    rw [this, hA]
    have h2 : 2 / ((b : ℝ) ^ j) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- combine
  have s1 : Real.sqrt ((b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ + 80) ≤ 9 := by
    calc _ ≤ Real.sqrt 81 := Real.sqrt_le_sqrt hT1
      _ = 9 := by rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s3 : Real.sqrt ((b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80) ≤ 9 := by
    calc _ ≤ Real.sqrt 81 := Real.sqrt_le_sqrt hT3
      _ = 9 := by rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s2 : Real.sqrt ((b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹)) ≤ Real.sqrt A * Real.sqrt g ^ m := by
    calc _ ≤ Real.sqrt (A * g ^ m) := Real.sqrt_le_sqrt hT2
      _ = _ := by rw [Real.sqrt_mul (by linarith), sqrt_pow' g hg0]
  have s23 : Real.sqrt (Real.sqrt ((b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹)) * Real.sqrt ((b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80)) ≤ 3 * A * gam b ^ m := by
    calc _ ≤ Real.sqrt ((Real.sqrt A * Real.sqrt g ^ m) * 9) :=
          Real.sqrt_le_sqrt (mul_le_mul s2 s3 (Real.sqrt_nonneg _) (by positivity))
      _ = Real.sqrt (Real.sqrt A) * gam b ^ m * 3 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            sqrt_pow' _ (Real.sqrt_nonneg _), show (9 : ℝ) = 3 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
          rfl
      _ ≤ A * gam b ^ m * 3 := by
          have h1 : Real.sqrt A ≤ A := sqrt_le_self' A hA1
          have h2 : Real.sqrt (Real.sqrt A) ≤ Real.sqrt A :=
            sqrt_le_self' _ (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hA1)
          have := gam_nonneg b
          gcongr
          linarith
      _ = 3 * A * gam b ^ m := by ring
  calc _ ≤ (b : ℝ) ^ (N + 1) * 9 * (3 * A * gam b ^ m) := by
        gcongr
    _ = _ := by rw [hA]; ring

/-- Prime squares for `x^{1/40} ≤ p ≤ x^{0.2499}` (the range of the Ω ≤ 4 sieve), saving `log³x`.
From `block_bound` on b-adic blocks and `card_piStar_lower`. -/
theorem squares_piStar2 (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ p ∈ (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 40 : ℝ)⌉₊
          ⌊((b : ℝ) ^ (2 * N + 1)) ^ (2499 / 10000 : ℝ)⌋₊).filter Nat.Prime,
          (countDvd (piStar b N) (p ^ 2) : ℝ)
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  obtain ⟨c, hc, N₀', hN₀'⟩ := card_piStar_lower b hb
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set C : ℝ := 27 * b * 10000 * (160000 * b + 3) * (20000 * Real.log b) ^ 3 with hC
  obtain ⟨n₀, hn₀⟩ := poly_gam_eventually b hb C c hc
  refine ⟨max (max 20000 N₀') (10000 * (n₀ + 1)), fun N hN => ?_⟩
  have hN60 : 20000 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNc : N₀' ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNn : 10000 * (n₀ + 1) ≤ N := le_trans (le_max_right _ _) hN
  set R := (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 40 : ℝ)⌉₊
    ⌊((b : ℝ) ^ (2 * N + 1)) ^ (2499 / 10000 : ℝ)⌋₊).filter Nat.Prime with hR
  set cnt : ℕ → ℝ := fun p => (#((univ : Finset (DigVec b N)).filter
    (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) : ℝ) with hcnt
  set B : ℝ := 27 * (b : ℝ) ^ (N + 1) * (16 * b * (N + 1) + 3) * gam b ^ (N / 10000) with hB
  -- block indices
  have hjb : ∀ p ∈ R, 2 * N + 1 < 40 * (Nat.log b p + 1) ∧
      10000 * Nat.log b p ≤ 2499 * (2 * N + 1) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.1 hpI
    have hp0 : p ≠ 0 := hpp.ne_zero
    have hlo : (b : ℝ) ^ (((2 * N + 1 : ℕ) : ℝ) * (1 / 40)) < (b : ℝ) ^ ((Nat.log b p + 1 : ℕ) : ℝ) := by
      rw [← rpow_x_eq, Real.rpow_natCast]
      calc ((b : ℝ) ^ (2 * N + 1)) ^ (1 / 40 : ℝ) ≤ ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 40 : ℝ)⌉₊ :=
            Nat.le_ceil _
        _ ≤ (p : ℝ) := by exact_mod_cast hp1
        _ < (b : ℝ) ^ (Nat.log b p + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by omega) p
    have hhi : (b : ℝ) ^ ((Nat.log b p : ℕ) : ℝ) ≤ (b : ℝ) ^ (((2 * N + 1 : ℕ) : ℝ) * (2499 / 10000)) := by
      rw [← rpow_x_eq, Real.rpow_natCast]
      calc (b : ℝ) ^ (Nat.log b p) ≤ (p : ℝ) := by exact_mod_cast Nat.pow_log_le_self b hp0
        _ ≤ ⌊((b : ℝ) ^ (2 * N + 1)) ^ (2499 / 10000 : ℝ)⌋₊ := by exact_mod_cast hp2
        _ ≤ _ := Nat.floor_le (by positivity)
    rw [Real.rpow_lt_rpow_left_iff hb1] at hlo
    rw [Real.rpow_le_rpow_left_iff hb1] at hhi
    push_cast at hlo hhi
    constructor
    · have : (2 * (N : ℝ) + 1) < 40 * ((Nat.log b p : ℝ) + 1) := by linarith
      exact_mod_cast this
    · have : 10000 * (Nat.log b p : ℝ) ≤ 2499 * (2 * N + 1) := by linarith
      exact_mod_cast this
  -- sum over blocks
  have hsum : ∑ p ∈ R, cnt p ≤ ∑ j ∈ R.image (Nat.log b),
      ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime, cnt p := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log b) (t := R.image (Nat.log b))
      (fun p hp => Finset.mem_image_of_mem _ hp) cnt]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpR, hpj⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, hpp⟩ := Finset.mem_filter.1 hpR
      refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨?_, ?_⟩, hpp⟩
      · rw [← hpj]; exact Nat.pow_log_le_self b hpp.ne_zero
      · rw [← hpj]; exact Nat.lt_pow_succ_log_self (by omega) p
    · intro p _ _
      exact Nat.cast_nonneg _
  have hblocks : ∑ j ∈ R.image (Nat.log b),
      ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime, cnt p ≤ (N + 1) * B := by
    have hsub : R.image (Nat.log b) ⊆ range (N + 1) := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      have := (hjb p hp).2
      rw [mem_range]; omega
    calc _ ≤ ∑ j ∈ R.image (Nat.log b), B := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
          exact block_bound2 b N (Nat.log b p) hb hN60 (hjb p hp).1 (hjb p hp).2
      _ = (#(R.image (Nat.log b)) : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N + 1) * B := by
          apply mul_le_mul_of_nonneg_right _ (by rw [hB]; have := gam_nonneg b; positivity)
          have := card_le_card hsub
          rw [card_range] at this
          exact_mod_cast this
  -- the final asymptotic comparison
  have hlogx : Real.log ((b : ℝ) ^ (2 * N + 1)) = (2 * N + 1) * Real.log b := by
    rw [Real.log_pow]; push_cast; ring
  have hcard := hN₀' N hNc
  set n := N / 10000 with hn
  have hnn : n₀ ≤ n := by omega
  have hN1 : (N : ℝ) + 1 ≤ 10000 * ((n : ℝ) + 1) := by
    have : N + 1 ≤ 10000 * (n + 1) := by omega
    exact_mod_cast this
  have hF := hn₀ n hnn
  have hbN : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  have hkey : (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 ≤ c * (b : ℝ) ^ N := by
    have hγ := gam_nonneg b
    have e : (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 = (b : ℝ) ^ N *
        (27 * b * (N + 1) * (16 * b * (N + 1) + 3) * ((2 * N + 1) * Real.log b) ^ 3 *
          gam b ^ n) := by rw [hB]; ring
    rw [e, mul_comm c]
    apply mul_le_mul_of_nonneg_left _ hbN.le
    refine le_trans ?_ hF
    rw [hC]
    have h2N : (2 * (N : ℝ) + 1) ≤ 20000 * ((n : ℝ) + 1) := by linarith
    have h16 : 16 * (b : ℝ) * (N + 1) + 3 ≤ (160000 * b + 3) * ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hgn : 0 ≤ gam b ^ n := pow_nonneg hγ n
    have hl3 : ((2 * N + 1) * Real.log b) ^ 3 ≤ (20000 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 3 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    calc 27 * (b : ℝ) * (N + 1) * (16 * b * (N + 1) + 3) * ((2 * N + 1) * Real.log b) ^ 3 *
          gam b ^ n
        ≤ 27 * (b : ℝ) * (10000 * ((n : ℝ) + 1)) * ((160000 * b + 3) * ((n : ℝ) + 1)) *
          ((20000 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 3) * gam b ^ n := by
          gcongr
      _ = 27 * b * 10000 * (160000 * b + 3) * (20000 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 5 *
          gam b ^ n := by ring
  calc ∑ p ∈ R, (countDvd (piStar b N) (p ^ 2) : ℝ) ≤ ∑ p ∈ R, cnt p := by
        apply Finset.sum_le_sum
        intro p _
        have h := countDvd_piStar_le b N p hb
        simp only [hcnt]
        exact_mod_cast h
    _ ≤ (N + 1) * B := hsum.trans hblocks
    _ ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
        rw [hlogx, le_div_iff₀ (by positivity)]
        calc (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 ≤ c * (b : ℝ) ^ N := hkey
          _ ≤ _ := hcard

end Palprimes
