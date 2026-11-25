import KappaOmega2.Items.LK10_Base

/-!
# LK15: the two ranges of the Farey total

Moduli `q` whose dyadic block `D = 2^{⌊log₂ q⌋}` satisfies `D ≤ x^{θ₀}` (so `q < 2x^{θ₀}`) by the free middle block
(`‖f(h/q + k/r)‖ ≤ qr/(2W)`, `W ≥ x^{3/10}`, `θ₀ < 3/20`); the other dyadic blocks by `TL¹_κ` at `ε = η/2`.
The total is `≪ N x^{−ν}`, smaller than any power of `log x`.
-/

namespace KappaOmega2

open Finset Real Palprimes

/-- `W ≥ x^{3/10}` in exponential form. -/
lemma LK15_W_ge (b N : ℕ) (hb : 1 ≤ b) :
    Real.exp (3 / 10 * ((2 * (N : ℝ) + 1) * Real.log b)) ≤ (WK b N : ℝ) := by
  obtain ⟨hs1, _, hs3⟩ := LK10_shape N
  have hW : (WK b N : ℝ) = Real.exp ((ellK N : ℝ) * Real.log b) := by
    unfold WK; rw [Nat.cast_pow, LK10_pow_exp b hb]
  rw [hW]
  apply Real.exp_le_exp.2
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  have h : 3 * (2 * N + 1) ≤ 10 * ellK N := by omega
  have h' : 3 * (2 * (N : ℝ) + 1) ≤ 10 * (ellK N : ℝ) := by exact_mod_cast h
  nlinarith

lemma LK15_bigB_pos (b : ℕ) (hb : 2 ≤ b) : 1 ≤ bigB b := by
  unfold bigB
  have : b < b ^ 3 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

lemma LK15_coprime_b (b q : ℕ) (hq : Nat.Coprime q (bigB b)) : Nat.Coprime q b :=
  Nat.Coprime.coprime_dvd_right (by unfold bigB; exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl) hq

/-- `Nat.log 2 Y < b(2N+1)` for `Y ≤ x`. -/
lemma LK15_log_le (b N Y : ℕ) (hb : 2 ≤ b) (hY : (Y : ℝ) ≤ xx b N) : Nat.log 2 Y + 1 ≤ b * (2 * N + 1) := by
  have hYx : Y ≤ b ^ (2 * N + 1) := by
    have : (Y : ℝ) ≤ ((b ^ (2 * N + 1) : ℕ) : ℝ) := by rw [Nat.cast_pow]; exact hY
    exact_mod_cast this
  have h2 : b ^ (2 * N + 1) < 2 ^ (b * (2 * N + 1)) := by
    rw [pow_mul]; exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
  rcases Nat.eq_zero_or_pos Y with h | h
  · subst h; simp only [Nat.log_zero_right, zero_add]; exact Nat.mul_pos (by omega) (by omega)
  · have := Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt hYx h2)
    omega

set_option maxHeartbeats 4000000 in
theorem itemLK15 : ItemLK15 := by
  intro b g θ η θ₀ hb hg hθ₀ hθ₀θ hθ₀3 hθ1 hη hTL A
  classical
  have hb1 : 1 ≤ b := by omega
  have hb2 : 2 ≤ b := by omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1R : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set lb := Real.log b with hlb
  have hlbpos : 0 < lb := Real.log_pos hb1R
  have hθpos : 0 < θ := lt_trans hθ₀ hθ₀θ
  set s₀ : ℝ := 3 / 10 - 2 * θ₀ with hs₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; linarith
  set η₃ : ℝ := min 1 (min (η / (4 * θ)) (s₀ / (2 * θ₀))) with hη₃
  have hη₃pos : 0 < η₃ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hη₃1 : η₃ ≤ 1 := min_le_left _ _
  have hη₃a : θ * η₃ ≤ η / 4 := by
    have : η₃ ≤ η / (4 * θ) := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hη₃b : θ₀ * η₃ ≤ s₀ / 2 := by
    have : η₃ ≤ s₀ / (2 * θ₀) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨C₃, hC₃⟩ := three_pow_omega_le_rpow η₃ hη₃pos
  have hC₃0 : 0 ≤ C₃ := by
    have := hC₃ 1 le_rfl
    simp at this; linarith
  obtain ⟨N₁, hN₁⟩ := hTL (η / 2) (by positivity)
  set ν : ℝ := min (η / 4) (s₀ / 2) with hν
  have hνpos : 0 < ν := lt_min (by positivity) (by positivity)
  have hν1 : ν ≤ η / 4 := min_le_left _ _
  have hν2 : ν ≤ s₀ / 2 := min_le_right _ _
  set r := bigB b with hr
  have hr1 : 1 ≤ r := LK15_bigB_pos b hb2
  set C' : ℝ := 4 * C₃ * r + 4 * C₃ * b with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set ρ : ℝ := Real.exp (-(2 * ν * lb)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, ← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : 0 < 2 * ν * lb := by positivity
    linarith
  obtain ⟨n₀, hn₀⟩ := eventually_poly_geom (C' * (2 * lb) ^ A) (A + 1) ρ hρ0 hρ1 1 one_pos
  refine ⟨max N₁ n₀, ?_⟩
  intro N hN k hk
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hn₀' : n₀ ≤ N := le_trans (le_max_right _ _) hN
  set L : ℝ := (2 * (N : ℝ) + 1) * lb with hL
  have hLpos : 0 < L := by positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  have hxx : xx b N = Real.exp L := LK10_xx_exp b N hb1
  have hx1 : 1 ≤ xx b N := by rw [hxx]; exact Real.one_le_exp hLpos.le
  set β : ℝ := (k : ℝ) / (r : ℝ) with hβ
  set X₀ : ℝ := xx b N ^ θ₀ with hX₀
  have hX₀e : X₀ = Real.exp (L * θ₀) := hxr θ₀
  have hX₀1 : 1 ≤ X₀ := by rw [hX₀e]; exact Real.one_le_exp (by positivity)
  set Y := ⌊xx b N ^ θ⌋₊ with hY
  have hYx : (Y : ℝ) ≤ xx b N ^ θ := Nat.floor_le (by positivity)
  have hYx' : (Y : ℝ) ≤ xx b N := hYx.trans (by
    calc xx b N ^ θ ≤ xx b N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hθ1.le
      _ = xx b N := Real.rpow_one _)
  have hW := LK15_W_ge b N hb1
  have hW0 : (0 : ℝ) < WK b N := lt_of_lt_of_le (Real.exp_pos _) hW
  have hL1f : ∀ d, 0 ≤ L1fareyK b g N d β := fun d => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set S := (Icc 2 Y).filter (fun q => Nat.Coprime q (bigB b)) with hS
  set w : ℕ → ℝ := fun q => (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1fareyK b g N q β
    with hw
  have hw0 : ∀ q, 0 ≤ w q := fun q => mul_nonneg (by positivity) (hL1f q)
  have hFK : FareyK b g N Y β = ∑ q ∈ S, w q := rfl
  set P : ℕ → Prop := fun q => ((2 ^ Nat.log 2 q : ℕ) : ℝ) ≤ X₀ with hP
  -- small moduli
  have hsmall_pt : ∀ q ∈ S.filter P, w q ≤ C₃ * (2 * X₀) ^ η₃ * (2 * X₀) * r / (2 * (WK b N : ℝ)) := by
    intro q hq
    simp only [hS, mem_filter, mem_Icc] at hq
    obtain ⟨⟨⟨hq2, _⟩, hqB⟩, hqP⟩ := hq
    have hq1 : 1 ≤ q := by omega
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hq2X : (q : ℝ) ≤ 2 * X₀ := by
      have h1 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
      have h2 : (q : ℝ) < ((2 ^ (Nat.log 2 q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [pow_succ, Nat.cast_mul] at h2
      have hqP' : ((2 ^ Nat.log 2 q : ℕ) : ℝ) ≤ X₀ := hqP
      push_cast at h2 hqP'
      linarith
    have hL1 : L1fareyK b g N q β ≤ q * ((q : ℝ) * r / (2 * (WK b N : ℝ))) := by
      unfold L1fareyK
      calc ∑ h ∈ redRes q, ‖fK b g N ((h : ℝ) / q + β)‖ ≤ ∑ _h ∈ redRes q, (q : ℝ) * r / (2 * (WK b N : ℝ)) := by
            apply Finset.sum_le_sum; intro h hh
            simp only [redRes, mem_filter, mem_range] at hh
            exact LK10_mid b g hg hb1 N q h k r hq2 (LK15_coprime_b b q hqB) hqB hr1 hh.2
        _ = #(redRes q) * ((q : ℝ) * r / (2 * (WK b N : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ q * ((q : ℝ) * r / (2 * (WK b N : ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have : #(redRes q) ≤ q := by
              calc #(redRes q) ≤ #(range q) := Finset.card_filter_le _ _
                _ = q := card_range q
            exact_mod_cast this
    have h3 := hC₃ q hq1
    calc w q ≤ (C₃ * (q : ℝ) ^ η₃ / q) * (q * ((q : ℝ) * r / (2 * (WK b N : ℝ)))) :=
          mul_le_mul (div_le_div_of_nonneg_right h3 hqpos.le) hL1 (hL1f q) (by positivity)
      _ = C₃ * (q : ℝ) ^ η₃ * q * r / (2 * (WK b N : ℝ)) := by field_simp
      _ ≤ C₃ * (2 * X₀) ^ η₃ * (2 * X₀) * r / (2 * (WK b N : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqpos.le hq2X hη₃pos.le) hC₃0)
            hq2X hqpos.le (by positivity)
  have hcard_small : (#(S.filter P) : ℝ) ≤ 2 * X₀ := by
    have hsub : S.filter P ⊆ Icc 1 ⌊2 * X₀⌋₊ := by
      intro q hq
      simp only [hS, mem_filter, mem_Icc] at hq
      obtain ⟨⟨⟨hq2, _⟩, _⟩, hqP⟩ := hq
      have h1 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
      have h2 : (q : ℝ) < ((2 ^ (Nat.log 2 q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      rw [pow_succ, Nat.cast_mul] at h2
      have hqP' : ((2 ^ Nat.log 2 q : ℕ) : ℝ) ≤ X₀ := hqP
      push_cast at h2 hqP'
      simp only [mem_Icc]
      exact ⟨by omega, Nat.le_floor (by linarith)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    calc (#(S.filter P) : ℝ) ≤ ((⌊2 * X₀⌋₊ + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ = (⌊2 * X₀⌋₊ : ℝ) := by norm_num
      _ ≤ 2 * X₀ := Nat.floor_le (by positivity)
  have hsmall : ∑ q ∈ S.filter P, w q ≤ 4 * C₃ * r * Real.exp (-(ν * L)) := by
    calc ∑ q ∈ S.filter P, w q ≤ ∑ _q ∈ S.filter P, C₃ * (2 * X₀) ^ η₃ * (2 * X₀) * r / (2 * (WK b N : ℝ)) :=
          Finset.sum_le_sum hsmall_pt
      _ = #(S.filter P) * (C₃ * (2 * X₀) ^ η₃ * (2 * X₀) * r / (2 * (WK b N : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * X₀ * (C₃ * (2 * X₀) ^ η₃ * (2 * X₀) * r / (2 * (WK b N : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard_small (by positivity)
      _ ≤ 2 * X₀ * (C₃ * (2 * Real.exp (L * θ₀ * η₃)) * (2 * X₀) * r /
            (2 * Real.exp (3 / 10 * L))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have e1 : (2 * X₀) ^ η₃ ≤ 2 * Real.exp (L * θ₀ * η₃) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), hX₀e, ← Real.exp_mul]
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            calc (2 : ℝ) ^ η₃ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη₃1
              _ = 2 := Real.rpow_one 2
          apply div_le_div₀ (by positivity) _ (by positivity) (by
            apply mul_le_mul_of_nonneg_left _ (by norm_num); rw [hL]; exact hW)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left e1 hC₃0
      _ = 4 * C₃ * r * Real.exp (L * θ₀ + L * θ₀ + L * θ₀ * η₃ - 3 / 10 * L) := by
          rw [hX₀e]; simp only [Real.exp_add, Real.exp_sub]; field_simp; ring
      _ ≤ 4 * C₃ * r * Real.exp (-(ν * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.2
          have h1 := mul_le_mul_of_nonneg_left hη₃b hLpos.le
          have h2 := mul_le_mul_of_nonneg_left hν2 hLpos.le
          rw [hs₀] at h1 h2
          nlinarith
  -- large moduli: dyadic blocks
  set I := Nat.log 2 Y + 1 with hI
  have hIb : I ≤ b * (2 * N + 1) := LK15_log_le b N Y hb2 hYx'
  have hmaps : ∀ q ∈ S.filter (fun q => ¬ P q), Nat.log 2 q ∈ range I := by
    intro q hq
    simp only [hS, mem_filter, mem_Icc] at hq
    exact mem_range.2 (Nat.lt_succ_of_le (Nat.log_mono_right hq.1.1.2))
  have hfib : ∀ i ∈ range I, ∑ q ∈ (S.filter (fun q => ¬ P q)).filter (fun q => Nat.log 2 q = i), w q ≤
      2 * C₃ * Real.exp (-(ν * L)) := by
    intro i _
    by_cases hiX : X₀ < ((2 ^ i : ℕ) : ℝ)
    · set D := 2 ^ i with hD
      have hD1 : 1 ≤ D := Nat.one_le_two_pow
      have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
      have hsub : (S.filter (fun q => ¬ P q)).filter (fun q => Nat.log 2 q = i) ⊆
          (Ico D (2 * D)).filter (fun d => Nat.Coprime d b) := by
        intro q hq
        simp only [hS, mem_filter, mem_Icc] at hq
        simp only [mem_filter, mem_Ico]
        have hq0 : q ≠ 0 := by omega
        refine ⟨⟨?_, ?_⟩, LK15_coprime_b b q hq.1.1.2⟩
        · rw [hD, ← hq.2]; exact Nat.pow_log_le_self 2 hq0
        · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
          rw [hq.2, pow_succ] at this; omega
      by_cases hne : ((S.filter (fun q => ¬ P q)).filter (fun q => Nat.log 2 q = i)).Nonempty
      swap
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty]; positivity
      have hDY : (D : ℝ) ≤ xx b N ^ θ := by
        obtain ⟨q, hq⟩ := hne
        simp only [hS, mem_filter, mem_Icc] at hq
        have h1 : D ≤ q := by rw [hD, ← hq.2]; exact Nat.pow_log_le_self 2 (by omega)
        have h2 : (D : ℝ) ≤ Y := by exact_mod_cast le_trans h1 hq.1.1.1.2
        exact h2.trans hYx
      have hTLD := hN₁ N hN₁' D ⟨i, rfl⟩ hiX hDY β
      set c : ℝ := C₃ * (2 * (D : ℝ)) ^ η₃ / D with hc
      have hc0 : 0 ≤ c := by positivity
      have hwc : ∀ q ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), w q ≤ c * L1fareyK b g N q β := by
        intro q hq
        simp only [mem_filter, mem_Ico] at hq
        apply mul_le_mul_of_nonneg_right _ (hL1f q)
        have hq1 : 1 ≤ q := le_trans hD1 hq.1.1
        have hqR : (D : ℝ) ≤ q := by exact_mod_cast hq.1.1
        have hq2 : (q : ℝ) ≤ 2 * D := by exact_mod_cast hq.1.2.le
        have hqpos : (0 : ℝ) < q := by linarith
        calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤ C₃ * (q : ℝ) ^ η₃ / q :=
              div_le_div_of_nonneg_right (hC₃ q hq1) hqpos.le
          _ ≤ C₃ * (2 * (D : ℝ)) ^ η₃ / q :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hqpos.le hq2 hη₃pos.le) hC₃0) hqpos.le
          _ ≤ c := div_le_div_of_nonneg_left (by positivity) hDpos hqR
      have hDθ : (D : ℝ) ^ η₃ ≤ Real.exp (L * θ * η₃) := by
        rw [Real.exp_mul, ← hxr]
        exact Real.rpow_le_rpow hDpos.le hDY hη₃pos.le
      calc _ ≤ ∑ q ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), w q :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw0 q)
        _ ≤ ∑ q ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), c * L1fareyK b g N q β :=
            Finset.sum_le_sum hwc
        _ = c * blockL1K b g N D β := by rw [← Finset.mul_sum]; rfl
        _ ≤ c * ((D : ℝ) * xx b N ^ (-η + η / 2)) := mul_le_mul_of_nonneg_left hTLD hc0
        _ = C₃ * 2 ^ η₃ * (D : ℝ) ^ η₃ * Real.exp (L * (-η + η / 2)) := by
            rw [hc, hxr, Real.mul_rpow (by norm_num) hDpos.le]; field_simp
        _ ≤ C₃ * 2 * Real.exp (L * θ * η₃) * Real.exp (L * (-η + η / 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul _ hDθ (by positivity) (by positivity)
            apply mul_le_mul_of_nonneg_left _ hC₃0
            calc (2 : ℝ) ^ η₃ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hη₃1
              _ = 2 := Real.rpow_one 2
        _ ≤ 2 * C₃ * Real.exp (-(ν * L)) := by
            rw [mul_assoc, ← Real.exp_add, mul_comm C₃ 2]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.2
            have h1 := mul_le_mul_of_nonneg_left hη₃a hLpos.le
            have h2 := mul_le_mul_of_nonneg_left hν1 hLpos.le
            nlinarith
    · have hemp : (S.filter (fun q => ¬ P q)).filter (fun q => Nat.log 2 q = i) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        simp only [mem_filter] at hq
        apply hq.1.2
        simp only [hP]
        rw [hq.2]; push Not at hiX; exact hiX
      rw [hemp, Finset.sum_empty]; positivity
  have hlarge : ∑ q ∈ S.filter (fun q => ¬ P q), w q ≤ (b * (2 * N + 1) : ℕ) * (2 * C₃ * Real.exp (-(ν * L))) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _i ∈ range I, 2 * C₃ * Real.exp (-(ν * L)) := Finset.sum_le_sum hfib
      _ = (I : ℝ) * (2 * C₃ * Real.exp (-(ν * L))) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hIb) (by positivity)
  have htot : FareyK b g N Y β ≤ C' * ((N : ℝ) + 1) * Real.exp (-(ν * L)) := by
    rw [hFK, ← Finset.sum_filter_add_sum_filter_not S P]
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hE0 : 0 ≤ Real.exp (-(ν * L)) := (Real.exp_pos _).le
    have h1 := add_le_add hsmall hlarge
    have h2 : 4 * C₃ * r * Real.exp (-(ν * L)) + ((b * (2 * N + 1) : ℕ) : ℝ) * (2 * C₃ * Real.exp (-(ν * L))) ≤
        C' * ((N : ℝ) + 1) * Real.exp (-(ν * L)) := by
      rw [hC']; push_cast
      have h3 : 0 ≤ C₃ * Real.exp (-(ν * L)) := by positivity
      have h4 : 0 ≤ (r : ℝ) * (C₃ * Real.exp (-(ν * L))) := by positivity
      have h5 : 0 ≤ (b : ℝ) * (C₃ * Real.exp (-(ν * L))) := by positivity
      nlinarith [mul_nonneg h4 hN0, mul_nonneg h5 hN0]
    linarith
  have hlogx : Real.log (xx b N) = L := by rw [hxx, Real.log_exp]
  rw [hlogx, le_div_iff₀ (pow_pos hLpos A)]
  have hLA : L ^ A ≤ (2 * lb) ^ A * ((N : ℝ) + 1) ^ A := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hLpos.le
    rw [hL]; nlinarith
  have hρN : Real.exp (-(ν * L)) ≤ ρ ^ N := by
    rw [hρ, ← Real.exp_natCast_mul]
    apply Real.exp_le_exp.2
    rw [hL]; nlinarith
  have hfin := hn₀ N hn₀'
  calc FareyK b g N Y β * L ^ A ≤ C' * ((N : ℝ) + 1) * Real.exp (-(ν * L)) * L ^ A :=
        mul_le_mul_of_nonneg_right htot (pow_nonneg hLpos.le _)
    _ ≤ C' * ((N : ℝ) + 1) * ρ ^ N * ((2 * lb) ^ A * ((N : ℝ) + 1) ^ A) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hρN (by positivity)) hLA (pow_nonneg hLpos.le _) (by positivity)
    _ = C' * (2 * lb) ^ A * ((N : ℝ) + 1) ^ (A + 1) * ρ ^ N := by ring
    _ ≤ 1 := hfin

end KappaOmega2
