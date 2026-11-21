import Palprimes.Sieve.Weighted

/-! # Counting form of the weighted sieve

`sieve_core_count` turns the weighted sum of `sieve_core` into a lower bound for the number of
elements with `Ω ≤ 5` all of whose prime factors are at least `x^{1/20}`, and
`sieve_count_large_factors` gives `≫ #A / log x` such elements. -/

open Finset Real

namespace Palprimes

/-- Each element contributes at most `λ` to `Σ (λ − pen)`, and only good ones contribute positively. -/
theorem card_good_ge (S0 : Finset ℕ) (bad : ℕ → Prop) [DecidablePred bad] (pen : ℕ → ℝ) (lam : ℝ)
    (hpen : ∀ n ∈ S0, 0 ≤ pen n) :
    ∑ n ∈ S0, (lam - pen n) ≤
      lam * (#(S0.filter bad) : ℝ) + lam * (#(S0.filter (fun n => ¬ bad n ∧ pen n < lam)) : ℝ) := by
  classical
  have hpt : ∀ n ∈ S0, lam - pen n ≤ (if bad n then lam else 0) +
      (if ¬ bad n ∧ pen n < lam then lam else 0) := by
    intro n hn
    have := hpen n hn
    by_cases h1 : bad n
    · simp [h1]; linarith
    · by_cases h2 : pen n < lam
      · simp [h1, h2]; linarith
      · simp [h1, h2]; linarith
  refine le_trans (Finset.sum_le_sum hpt) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  ring

open Classical in
/-- **Counting core of the weighted sieve**, for one `x`. -/
theorem sieve_core_count (A : Finset ℕ) (B : ℕ) (x : ℝ) (hx : 1 < x) (hB1 : 1 ≤ B)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ x ∧ Nat.Coprime n B)
    (W Z : ℕ) (hWZ : W ≤ Z) (hBZ : B < Z) (hxZ : x ^ ((1 : ℝ) / 20) ≤ (Z : ℝ))
    (hPW : ((∏ q ∈ PB B W, q : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25))
    (hZD : ∀ p : ℕ, 1 ≤ p → p < Z → 1 ≤ x ^ ((6 : ℝ) / 25) / p)
    (hyD : ∀ p : ℕ, 1 ≤ p → (p : ℝ) < x ^ ((23 : ℝ) / 100) → 1 ≤ x ^ ((6 : ℝ) / 25) / p)
    (eB eR : ℝ)
    (hB : ∑ p ∈ (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B),
        (1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p) ≤
        eB * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ)))
    (hR : ∑ p ∈ (Ico Z ⌈x ^ ((23 : ℝ) / 100)⌉₊).filter Nat.Prime,
        (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) /
          (p * selS (PB B Z) (x ^ ((6 : ℝ) / 25) / p)) ≤
        eR * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ)))
    (hlev : levelSum A B (x ^ ((6 : ℝ) / 25)) ≤ (#A : ℝ) / Real.log x ^ 3)
    (hsq : ∑ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime,
        (countDvd A (p ^ 2) : ℝ) ≤ (#A : ℝ) / Real.log x ^ 3) :
    (#A : ℝ) * ((8 / 5 * (1 - eB) - eR) * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))) -
        29 / 5 * ((#A : ℝ) / Real.log x ^ 3) ≤
      8 / 5 * (#(A.filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
        ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) := by
  classical
  set y := x ^ ((23 : ℝ) / 100) with hy
  set D := x ^ ((6 : ℝ) / 25) with hD
  set X := (#A : ℝ)
  set VZ := ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))
  set S0 := A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)
  set RP := (Ico Z ⌈y⌉₊).filter Nat.Prime
  set w : ℕ → ℝ := fun p => 1 - Real.log p / Real.log y
  set R := levelSum A B D
  have hL : 0 < Real.log x := Real.log_pos hx
  have hly : Real.log y = 23 / 100 * Real.log x := by rw [hy, Real.log_rpow (by linarith)]
  have hly0 : 0 < Real.log y := by rw [hly]; positivity
  have hX : (0 : ℝ) ≤ X := by simp only [X]; exact Nat.cast_nonneg _
  have hR0 : 0 ≤ R := levelSum_nonneg A B D
  have hVZ := V_PB_pos B Z
  -- weights
  have hw : ∀ p ∈ RP, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p hp
    simp only [RP, mem_filter, mem_Ico] at hp
    have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hpy : (p : ℝ) < y := Nat.lt_ceil.1 hp.1.2
    have h1 : 0 ≤ Real.log p := Real.log_nonneg hp0
    have h2 : Real.log p < Real.log y := Real.log_lt_log (by linarith) hpy
    simp only [w]
    constructor
    · rw [sub_nonneg, div_le_one hly0]; linarith
    · have : 0 ≤ Real.log p / Real.log y := div_nonneg h1 hly0.le
      linarith
  have hRP : ∀ p ∈ RP, p.Prime ∧ Z ≤ p ∧ ¬ p ∣ B ∧ 1 ≤ D / p := by
    intro p hp
    simp only [RP, mem_filter, mem_Ico] at hp
    refine ⟨hp.2, hp.1.1, fun h => ?_, hyD p hp.2.one_lt.le (Nat.lt_ceil.1 hp.1.2)⟩
    have := Nat.le_of_dvd (by omega) h; have := hp.1.1; omega
  -- the two main estimates
  have hlow := lower_S0 A B D W Z hWZ hPW hZD
  have hup := upper_rich A B D Z RP w hRP hw
  -- the penalty sum
  set pen : ℕ → ℝ := fun n => richertPenalty y n
  have hpen0 : ∀ n ∈ S0, 0 ≤ pen n := by
    intro n hn
    simp only [pen, richertPenalty]
    apply Finset.sum_nonneg; intro p hp
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.1.one_lt.le
    have h2 : Real.log p < Real.log y := Real.log_lt_log (by linarith) hp.2
    rw [sub_nonneg, div_le_one hly0]; linarith
  have hpensum : ∑ n ∈ S0, pen n = ∑ p ∈ RP, w p * (#(S0.filter (p ∣ ·)) : ℝ) := by
    have h1 : ∀ n ∈ S0, pen n = ∑ p ∈ RP.filter (· ∣ n), w p := by
      intro n hn
      simp only [S0, mem_filter] at hn
      obtain ⟨h1, h2, h3⟩ := hA n hn.1
      simp only [pen, richertPenalty]
      rw [primeFactors_eq_RP B Z y n (by omega) h3 hn.2]
    rw [Finset.sum_congr rfl h1]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    split_ifs <;> simp
  -- the bad count
  set bad : ℕ → Prop := fun n => ∃ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime, p ^ 2 ∣ n
  have hbad : (#(S0.filter bad) : ℝ) ≤ X / Real.log x ^ 3 := by
    refine le_trans ?_ hsq
    have hsub : S0.filter bad ⊆ ((Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime).biUnion
        (fun p => A.filter ((p ^ 2) ∣ ·)) := by
      intro n hn
      simp only [S0, bad, mem_filter] at hn
      obtain ⟨⟨hnA, -⟩, p, hp, hpn⟩ := hn
      rw [mem_biUnion]; exact ⟨p, mem_filter.2 hp, mem_filter.2 ⟨hnA, hpn⟩⟩
    have := le_trans (card_le_card hsub) card_biUnion_le
    simp only [countDvd]; exact_mod_cast this
  -- lower bound for the weighted sum
  have hWlow : X * ((8 / 5 * (1 - eB) - eR) * VZ) - 21 / 5 * R ≤ ∑ n ∈ S0, (8 / 5 - pen n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hpensum]
    have hRP' : ∑ p ∈ RP, w p / (p * selS (PB B Z) (D / p)) ≤ eR * VZ := hR
    have hS0 : X * VZ - X * (eB * VZ) - 2 * R ≤ (#S0 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hB hX
      linarith [hlow]
    have hup' : ∑ p ∈ RP, w p * (#(S0.filter (p ∣ ·)) : ℝ) ≤ X * (eR * VZ) + R := by
      have := mul_le_mul_of_nonneg_left hRP' hX
      linarith [hup]
    nlinarith
  have hcard := card_good_ge S0 bad pen (8 / 5) hpen0
  -- good elements have `Ω ≤ 5` and only prime factors `≥ x^{1/20}`
  have hsub : S0.filter (fun n => ¬ bad n ∧ pen n < 8 / 5) ⊆ A.filter (fun n =>
      Nat.IsAtMostAlmostPrime 5 n ∧ ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ)) := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨hnS, hnbad, hnpen⟩ := hn
    have hnS' := hnS
    simp only [S0, mem_filter] at hnS'
    obtain ⟨hn1, hnx, hncop⟩ := hA n hnS'.1
    have hsmall : ∀ p : ℕ, p.Prime → p ∣ n → Z ≤ p := by
      intro p hp hpn
      by_contra hpZ; push_neg at hpZ
      by_cases hpB : p ∣ B
      · have := Nat.Coprime.coprime_dvd_left hpn hncop
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hpB)
      · exact hnS'.2 p (by simp only [PB, mem_filter, mem_range]; exact ⟨hpZ, hp, hpB⟩) hpn
    rw [mem_filter]
    refine ⟨hnS'.1, ⟨by omega, ?_⟩, ?_⟩
    · apply richert_omega_le_five x hx n hn1 hnx _ hnpen
      intro p hp hpy hp2
      have hpZ := hsmall p hp (dvd_trans (dvd_pow_self p two_ne_zero) hp2)
      apply hnbad
      refine ⟨p, ?_, hp2⟩
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨?_, Nat.le_floor hpy.le⟩, hp⟩
      apply Nat.ceil_le.2
      have : (Z : ℝ) ≤ p := by exact_mod_cast hpZ
      linarith
    · intro p hp
      have hpZ := hsmall p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      have : (Z : ℝ) ≤ p := by exact_mod_cast hpZ
      linarith
  have hc := card_le_card hsub
  have hc' : (#(S0.filter (fun n => ¬ bad n ∧ pen n < 8 / 5)) : ℝ) ≤ (#(A.filter (fun n =>
      Nat.IsAtMostAlmostPrime 5 n ∧ ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) := by
    exact_mod_cast hc
  have hRl : R ≤ X / Real.log x ^ 3 := hlev
  nlinarith

/-- `V(Z_c) log x ≥ 5` eventually (two-sided Mertens 3). -/
theorem eventually_VZ_log (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℝ in Filter.atTop, 5 ≤ (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) * Real.log x := by
  have H := tendsto_Zc.eventually (mertens_two_sided C₃ hC₃ B hB (1 / 2) (by norm_num) (by norm_num))
  have H3 := tendsto_Zc.eventually (Filter.eventually_ge_atTop 3)
  filter_upwards [H, H3, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h3 hx
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  have hVZ := V_PB_pos B (Zc x)
  have hβ := betaB_pos B
  have hβ1 := betaB_le_one B
  have he := exp_neg_gamma_ge
  have hZ : Real.log ((Zc x : ℝ) - 1) ≤ Real.log x / 20 := by
    have h3' : (3 : ℝ) ≤ Zc x := by exact_mod_cast h3
    have := Real.log_le_log (by linarith) (Zc_sub_one_le x hx.le)
    rw [Real.log_rpow (by linarith)] at this; linarith
  have hlow : 1 / 2 * (10000 / 17813) ≤ VZ * betaB B * (Real.log x / 20) := by
    have := h1.1
    have h3 : VZ * betaB B * Real.log ((Zc x : ℝ) - 1) ≤ VZ * betaB B * (Real.log x / 20) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    nlinarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have : VZ * betaB B * (Real.log x / 20) ≤ VZ * (Real.log x / 20) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  nlinarith

open Classical in
/-- **Counting form of the abstract weighted sieve.** Under the hypotheses of `sieve_omega_le_five`,
at least `#A / (40 log x)` elements of `A` have `Ω ≤ 5` and no prime factor below `x^{1/20}`. -/
theorem sieve_count_large_factors (B : ℕ) (hB : 1 ≤ B) :
    ∃ x₀ : ℝ, ∀ (A : Finset ℕ) (x : ℝ), x₀ ≤ x →
      (∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ x ∧ Nat.Coprime n B) →
      ∑ q ∈ (Icc 1 ⌊x ^ (6 / 25 : ℝ)⌋₊).filter (fun q => Nat.Coprime q B),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd A q : ℝ) - (#A : ℝ) / q| ≤ (#A : ℝ) / (Real.log x) ^ 3 →
      ∑ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime,
          (countDvd A (p ^ 2) : ℝ) ≤ (#A : ℝ) / (Real.log x) ^ 3 →
      1 / 40 * ((#A : ℝ) / Real.log x) ≤
        (#(A.filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
          ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ) := by
  obtain ⟨c₁, hc₁⟩ := mertens1_upper
  obtain ⟨C₂, hC₂⟩ := mertens2_interval
  obtain ⟨C₃, hC₃⟩ := mertens3
  set δ : ℝ := 1 / 1000
  set eB : ℝ := 1 / 2000 + δ + (73899 / 500000 + δ)
  set eR : ℝ := 1200877 / 1000000 + δ
  have hc0 : (1 : ℝ) / 50 ≤ 8 / 5 * (1 - eB) - eR := by norm_num [eB, eR, δ]
  have hRt := R_total C₂ C₃ c₁ hC₂ hC₃ hc₁ B hB δ (by norm_num)
  have hBt := B_total C₂ C₃ c₁ hC₂ hC₃ hc₁ B hB δ (by norm_num)
  have hTt := tail_total c₁ hc₁ C₃ hC₃ B hB δ (by norm_num)
  have hV := eventually_VZ_log C₃ hC₃ B hB
  have hBZ := tendsto_Zc.eventually (Filter.eventually_gt_atTop B)
  have HL := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (11 : ℝ))
  have hall : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ p ∈ (Ioc ⌊x ^ (aR 0)⌋₊ ⌊x ^ (aR 48)⌋₊).filter Nat.Prime, fR B x p ≤
        (1200877 / 1000000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (∑ p ∈ (Ioc ⌊x ^ (aB 0)⌋₊ ⌊x ^ (aB 20)⌋₊).filter Nat.Prime, fB B x p ≤
        (73899 / 500000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p), fB B x p ≤
        (1 / 2000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (5 ≤ (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) * Real.log x) ∧ 11 ≤ Real.log x ∧
      B < Zc x ∧ Wc x ≤ Zc x ∧ ((∏ q ∈ PB B (Wc x), q : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25) ∧ 1 < x := by
    filter_upwards [hRt, hBt, hTt, hV, HL, hBZ, eventually_W_le_Z, eventually_PW B,
      Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hall
  refine ⟨x₀, fun A x hx hA hlev hsq => ?_⟩
  obtain ⟨hR1, hB1, hT1, hVL, hL11, hBZx, hWZ, hPW, hx1⟩ := hx₀ x hx
  have ha0 : aR 0 = 49 / 1000 := by norm_num [aR]
  have ha48 : aR 48 = 23 / 100 := by norm_num [aR]
  have hb0 : aB 0 = 1 / 200 := by norm_num [aB]
  have hb20 : aB 20 = 1 / 20 := by norm_num [aB]
  rw [ha0, ha48] at hR1
  rw [hb0, hb20] at hB1
  have h20 : x ^ ((1 : ℝ) / 20) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have h23 : x ^ ((23 : ℝ) / 100) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hcore := sieve_core_count A B x hx1 hB hA (Wc x) (Zc x) hWZ hBZx (Nat.le_ceil _) hPW
    (fun p hp1 hpZ => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
      rw [le_div_iff₀ hp0, one_mul]
      have : (p : ℝ) < x ^ ((1 : ℝ) / 20) := Nat.lt_ceil.1 hpZ
      linarith)
    (fun p hp1 hpy => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
      rw [le_div_iff₀ hp0, one_mul]; linarith)
    eB eR
    (by
      refine le_trans (B_glue B x hx1) ?_
      have : eB * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) =
          (1 / 2000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) +
          (73899 / 500000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) := by simp only [eB]; ring
      rw [this]; exact add_le_add hT1 hB1)
    (le_trans (R_glue B x hx1) hR1)
    hlev hsq
  -- arithmetic: `c VZ ≥ 1/(10 L)` and `29/5 · X/L³ ≤ 29/5 · X/(121 L)`
  set L := Real.log x
  set X := (#A : ℝ)
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  set T := (#(A.filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, x ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ)
  have hL0 : 0 < L := by linarith
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hcV : 1 / 10 / L ≤ (8 / 5 * (1 - eB) - eR) * VZ := by
    rw [div_le_iff₀ hL0]
    have hVZ0 := (V_PB_pos B (Zc x)).le
    calc 1 / 10 = 1 / 50 * 5 := by norm_num
      _ ≤ (8 / 5 * (1 - eB) - eR) * (VZ * L) := mul_le_mul hc0 hVL (by norm_num) (by linarith)
      _ = _ := by ring
  have hL3 : X / L ^ 3 ≤ X / L / 121 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hL2 : (121 : ℝ) ≤ L ^ 2 := by nlinarith
    have : (121 : ℝ) * L ≤ L ^ 3 := by
      have := mul_le_mul_of_nonneg_left hL2 hL0.le
      calc (121 : ℝ) * L = L * 121 := by ring
        _ ≤ L * L ^ 2 := this
        _ = L ^ 3 := by ring
    nlinarith
  have h1 : X * (1 / 10 / L) ≤ X * ((8 / 5 * (1 - eB) - eR) * VZ) := mul_le_mul_of_nonneg_left hcV hX0
  have h2 : X * (1 / 10 / L) = 1 / 10 * (X / L) := by ring
  nlinarith

end Palprimes
