import KappaOmega2.SkelLevelK
import KappaOmega2.SkelMain
import Palprimes.Omega4.Skeleton
import Palprimes.AlmostPrime.OmegaLeFive

/-!
# Skeleton K: all items ⇒ Ω ≤ 2 for κ-palindromes (κ = 7/10) in every base `b ≥ 3`

`skeletonK : AllItemsK → MainTheoremK ∧ MainCountK`, sorry-free. The weighted sieve sum
`Σ_{n<x} a_n [ν_{y,U}(n) ≤ 2] w(p(n))` is bounded below by `X_w·MT − K·(level sum)` (pointwise inequality,
`SkelSieve`), `MT ≥ c/log y` (`SkelMain`), the level sum and the square sum are `≤ (log x)^{−2}` (`SkelLevel`), and above by
`W(1)(#good·2^{−m}W^{−1} + square sum)`; `X ≥ c` (LK13).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

theorem y_pow_eq (x : ℝ) (hx : 0 < x) (a : ℝ) : (x ^ thS) ^ a = x ^ (thS * a) := by
  rw [← Real.rpow_mul hx.le]

theorem thS_mm : thS * mm = c0 := by norm_num [thS, mm, c0]
theorem thS_UU : thS * UU = c1 := by norm_num [thS, UU, c1]

/-- `y = x^θ ≥ Y` for large `N`. -/
theorem y_large (b : ℕ) (hb : 2 ≤ b) (Y : ℝ) : ∃ N₀ : ℕ, ∀ N ≥ N₀, Y ≤ xx b N ^ thS := by
  obtain ⟨N₀, h⟩ := xx_large b hb ((max Y 1) ^ (1 / thS))
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := h N hN
  have hth : (0 : ℝ) < thS := by norm_num [thS]
  have h2 : ((max Y 1) ^ (1 / thS)) ^ thS ≤ xx b N ^ thS := Real.rpow_le_rpow (by positivity) h1 hth.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hth.ne', Real.rpow_one] at h2
  exact le_trans (le_max_left _ _) h2

theorem mem_kpiStar {b N n : ℕ} (h : n ∈ kpiStar b N) :
    b ^ (2 * N) ≤ n ∧ n < b ^ (2 * N + 1) ∧ IsKappaPal b n ∧ Nat.Coprime n (bigB b) := by
  unfold kpiStar at h
  rw [Finset.mem_filter, Finset.mem_Ico] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

set_option maxHeartbeats 4000000 in
/-- The counting form for one base. -/
theorem count_lowerK (H : AllItemsK) (b : ℕ) (hb : 3 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * (2 : ℝ) ^ mK N * (WK b N : ℝ) / Real.log (xx b N) ≤
        (#((kpiStar b N).filter (fun n => Ω n ≤ 2 ∧ ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ) := by
  classical
  obtain ⟨⟨hS01, hS02, hS03, hS04, hS05, hS06, hS07, hS08, hS09, hS10, hS11, hS12, hS13, hS14,
    hS15, hM01, hM02, hM03, hM04, hM05, hM06, hM07, hM08, hM09, hM10, hM11, hM12, hM13⟩,
    ⟨hL01, hL02, hL03, hLK01, hLK06, hLK07, hLK08, hLK09, hLKM, hLK10, hLK13, hLK14, hLK15, hLK17, hQK01, hQK03,
    hQK04⟩⟩ := H
  have hb2 : 2 ≤ b := by omega
  set g : ℕ → ℝ := recGKR b with hg
  obtain ⟨hgw, hg1, hg3, -⟩ := recK_data hL01 hL02 hL03 hLK01 hLK06 hLK07 b hb
  -- the band data
  obtain ⟨B, ε₀, hε₀, hB, hallow, hcEta, hcost⟩ := hS10
  obtain ⟨ε, hε, hε1, cM, hcM, yM, hMT⟩ :=
    mainterm_lower hS05 hS13 hS14 hM01 hM02 hM03 hM04 hM05 hM06 hM07 hM08 hM09 hM10 hM11 hM12 hM13 b hb2 B hB
      hcEta hcost
  obtain ⟨yP, hP⟩ := pointwise hS01 hS02 hS03 hS04 hS05 hS06 hS07 hS08 hS09 hS12 hS13 hS14 hS15 b hb2 B hB ε₀ hε₀
    hallow ε hε hε1
  have hetas : ∀ e ∈ ([] :: B.etas), StepOK e := by
    intro e he
    rcases List.mem_cons.1 he with h | h
    · rw [h]; exact stepOK_nil
    · exact hB.2.2.2.2.1 e h
  obtain ⟨K, yK, hK⟩ := hS11 b hb2 B hB (hS09 b hb2 _ hetas) ε hε.le hε1
  obtain ⟨cX, hcX, NX, hX⟩ := hLK13 b g hb hgw hg1
  obtain ⟨NL, hNL⟩ := level_boundK hL01 hL02 hL03 hLK01 hLK06 hLK07 hLK08 hLK09 hLKM hLK10 hLK14 hLK15 b hb 2
  obtain ⟨NQ, hNQ⟩ := squares_boundK hL01 hL02 hL03 hLK01 hLK06 hLK07 hLK08 hLK09 hLKM hLK10 hLK17 hQK01 hQK03
    hQK04 b hb 2
  obtain ⟨NY, hNY⟩ := y_large b hb2 (max (max yM yP) (max yK 2))
  set Kp : ℝ := max K 0 with hKp
  have hW1 : (0 : ℝ) < W1 := by norm_num [W1]
  have hth : (0 : ℝ) < thS := by norm_num [thS]
  set c₀' : ℝ := cX * cM / (W1 * thS) with hc₀'
  have hc₀'0 : 0 < c₀' := by positivity
  obtain ⟨NLx, hNLx⟩ := logx_large b hb2 (4 * (Kp / W1 + 1) / c₀' + 1)
  refine ⟨c₀' / 3, by positivity, max (max (max NX NL) (max NQ NY)) (max NLx 1), fun N hN => ?_⟩
  have hNX : NX ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hNL' : NL ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hN)
  have hNQ' : NQ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hNY' : NY ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hN)
  have hNLx' : NLx ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  set x : ℝ := xx b N with hxdef
  have hx1 : 1 < x := one_lt_xx b N hb2
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ thS with hydef
  have hyY := hNY N hNY'
  have hyM : yM ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hyY
  have hyP : yP ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hyY
  have hyK : yK ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hyY
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hyY
  have hy1 : 1 < y := by linarith
  set L : ℝ := Real.log x with hLdef
  have hL0 : 0 < L := Real.log_pos hx1
  have hLy : Real.log y = thS * L := by rw [hydef, Real.log_rpow hx0]
  set z : ℝ := y ^ UU with hzdef
  have hz : z = x ^ c1 := by rw [hzdef, hydef, y_pow_eq x hx0, thS_UU]
  have hym : y ^ mm = x ^ c0 := by rw [hydef, y_pow_eq x hx0, thS_mm]
  have hyx : y ^ (1 / thS) = x := by
    rw [hydef, ← Real.rpow_mul hx0.le, mul_one_div_cancel hth.ne', Real.rpow_one]
  obtain ⟨hw0, hwle, hwU, hwzero, hwlin, -, -⟩ := hS05 y hy1
  -- notation
  set Xn : ℕ := b ^ (2 * N + 1) with hXn
  have hxXn : x = (Xn : ℝ) := by rw [hxdef, xx, hXn]; push_cast; ring
  set c := cSieve b B ε y with hcdef
  set DP := (primorialLt z).divisors with hDP
  set w := wy y with hw
  set tgt : ℕ → ℝ := ptarget y UU w with htgt
  set good := (kpiStar b N).filter (fun n => Ω n ≤ 2 ∧ ∀ p ∈ n.primeFactors, x ^ c0 < (p : ℝ)) with hgood
  set Pset := (Icc 1 ⌊x ^ c1⌋₊).filter (fun p : ℕ => p.Prime ∧ x ^ c0 < (p : ℝ)) with hPset
  have hseq := hLK17 b g (1 / 2) N hb hN1 hgw.1 hg3
  have haW := hseq.1
  have hAW := hseq.2.1
  have hXW1 : XK b g N ≤ 1 := hseq.2.2 hgw
  -- (P) lower bound of the sieve sum
  have hpt : ∀ n ∈ range Xn, aK b g N n * (∑ d ∈ n.divisors, c d) ≤ aK b g N n * tgt n := by
    intro n hn
    by_cases h0 : aK b g N n = 0
    · rw [h0]; simp
    have hmem := (haW n).2.2 h0
    obtain ⟨hlo, hhi, -, -⟩ := mem_kpiStar hmem
    have hn2 : 2 ≤ n := by
      have : b ≤ b ^ (2 * N) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hnx : (n : ℝ) < y ^ (1 / thS) := by rw [hyx, hxdef, xx]; exact_mod_cast hhi
    exact mul_le_mul_of_nonneg_left (hP y hyP n hn2 hnx) (haW n).1
  have hsupp : ∀ d, c d ≠ 0 → d ∈ DP ∧ Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ y := by
    intro d hd
    obtain ⟨⟨hsq, h1, hy', hdvd⟩, -⟩ := hK y hyK d hd
    refine ⟨?_, hsq, h1, hy'⟩
    rw [hDP, Nat.mem_divisors]
    refine ⟨hdvd, ?_⟩
    unfold primorialLt; exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
  have hdiv_eq : ∀ n ∈ range Xn, aK b g N n * (∑ d ∈ n.divisors, c d) =
      aK b g N n * ∑ d ∈ DP, (if d ∣ n then c d else 0) := by
    intro n _
    by_cases h0 : n = 0
    · subst h0
      have : aK b g N 0 = 0 := by
        by_contra hne
        obtain ⟨hlo, -, -, -⟩ := mem_kpiStar ((haW 0).2.2 hne)
        have : 1 ≤ b ^ (2 * N) := Nat.one_le_pow _ _ (by omega)
        omega
      simp [this]
    congr 1
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mem_divisors.2 ⟨hd.2, h0⟩
    · intro d hd
      rw [Finset.mem_sdiff, Finset.mem_filter] at hd
      by_contra hcd
      exact hd.2 ⟨(hsupp d hcd).1, (Nat.mem_divisors.1 hd.1).1⟩
    · intro d _; rfl
  have hexch : ∑ n ∈ range Xn, aK b g N n * (∑ d ∈ n.divisors, c d) = ∑ d ∈ DP, c d * AK b g N d := by
    rw [Finset.sum_congr rfl hdiv_eq]
    simp_rw [Finset.mul_sum, hAW]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    split_ifs <;> ring
  have hsplit : ∑ d ∈ DP, c d * AK b g N d = XK b g N * MTs b B ε y + ∑ d ∈ DP, c d * RK b g N d := by
    unfold MTs
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _
    unfold RK; ring
  have hrem : -(Kp * levelSumK b g N ⌊y⌋₊) ≤ ∑ d ∈ DP, c d * RK b g N d := by
    have h1 : |∑ d ∈ DP, c d * RK b g N d| ≤ ∑ d ∈ DP.filter (fun d => c d ≠ 0), Kp * ((3 : ℝ) ^ ω d * |RK b g N d|) := by
      rw [Finset.sum_filter]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun d _ => ?_))
      split_ifs with hcd
      · rw [abs_mul]
        have := (hK y hyK d hcd).2
        have hK' : |c d| ≤ Kp * 3 ^ ω d := le_trans this (by gcongr; exact le_max_left _ _)
        calc |c d| * |RK b g N d| ≤ Kp * 3 ^ ω d * |RK b g N d| := by gcongr
          _ = _ := by ring
      · push Not at hcd; rw [hcd]; simp
    have h2 : ∑ d ∈ DP.filter (fun d => c d ≠ 0), Kp * ((3 : ℝ) ^ ω d * |RK b g N d|) ≤
        Kp * levelSumK b g N ⌊y⌋₊ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
      unfold levelSumK
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨-, hsq, h1, hy'⟩ := hsupp d hd.2
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h1, Nat.le_floor hy'⟩, hsq⟩
      · intro d _ _; positivity
    have := neg_abs_le (∑ d ∈ DP, c d * RK b g N d)
    linarith
  -- (U) upper bound of the sieve sum
  have hwminFac : ∀ n : ℕ, 2 ≤ n → 0 < w n.minFac → x ^ c0 < (n.minFac : ℝ) := by
    intro n hn hpos
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    rw [← hym]
    by_contra hle
    push Not at hle
    have := hwzero _ hp hle
    rw [hw] at hpos
    linarith
  have hup : ∀ n ∈ range Xn, aK b g N n * tgt n ≤
      W1 * ((if n ∈ good then aK b g N n else 0) + ∑ p ∈ Pset, if p ^ 2 ∣ n then aK b g N n else 0) := by
    intro n hn
    have ha0 := (haW n).1
    have hsum0 : 0 ≤ ∑ p ∈ Pset, (if p ^ 2 ∣ n then aK b g N n else 0) :=
      Finset.sum_nonneg (fun p _ => by split_ifs <;> first | exact ha0 | exact le_rfl)
    have hrhs0 : 0 ≤ W1 * ((if n ∈ good then aK b g N n else 0) + ∑ p ∈ Pset, if p ^ 2 ∣ n then aK b g N n else 0) := by
      have : 0 ≤ (if n ∈ good then aK b g N n else 0) := by split_ifs <;> first | exact ha0 | exact le_rfl
      positivity
    by_cases h0 : aK b g N n = 0
    · calc aK b g N n * tgt n = 0 := by rw [h0, zero_mul]
        _ ≤ _ := hrhs0
    have hmem := (haW n).2.2 h0
    obtain ⟨hlo, hhi, -, -⟩ := mem_kpiStar hmem
    have hn2 : 2 ≤ n := by
      have : b ≤ b ^ (2 * N) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have htgt_le : tgt n ≤ W1 := by
      rw [htgt]; unfold ptarget; split_ifs
      · exact hwle _ hp
      · norm_num [W1]
    by_cases hnu : nu n (y ^ UU) ≤ 2
    · have htn : tgt n = w n.minFac := by rw [htgt]; unfold ptarget; rw [if_pos hnu]
      by_cases hwpos : 0 < w n.minFac
      · have hbig := hwminFac n hn2 hwpos
        by_cases hbad : ∃ p ∈ Pset, p ^ 2 ∣ n
        · obtain ⟨p, hpP, hpn⟩ := hbad
          have hsingle : aK b g N n ≤ ∑ p ∈ Pset, if p ^ 2 ∣ n then aK b g N n else 0 := by
            have := Finset.single_le_sum (f := fun p => if p ^ 2 ∣ n then aK b g N n else 0)
              (fun q _ => by split_ifs <;> first | exact ha0 | exact le_rfl) hpP
            simpa [hpn] using this
          have : 0 ≤ (if n ∈ good then aK b g N n else 0) := by split_ifs <;> first | exact ha0 | exact le_rfl
          calc aK b g N n * tgt n ≤ aK b g N n * W1 := mul_le_mul_of_nonneg_left htgt_le ha0
            _ ≤ W1 * ((if n ∈ good then aK b g N n else 0) + ∑ p ∈ Pset, if p ^ 2 ∣ n then aK b g N n else 0) := by
                nlinarith
        · push Not at hbad
          have hallbig : ∀ p ∈ n.primeFactors, x ^ c0 < (p : ℝ) := by
            intro p hp'
            have : n.minFac ≤ p := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp').two_le
              (Nat.dvd_of_mem_primeFactors hp')
            have : (n.minFac : ℝ) ≤ p := by exact_mod_cast this
            linarith
          have hsq : ∀ p : ℕ, p.Prime → x ^ c0 < p → (p : ℝ) < y ^ UU → ¬ p ^ 2 ∣ n := by
            intro p hpp h1 h2 hdvd
            apply hbad p _ hdvd
            rw [hPset, Finset.mem_filter, Finset.mem_Icc]
            refine ⟨⟨hpp.one_lt.le, Nat.le_floor ?_⟩, hpp, h1⟩
            rw [← hz]; exact h2.le
          have hΩ := omega_eq_nu n (by omega) (x ^ c0) (y ^ UU) hallbig hsq
          have hgoodn : n ∈ good := by
            rw [hgood, Finset.mem_filter]; exact ⟨hmem, by rw [hΩ]; exact hnu, hallbig⟩
          rw [if_pos hgoodn]
          calc aK b g N n * tgt n ≤ aK b g N n * W1 := mul_le_mul_of_nonneg_left htgt_le ha0
            _ ≤ W1 * (aK b g N n + ∑ p ∈ Pset, if p ^ 2 ∣ n then aK b g N n else 0) := by nlinarith
      · push Not at hwpos
        have : tgt n ≤ 0 := by rw [htn]; exact hwpos
        have : aK b g N n * tgt n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 this
        linarith
    · have htn : tgt n = 0 := by rw [htgt]; unfold ptarget; rw [if_neg hnu]
      rw [htn, mul_zero]; exact hrhs0
  -- summing (U)
  have hgood_sub : good ⊆ range Xn := by
    intro n hn
    rw [hgood, Finset.mem_filter] at hn
    obtain ⟨-, hhi, -, -⟩ := mem_kpiStar hn.1
    exact Finset.mem_range.2 hhi
  have hUsum : ∑ n ∈ range Xn, aK b g N n * tgt n ≤
      W1 * ((#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ)) + SqK b g N c0 c1) := by
    refine le_trans (Finset.sum_le_sum hup) ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ hW1.le
    apply add_le_add
    · rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hgood_sub]
      calc ∑ n ∈ good, aK b g N n ≤ ∑ n ∈ good, (1 / 2 : ℝ) ^ mK N / (WK b N : ℝ) :=
            Finset.sum_le_sum (fun n _ => (haW n).2.1)
        _ = (#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    · rw [Finset.sum_comm]
      unfold SqK
      apply le_of_eq
      apply Finset.sum_congr rfl; intro p _
      rw [hAW]
  -- assembling
  have hlowS : XK b g N * MTs b B ε y - Kp * levelSumK b g N ⌊y⌋₊ ≤ ∑ n ∈ range Xn, aK b g N n * tgt n := by
    have := Finset.sum_le_sum hpt
    rw [hexch, hsplit] at this
    linarith
  have hXW := hX N hNX
  have hMTy := hMT y hyM
  have hlev := hNL N hNL'
  have hsqb := hNQ N hNQ'
  have hLbig := hNLx N hNLx'
  rw [hLy] at hMTy
  have hMTpos : cM / (thS * L) ≤ MTs b B ε y := hMTy
  have hcMpos : 0 < cM / (thS * L) := by positivity
  have hXMT : cX * (cM / (thS * L)) ≤ XK b g N * MTs b B ε y := by
    apply mul_le_mul hXW hMTpos hcMpos.le (le_trans hcX.le hXW)
  have hLv : levelSumK b g N ⌊y⌋₊ ≤ 1 / L ^ 2 := hlev
  have hSq : SqK b g N c0 c1 ≤ 1 / L ^ 2 := hsqb
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have key : (#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ)) ≥ (cX * cM / (thS * L) - Kp / L ^ 2) / W1 - 1 / L ^ 2 := by
    have h1 : cX * cM / (thS * L) - Kp / L ^ 2 ≤ W1 * ((#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ)) + SqK b g N c0 c1) := by
      have : Kp * levelSumK b g N ⌊y⌋₊ ≤ Kp / L ^ 2 := by
        calc Kp * levelSumK b g N ⌊y⌋₊ ≤ Kp * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hLv hKp0
          _ = Kp / L ^ 2 := by ring
      have e : cX * cM / (thS * L) = cX * (cM / (thS * L)) := by ring
      linarith
    rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hW1]
    nlinarith
  -- the final inequality
  have hW0 : (0 : ℝ) < (WK b N : ℝ) := by unfold WK; positivity
  have h3 : (0 : ℝ) < (1 / 2) ^ mK N / (WK b N : ℝ) := by positivity
  have hLbig' : 4 * (Kp / W1 + 1) / c₀' ≤ L := by linarith
  have habs : (Kp / W1 + 1) / L ^ 2 ≤ c₀' / (4 * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := (div_le_iff₀ hc₀'0).1 hLbig'
    nlinarith
  have hmain : c₀' / (3 * L) ≤ (#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ)) := by
    have e1 : (cX * cM / (thS * L) - Kp / L ^ 2) / W1 - 1 / L ^ 2 = c₀' / L - (Kp / W1 + 1) / L ^ 2 := by
      rw [hc₀']; field_simp; ring
    rw [e1] at key
    have : c₀' / (3 * L) ≤ c₀' / L - c₀' / (4 * L) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hpow : (2 : ℝ) ^ mK N * (1 / 2) ^ mK N = 1 := by
    rw [← mul_pow]; norm_num
  calc c₀' / 3 * (2 : ℝ) ^ mK N * (WK b N : ℝ) / L
        = ((2 : ℝ) ^ mK N * (WK b N : ℝ)) * (c₀' / (3 * L)) := by field_simp
    _ ≤ ((2 : ℝ) ^ mK N * (WK b N : ℝ)) * ((#good : ℝ) * ((1 / 2) ^ mK N / (WK b N : ℝ))) := by gcongr
    _ = #good := by
        field_simp
        rw [mul_comm ((2 : ℝ) ^ mK N), mul_assoc, ← mul_pow]; norm_num

/-- `MainCountK` from the items. -/
theorem mainCountK_of (H : AllItemsK) : MainCountK := fun b hb => count_lowerK H b hb

/-- `MainTheoremK` from `MainCountK`. -/
theorem mainTheoremK_of_count (h : MainCountK) : MainTheoremK := by
  intro b hb
  classical
  obtain ⟨c, hc, N₀, hN⟩ := h b hb
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  set N := max N₀ (M + 1) with hNdef
  have hcount := hN N (le_max_left _ _)
  have hx1 : 1 < xx b N := one_lt_xx b N (by omega)
  have hL : 0 < Real.log (xx b N) := Real.log_pos hx1
  have hW0 : (0 : ℝ) < (WK b N : ℝ) := by
    unfold WK; exact_mod_cast pow_pos (by omega : 0 < b) _
  have hpos : (0 : ℝ) < (#((kpiStar b N).filter (fun n => Ω n ≤ 2 ∧ ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ) :=
    lt_of_lt_of_le (by positivity) hcount
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnP, hn2, -⟩ := hn
  obtain ⟨h1, -, hpal, -⟩ := mem_kpiStar hnP
  have hn0 : n ≠ 0 := by
    have : 1 ≤ b ^ (2 * N) := Nat.one_le_pow _ _ (by omega)
    omega
  have hle : n ≤ M := hM ⟨hpal, hn0, hn2⟩
  have hlt : M < b ^ (2 * N) := by
    calc M < N := by omega
      _ < 2 ^ N := Nat.lt_two_pow_self
      _ ≤ b ^ N := Nat.pow_le_pow_left (by omega) _
      _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Skeleton K.** All items imply Ω ≤ 2 for κ-palindromes (κ = 7/10) in every base `b ≥ 3`, in the infinitude and
in the counting form. -/
theorem skeletonK : AllItemsK → MainTheoremK ∧ MainCountK := fun H =>
  ⟨mainTheoremK_of_count (mainCountK_of H), mainCountK_of H⟩

end KappaOmega2
