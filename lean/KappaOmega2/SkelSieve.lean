import KappaOmega2.Statements

/-!
# Skeleton, part 2: the pointwise sieve inequality

`pointwise`: for every `ε ∈ (0, 1]` and `y` large, every integer `2 ≤ a < y^{1/θ}` satisfies
`Σ_{n ∣ a} c_{y,ε}(n) ≤ [ν_{y,U}(a) ≤ 3] w(p(a))`.
Chain: S12 (expansion) → S06 with the admissibility (S07 outside the bands, S10's allowance inside, S08 for
`λ₁ + λ_q`, S09 for `λ₁ = 1` and the support, S13, S14) → S04 → S03 → S02 → S01, with S05 and S15 for the
side conditions.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

theorem StepFn.eval_nil (u : ℝ) : StepFn.eval [] u = 0 := by simp [StepFn.eval]

theorem Ahat_nil (s : ℝ) : Ahat [] s = 0 := by simp [Ahat, StepFn.eval_nil]

theorem gEta_nil (u : ℝ) : gEta [] u = u := by
  simp only [gEta, Ahat_nil, StepFn.eval_nil]; ring

theorem stepOK_nil : StepOK [] := by simp [StepOK]

theorem etaOf_mem (hS14 : ItemS14) (B : BandData) (hB : BandOK B) (y : ℝ) (hy : 1 < y) (δ : ℕ) :
    etaOf B y δ ∈ ([] :: B.etas) := by
  classical
  by_cases h : ∃ i, inBand B y i δ
  · obtain ⟨i, hi⟩ := h
    have := (hS14 B hB y hy i δ hi)
    rw [this.1]; exact List.mem_cons_of_mem _ this.2.2.1
  · unfold etaOf; rw [dif_neg h]; exact List.mem_cons_self

theorem etaOf_nonband (B : BandData) (y : ℝ) (δ : ℕ) (h : ¬ ∃ i, inBand B y i δ) : etaOf B y δ = [] := by
  classical
  unfold etaOf; rw [dif_neg h]

/-- `log √(y/δ) = (log y − log δ)/2`. -/
theorem log_sqrt_div (y δ : ℝ) (hy : 0 < y) (hδ : 0 < δ) :
    Real.log (Real.sqrt (y / δ)) = (Real.log y - Real.log δ) / 2 := by
  rw [Real.log_sqrt (by positivity), Real.log_div hy.ne' hδ.ne']

theorem Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf mm kSq UU W1
  split_ifs with h1 h2 h3
  · exact le_rfl
  · push Not at h1; exact le_min (by positivity) (by linarith)
  · push Not at h1; linarith
  · norm_num

set_option maxHeartbeats 4000000 in
theorem pointwise (hS01 : ItemS01) (hS02 : ItemS02) (hS03 : ItemS03) (hS04 : ItemS04) (hS05 : ItemS05)
    (hS06 : ItemS06) (hS07 : ItemS07) (hS08 : ItemS08) (hS09 : ItemS09) (hS12 : ItemS12) (hS13 : ItemS13)
    (hS14 : ItemS14) (hS15 : ItemS15)
    (b : ℕ) (hb : 2 ≤ b) (B : BandData) (hB : BandOK B) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hallow : BandAllow B ε₀)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ a : ℕ, 2 ≤ a → (a : ℝ) < y ^ (1 / thS) →
      ∑ n ∈ a.divisors, cSieve b B ε y n ≤ ptarget y UU (wy y) a := by
  classical
  set etas : List StepFn := [] :: B.etas with hetas_def
  have hetas : ∀ e ∈ etas, StepOK e := by
    intro e he
    rcases List.mem_cons.1 he with h | h
    · rw [h]; exact stepOK_nil
    · exact hB.2.2.2.2.1 e h
  have hmm : (0 : ℝ) < mm := by norm_num [mm]
  obtain ⟨C, x₁, hA1⟩ := hS09 b hb etas hetas
  set ε₈ : ℝ := min ε₀ (mm * ε / 4) with hε₈
  have hε₈0 : 0 < ε₈ := lt_min hε₀ (by positivity)
  obtain ⟨x₂, h8⟩ := hS08 b hb etas hetas mm ε₈ hmm hε₈0
  obtain ⟨cD, hcD⟩ : ∃ c : ℝ, c = (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 := ⟨_, rfl⟩
  have hcD0 : 0 < cD := by rw [hcD]; positivity
  set X : ℝ := max (max x₁ x₂) 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  refine ⟨max 2 (X ^ (1 / cD)), fun y hy a ha hax => ?_⟩
  have hy2 : 2 ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hyX : X ≤ y ^ cD := by
    have h1 : X ^ (1 / cD) ≤ y := le_trans (le_max_right _ _) hy
    have h2 : (X ^ (1 / cD)) ^ cD ≤ y ^ cD := Real.rpow_le_rpow (by positivity) h1 hcD0.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hcD0.ne', Real.rpow_one] at h2
  set z : ℝ := y ^ UU with hz
  obtain ⟨hw0, hwle, hwU, hwzero, hwlin, hDφ, hD4⟩ := hS05 y hy1
  set w : ℕ → ℝ := wy y with hw
  have ha1 : 1 ≤ a := by omega
  obtain ⟨hAsq, hAprimes, hAdvdP, hAdvda, hAidem, hdvd_iff⟩ := hS15 a z ha1
  set A : ℕ := radLt a z with hA
  have hA0 : A ≠ 0 := hAsq.ne_zero
  -- facts on `𝒟`
  have hDfacts := hS13 y hy1
  -- the per-δ Lemma 3 inequality
  have hLam : ∀ δ ∈ (Dset y z mm).filter (· ∣ A),
      LamA (radLt (A / δ) (Real.sqrt (y / δ))) (phiW W1 w δ) w ≤
        (1 + ε) * (phiW W1 w δ * (∑ d ∈ (A / δ).divisors, LamD b B y δ d) ^ 2) := by
    intro δ hδ
    rw [Finset.mem_filter] at hδ
    obtain ⟨hδD, hδA⟩ := hδ
    obtain ⟨hδsq, hδprimes, hδmin, hδlev⟩ := hDfacts δ hδD
    rw [← hcD] at hδlev
    have hδ0 : δ ≠ 0 := hδsq.ne_zero
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
    have hφ0 : 0 ≤ phiW W1 w δ := (hDφ δ hδD).1
    -- the level `y/δ` is large
    have hyδX : X ≤ y / δ := le_trans hyX hδlev
    have hyδ1 : 1 ≤ y / δ := le_trans hX1 hyδX
    have hyδx₁ : x₁ ≤ y / δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hyδX
    have hyδx₂ : x₂ ≤ y / δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hyδX
    have hyδ_gt : 1 < y / δ := by
      have : (1 : ℝ) < y ^ cD := Real.one_lt_rpow hy1 hcD0
      linarith [hδlev]
    have hmem := etaOf_mem hS14 B hB y hy1 δ
    obtain ⟨hlam1, -, hsupp⟩ := hA1 (y / δ) hyδx₁ (etaOf B y δ) hmem
    have hM1 : 1 ≤ A / δ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hδA) (Nat.pos_of_ne_zero hδ0)
    have hlogyδ : 0 < Real.log (y / δ) := Real.log_pos hyδ_gt
    have hlogδ : Real.log δ = Real.log y - Real.log (y / δ) := by
      rw [Real.log_div hy0.ne' hδpos.ne']; ring
    have hlogyδ_le : Real.log (y / δ) ≤ Real.log y := by
      have : 0 ≤ Real.log δ := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hδ0)
      linarith
    refine le_trans (hS06 (Real.sqrt (y / δ)) (phiW W1 w δ) (1 + ε) w (LamD b B y δ) (A / δ) hφ0
      (by linarith) hlam1 (fun d hd => ⟨(hsupp d hd).1, (hsupp d hd).2.2⟩) ?_ hM1) (le_of_eq (by ring))
    -- the condition on primes `q < √(y/δ)`
    intro q hq hqz
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
    have hq0 : (0 : ℝ) < q := by linarith
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    have hsq : (q : ℝ) ^ 2 * δ < y := by
      have h1 : (q : ℝ) ^ 2 < y / δ := by
        have := Real.sqrt_nonneg (y / δ)
        have h2 : (q : ℝ) ^ 2 < Real.sqrt (y / δ) ^ 2 := by gcongr
        rwa [Real.sq_sqrt (by linarith)] at h2
      rwa [lt_div_iff₀ hδpos] at h1
    have hlq : 2 * Real.log q < Real.log (y / δ) := by
      have h1 : (q : ℝ) ^ 2 < y / δ := by rw [lt_div_iff₀ hδpos]; exact hsq
      have := Real.log_lt_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hK0 : 0 ≤ (1 + ε) * phiW W1 w δ * (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by positivity
    by_cases hwq : w q = 0
    · rw [hwq]; exact hK0
    have hwq0 : 0 < w q := lt_of_le_of_ne (hw0 q) (Ne.symm hwq)
    -- `t = log q / log y > m`
    set t : ℝ := Real.log q / Real.log y with ht
    have htm : mm < t := by
      by_contra hle
      push Not at hle
      have hqm : (q : ℝ) ≤ y ^ mm := by
        have h1 : Real.log q ≤ mm * Real.log y := by rw [ht, div_le_iff₀ hlogy] at hle; linarith
        rw [Real.rpow_def_of_pos hy0, ← Real.exp_log hq0]
        exact Real.exp_le_exp.2 (by linarith)
      exact hwq (hwzero q hq hqm)
    have hqlow : (y / δ) ^ mm ≤ (q : ℝ) := by
      have h1 : mm * Real.log (y / δ) ≤ Real.log q := by
        have : mm * Real.log y < Real.log q := by rw [ht, lt_div_iff₀ hlogy] at htm; linarith
        nlinarith
      rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_log hq0]
      exact Real.exp_le_exp.2 (by linarith)
    -- `u = log q / log √(y/δ)`
    have hu : Real.log q / Real.log (Real.sqrt (y / δ)) = 2 * Real.log q / Real.log (y / δ) := by
      rw [Real.log_sqrt (by linarith)]; field_simp
    have hS8 : |LamD b B y δ 1 + LamD b B y δ q - gEta (etaOf B y δ) (2 * Real.log q / Real.log (y / δ))| ≤ ε₈ := by
      have := h8 (y / δ) hyδx₂ (etaOf B y δ) hmem q hq hqlow hqz
      rw [hu] at this; exact this
    have hwq' : w q = Wf t := by simp only [hw, wy, ht]
    by_cases hband : ∃ i, inBand B y i δ
    · -- band prime
      obtain ⟨i, hi⟩ := hband
      obtain ⟨heta, -, -, -, hxi, hxi1, hφ⟩ := hS14 B hB y hy1 i δ hi
      set x : ℝ := Real.log δ / Real.log y with hx
      have hi_lt : i < B.etas.length := hi.2.1
      have key : 2 * t - (1 - x) = (2 * Real.log q - Real.log (y / δ)) / Real.log y := by
        rw [ht, hx, hlogδ]; field_simp; ring
      have h2t : 2 * t < 1 - x := by
        have : (2 * Real.log q - Real.log (y / δ)) / Real.log y < 0 := div_neg_of_neg_of_pos (by linarith) hlogy
        linarith
      obtain ⟨hgpos, hWt⟩ := hallow i hi_lt x t hxi hxi1 htm h2t
      have hux : 2 * Real.log q / Real.log (y / δ) = 2 * t / (1 - x) := by
        have h1x : (1 - x) * Real.log y = Real.log (y / δ) := by
          rw [hx, sub_mul, div_mul_cancel₀ _ hlogy.ne', one_mul, hlogδ]; ring
        rw [ht, ← h1x]; field_simp
      rw [hux, heta] at hS8
      set g := gEta (B.etas.getD i []) (2 * t / (1 - x)) with hg
      have hε8 : ε₈ ≤ ε₀ := min_le_left _ _
      have hlow : g - ε₀ ≤ LamD b B y δ 1 + LamD b B y δ q := by
        have := (abs_le.1 hS8).1; linarith
      have hsq2 : (g - ε₀) ^ 2 ≤ (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by
        have h0 : 0 ≤ g - ε₀ := by linarith
        nlinarith
      rw [hwq']
      have hUx : 0 ≤ UU - x := by rw [← hφ]; exact hφ0
      calc Wf t ≤ (1 - ε₀) * (UU - x) * (g - ε₀) ^ 2 := hWt
        _ ≤ (UU - x) * (g - ε₀) ^ 2 := by
            have : 0 ≤ (UU - x) * (g - ε₀) ^ 2 := by positivity
            nlinarith
        _ ≤ (UU - x) * (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by gcongr
        _ ≤ (1 + ε) * phiW W1 w δ * (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by
            rw [hφ]
            have : 0 ≤ (UU - x) * (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by positivity
            nlinarith
    · -- Greaves' weights (outside the bands)
      have h7 := hS07 B hB y δ q hy1 hδD hband hq hsq
      rw [etaOf_nonband B y δ hband, gEta_nil] at hS8
      set u : ℝ := 2 * Real.log q / Real.log (y / δ) with hu_def
      have hu2 : 2 * mm ≤ u := by
        have h1 : mm * Real.log y < Real.log q := by rw [ht, lt_div_iff₀ hlogy] at htm; linarith
        rw [hu_def, le_div_iff₀ hlogyδ]; nlinarith
      have hε8 : ε₈ ≤ mm * ε / 4 := min_le_right _ _
      have hlow : u * (1 - ε / 8) ≤ LamD b B y δ 1 + LamD b B y δ q := by
        have := (abs_le.1 hS8).1
        have : mm * ε / 4 ≤ u * ε / 8 := by nlinarith
        nlinarith
      have hlow0 : 0 ≤ u * (1 - ε / 8) := by
        have : 0 ≤ u := by linarith
        have : 0 ≤ 1 - ε / 8 := by linarith
        positivity
      have hsq2 : (u * (1 - ε / 8)) ^ 2 ≤ (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by nlinarith
      have hfac : 1 ≤ (1 + ε) * (1 - ε / 8) ^ 2 := by
        have e1 : (1 + ε) * (1 - ε / 8) ^ 2 - 1 = ε * (3 / 4 - 15 * ε / 64 + ε ^ 2 / 64) := by ring
        have e2 : 0 < 3 / 4 - 15 * ε / 64 + ε ^ 2 / 64 := by nlinarith [sq_nonneg ε]
        have := mul_pos hε e2
        linarith
      calc w q ≤ phiW W1 w δ * u ^ 2 := h7
        _ ≤ phiW W1 w δ * ((1 + ε) * (1 - ε / 8) ^ 2 * u ^ 2) := by
            have : 0 ≤ u ^ 2 := sq_nonneg u
            have : u ^ 2 ≤ (1 + ε) * (1 - ε / 8) ^ 2 * u ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_left this hφ0
        _ = (1 + ε) * phiW W1 w δ * (u * (1 - ε / 8)) ^ 2 := by ring
        _ ≤ (1 + ε) * phiW W1 w δ * (LamD b B y δ 1 + LamD b B y δ q) ^ 2 := by
            have : 0 ≤ (1 + ε) * phiW W1 w δ := by positivity
            exact mul_le_mul_of_nonneg_left hsq2 this
  -- the chain
  have hexp := hS12 b B ε y a hb hy1 ha1
  have hsumLam : ∑ δ ∈ (Dset y z mm).filter (· ∣ A),
      LamA (radLt (A / δ) (Real.sqrt (y / δ))) (phiW W1 w δ) w ≤
        (1 + ε) * ∑ δ ∈ (Dset y z mm).filter (· ∣ A), phiW W1 w δ * (∑ d ∈ (A / δ).divisors, LamD b B y δ d) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hLam
  have hz_le : z ≤ y := by
    rw [hz]; calc y ^ UU ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num [UU])
      _ = y := Real.rpow_one y
  have hprimesA : ∀ p ∈ A.primeFactors, (p : ℝ) < z := fun p hp => (hAprimes p hp).1
  have h4 := hS04 y z mm W1 w A hmm hy1 hAsq hprimesA hw0 (fun δ hδ _ => hDφ δ hδ)
  have h3 := hS03 y z mm W1 w A hmm hy1 hAsq hprimesA hw0 hD4
  have h2 := hS02 y z mm W1 w A hmm (by norm_num [mm]) hy1 hz_le hAsq hprimesA
  have h1 := hS01 y UU mm z (1 / thS) w a hy1 (by norm_num [UU]) (by norm_num [UU]) hmm.le le_rfl
    (by norm_num [thS, mm, UU]) ha hax (fun p _ => hw0 p) (fun p hp => by have := hwle p hp; norm_num [W1, UU, mm] at this ⊢; linarith)
    (fun p hp hpU => by rw [hwU p hp hpU]; norm_num [W1, UU, mm]) hwzero hwlin
  have hW1 : UU - mm = W1 := by norm_num [UU, mm, W1]
  rw [hW1] at h1
  -- `SigmaG y z W1 w A` is `SigmaG y z W1 w (radLt a z)`
  calc ∑ n ∈ a.divisors, cSieve b B ε y n
      = Sig1 y z mm W1 w A - (1 + ε) * ∑ δ ∈ (Dset y z mm).filter (· ∣ A),
          phiW W1 w δ * (∑ d ∈ (A / δ).divisors, LamD b B y δ d) ^ 2 := hexp
    _ ≤ Sig1 y z mm W1 w A - ∑ δ ∈ (Dset y z mm).filter (· ∣ A),
          LamA (radLt (A / δ) (Real.sqrt (y / δ))) (phiW W1 w δ) w := by linarith
    _ ≤ Sig1 y z mm W1 w A + Sig2 y z mm W1 w A + Sig3 y z mm W1 w A := by linarith
    _ ≤ Sig1 y z mm W1 w A + Sig2 y z mm W1 w A + Sig3 y z mm W1 w A + Sig4 y z mm W1 w A := by linarith
    _ = SigmaG y z W1 w A := h2.symm
    _ ≤ ptarget y UU w a := h1

end KappaOmega2
