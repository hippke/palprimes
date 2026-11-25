import KappaOmega2.SkelSieve
import Palprimes.MainTerm.VB
import Palprimes.E1.Mertens

/-!
# Skeleton, part 3: the main term

`mainterm_lower`: for band data with the S10 bounds there is `ε ∈ (0, 1]` and `c > 0` with
`Σ_{n ∣ P(z)} c_{y,ε}(n) γ(n)/n ≥ c / log y` for large `y`.
Chain: M01 (identity), M02 (Lemma A part 2) with S10's `c_η ≤ c_i` and S14, M03 (F5), M04 (band cost), M05 (`M₂₃ = O(V)`),
Lemma 6 = M06 + M07 + M08 + M09 + M10 + M11, `𝓜(W) ≥ 0.0098` (M12, M13), Mertens (`Palprimes.MT.VB_log`).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

theorem cEta_nil : cEta [] = 1 := by simp [cEta, StepFn.eval_nil]

theorem cOf_nonband (B : BandData) (y : ℝ) (δ : ℕ) (h : ¬ ∃ i, inBand B y i δ) : cOf B y δ = 1 := by
  classical
  unfold cOf; rw [dif_neg h]

theorem GS_pos (b : ℕ) (z : ℝ) (hz : 1 < z) : 0 < GS b z := by
  classical
  unfold GS
  have h1 : 1 ∈ ltSet z := by
    unfold ltSet
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, le_rfl, by exact_mod_cast hz⟩
    exact Nat.lt_ceil.2 (by exact_mod_cast hz)
  have hg1 : gS b 1 = 1 := by simp [gS]
  have hnn : ∀ n ∈ ltSet z, 0 ≤ gS b n := by
    intro n _; unfold gS; split_ifs <;> positivity
  calc (0 : ℝ) < gS b 1 := by rw [hg1]; norm_num
    _ ≤ ∑ n ∈ ltSet z, gS b n := Finset.single_le_sum hnn h1

/-- `V(y) ≥ κ/(2 log y)` for large `y` (Mertens, `Palprimes.MT.VB_log`). -/
theorem VB_lower (b : ℕ) (hb : 2 ≤ b) : ∃ κ : ℝ, 0 < κ ∧ ∃ Y : ℝ, 1 < Y ∧ ∀ y ≥ Y,
    κ / (2 * Real.log y) ≤ MT.VB b y := by
  obtain ⟨C, hC0, hC⟩ := MT.VB_log b hb
  set κ := MT.kappaB b
  have hκ : 0 < κ := MT.kappaB_pos b
  refine ⟨κ, hκ, max ((bigB b : ℝ) + 4) (Real.exp (2 * C / κ + 1)), ?_, fun y hy => ?_⟩
  · have : (1 : ℝ) < (bigB b : ℝ) + 4 := by have := (Nat.cast_nonneg (bigB b) : (0 : ℝ) ≤ _); linarith
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hy1 : (bigB b : ℝ) + 4 ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : Real.exp (2 * C / κ + 1) ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy2
  have hly : 2 * C / κ + 1 ≤ Real.log y := by
    rw [← Real.log_exp (2 * C / κ + 1)]; exact Real.log_le_log (Real.exp_pos _) hy2
  have hlpos : 0 < Real.log y := by have : 0 ≤ 2 * C / κ := by positivity
                                    linarith
  have h := hC y hy1
  have hCl : C / Real.log y ≤ κ / 2 := by
    rw [div_le_iff₀ hlpos]
    have := (div_le_iff₀ hκ).1 (show 2 * C / κ ≤ Real.log y by linarith)
    linarith
  have h2 := (abs_le.1 h).1
  have hV : κ / 2 ≤ MT.VB b y * Real.log y := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith

set_option maxHeartbeats 4000000 in
theorem mainterm_lower (hS05 : ItemS05) (hS13 : ItemS13) (hS14 : ItemS14)
    (hM01 : ItemM01) (hM02 : ItemM02) (hM03 : ItemM03) (hM04 : ItemM04) (hM05 : ItemM05) (hM06 : ItemM06)
    (hM07 : ItemM07) (hM08 : ItemM08) (hM09 : ItemM09) (hM10 : ItemM10) (hM11 : ItemM11) (hM12 : ItemM12)
    (hM13 : ItemM13)
    (b : ℕ) (hb : 2 ≤ b) (B : BandData) (hB : BandOK B)
    (hcEta : ∀ i < B.etas.length, cEta (B.etas.getD i []) ≤ (B.cs.getD i 1 : ℝ))
    (hcost : bandCost B ≤ 7 / 1000) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, ∀ y ≥ y₀, c / Real.log y ≤ MTs b B ε y := by
  classical
  -- `𝓜(W) ≥ 0.009`
  obtain ⟨ξ, Hb, hT, hMl⟩ := hM12
  have hmval : (9 / 1000 : ℝ) ≤ mvalW := le_trans hMl (hM13 ξ Hb hT)
  -- constants
  obtain ⟨C₅, y₅, h5⟩ := hM05 b hb
  set C : ℝ := max C₅ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  set eγ : ℝ := Real.exp Real.eulerMascheroniConstant with heγ
  have heγ1 : 1 ≤ eγ := Real.one_le_exp (le_of_lt (lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant))
  set μ₀ : ℝ := 2 / 1000 with hμ₀
  set ε : ℝ := min 1 (eγ * μ₀ / (3 + 7 * C + 14 * eγ)) with hεdef
  have hden : 0 < 3 + 7 * C + 14 * eγ := by positivity
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεb : ε * (3 + 7 * C + 14 * eγ) ≤ eγ * μ₀ := by
    have := min_le_right 1 (eγ * μ₀ / (3 + 7 * C + 14 * eγ))
    rw [← hεdef] at this
    calc ε * (3 + 7 * C + 14 * eγ) ≤ eγ * μ₀ / (3 + 7 * C + 14 * eγ) * (3 + 7 * C + 14 * eγ) :=
          mul_le_mul_of_nonneg_right this hden.le
      _ = eγ * μ₀ := div_mul_cancel₀ _ hden.ne'
  refine ⟨ε, hε0, hε1, ?_⟩
  -- the items at this ε
  set etas : List StepFn := [] :: B.etas with hetas_def
  have hetas : ∀ e ∈ etas, StepOK e := by
    intro e he
    rcases List.mem_cons.1 he with h | h
    · rw [h]; exact stepOK_nil
    · exact hB.2.2.2.2.1 e h
  obtain ⟨x₂, h2⟩ := hM02 b hb etas hetas ε hε0
  obtain ⟨x₃, h3⟩ := hM03 b hb ε hε0
  obtain ⟨y₄, h4⟩ := hM04 b hb B hB ε hε0
  have L7 := hM06 b hb
  have L9 := hM08 b hb L7
  obtain ⟨y₇, h7⟩ := hM07 b hb L7 ε hε0
  obtain ⟨y₁₀, h10⟩ := hM10 b hb L9 hM09 ε hε0
  obtain ⟨y₁₁, h11⟩ := hM11 b hb L7 ε hε0
  obtain ⟨κV, hκV, YV, hYV1, hYV⟩ := VB_lower b hb
  obtain ⟨cD, hcD⟩ : ∃ c : ℝ, c = (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 := ⟨_, rfl⟩
  have hcD0 : 0 < cD := by rw [hcD]; positivity
  set X : ℝ := max (max x₂ x₃) 2 with hX
  have hX2 : 2 ≤ X := le_max_right _ _
  refine ⟨μ₀ * κV / 2, by positivity,
    max (max (max 2 (X ^ (1 / cD))) (max y₄ y₅)) (max (max y₇ y₁₀) (max y₁₁ YV)), fun y hy => ?_⟩
  have hy2 : 2 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hy)
  have hyX' : X ^ (1 / cD) ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hy)
  have hy4 : y₄ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hy)
  have hy5 : y₅ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hy)
  have hy7 : y₇ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hy)
  have hy10 : y₁₀ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hy)
  have hy11 : y₁₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hy)
  have hyV : YV ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hy)
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  have hyX : X ≤ y ^ cD := by
    have h2' : (X ^ (1 / cD)) ^ cD ≤ y ^ cD := Real.rpow_le_rpow (by positivity) hyX' hcD0.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hcD0.ne', Real.rpow_one] at h2'
  set V : ℝ := MT.VB b y with hV
  have hVpos : 0 < V := E1.VB_pos' b y
  obtain ⟨-, -, -, -, -, hDφ, -⟩ := hS05 y hy1
  -- the bound for each quadratic form
  set D := Dset y (y ^ UU) mm with hD
  have hQ : ∀ δ ∈ D, phiW W1 (wy y) δ * rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ) ≤
      (1 + ε) * (phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1)) +
        (1 + ε) * (1 + ε) * (phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ))) := by
    intro δ hδ
    obtain ⟨hδsq, -, -, hδlev⟩ := hS13 y hy1 δ hδ
    rw [← hcD] at hδlev
    have hδ0 : δ ≠ 0 := hδsq.ne_zero
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
    have hφ0 : 0 ≤ phiW W1 (wy y) δ := (hDφ δ hδ).1
    have hρ0 : 0 ≤ rhoB b δ := by unfold rhoB; split_ifs <;> norm_num
    have hcoef : 0 ≤ phiW W1 (wy y) δ * rhoB b δ / δ := by positivity
    have hxX : X ≤ y / δ := le_trans hyX hδlev
    have hx2 : x₂ ≤ y / δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxX
    have hx3 : x₃ ≤ y / δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxX
    have hsq1 : 1 < Real.sqrt (y / δ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hG := GS_pos b _ hsq1
    have hmem := etaOf_mem hS14 B hB y hy1 δ
    have hQ2 := h2 (y / δ) hx2 (etaOf B y δ) hmem
    have hQ3 := h3 (y / δ) hx3
    -- `c_η ≤ c_δ` and `c_δ ≥ 1`
    have hcη : cEta (etaOf B y δ) ≤ cOf B y δ ∧ 1 ≤ cOf B y δ := by
      by_cases hband : ∃ i, inBand B y i δ
      · obtain ⟨i, hi⟩ := hband
        obtain ⟨heta, hc, -, hc1, -⟩ := hS14 B hB y hy1 i δ hi
        refine ⟨?_, hc1⟩
        rw [heta, hc]; exact hcEta i hi.2.1
      · rw [etaOf_nonband B y δ hband, cOf_nonband B y δ hband, cEta_nil]; exact ⟨le_rfl, le_rfl⟩
    have hVδ : 0 < MT.VB b (Real.sqrt (y / δ)) := E1.VB_pos' b _
    have hQle : Qform b (y / δ) (LamD b B y δ) ≤ (cOf B y δ + ε) * ((1 + ε) * eγ * MT.VB b (Real.sqrt (y / δ))) := by
      calc Qform b (y / δ) (LamD b B y δ) ≤ (cEta (etaOf B y δ) + ε) / GS b (Real.sqrt (y / δ)) := hQ2
        _ ≤ (cOf B y δ + ε) / GS b (Real.sqrt (y / δ)) := by gcongr; exact hcη.1
        _ = (cOf B y δ + ε) * (1 / GS b (Real.sqrt (y / δ))) := by ring
        _ ≤ (cOf B y δ + ε) * ((1 + ε) * eγ * MT.VB b (Real.sqrt (y / δ))) := by
            gcongr
            · linarith [hcη.2]
    calc phiW W1 (wy y) δ * rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ)
        ≤ phiW W1 (wy y) δ * rhoB b δ / δ * ((cOf B y δ + ε) * ((1 + ε) * eγ * MT.VB b (Real.sqrt (y / δ)))) :=
          mul_le_mul_of_nonneg_left hQle hcoef
      _ = _ := by ring
  have hsumQ : ∑ δ ∈ D, phiW W1 (wy y) δ * rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ) ≤
      (1 + ε) * (∑ δ ∈ D, phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1)) +
        (1 + ε) * (1 + ε) * M23 b y := by
    calc _ ≤ ∑ δ ∈ D, ((1 + ε) * (phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1)) +
          (1 + ε) * (1 + ε) * (phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ)))) :=
          Finset.sum_le_sum hQ
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
  -- `M₂₃ ≥ 0` and `≤ C V`
  have hM23nn : 0 ≤ M23 b y := by
    unfold M23
    refine Finset.sum_nonneg (fun δ hδ => ?_)
    have hφ0 : 0 ≤ phiW W1 (wy y) δ := (hDφ δ hδ).1
    have hρ0 : 0 ≤ rhoB b δ := by unfold rhoB; split_ifs <;> norm_num
    have := E1.VB_pos' b (Real.sqrt (y / δ))
    positivity
  have hM23C : M23 b y ≤ C * V := le_trans (h5 y hy5) (mul_le_mul_of_nonneg_right (le_max_left _ _) hVpos.le)
  have hBand := h4 y hy4
  -- Lemma 6
  have e7 := h7 y hy7
  have e10 := h10 y hy10
  have e11 := h11 y hy11
  have hL6 : 2 * eγ * V * mvalW - 3 * ε * V ≤ M1 b y - M23 b y := by
    have a1 := (abs_le.1 e7).1
    have a2 := (abs_le.1 e10).1
    have a3 := (abs_le.1 e11).1
    linarith
  -- the main term
  have hMT := hM01 b B ε y hb hy1
  set Bs := ∑ δ ∈ D, phiW W1 (wy y) δ * rhoB b δ / δ * eγ * MT.VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1) with hBs
  set S := ∑ δ ∈ D, phiW W1 (wy y) δ * rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ) with hSdef
  have h1e : 0 ≤ 1 + ε := by linarith
  have hA1 : (1 + ε) * S ≤ (1 + ε) ^ 2 * Bs + (1 + ε) ^ 3 * M23 b y := by
    have := mul_le_mul_of_nonneg_left hsumQ h1e
    have e : (1 + ε) * ((1 + ε) * Bs + (1 + ε) * (1 + ε) * M23 b y) = (1 + ε) ^ 2 * Bs + (1 + ε) ^ 3 * M23 b y := by ring
    linarith
  have h2eV : 0 ≤ 2 * eγ * V := by positivity
  have hA2 : (1 + ε) ^ 2 * Bs ≤ 2 * eγ * V * (bandCost B + 7 * ε) := by
    have s1 : (1 + ε) ^ 2 * Bs ≤ (1 + ε) ^ 2 * (2 * eγ * V * (bandCost B + ε)) :=
      mul_le_mul_of_nonneg_left hBand (by positivity)
    have s2 : (1 + ε) ^ 2 * (bandCost B + ε) ≤ bandCost B + 7 * ε := by
      have t1 : (2 * ε + ε ^ 2) * bandCost B ≤ (2 * ε + ε ^ 2) * (7 / 1000) :=
        mul_le_mul_of_nonneg_left hcost (by positivity)
      have t2 : (2 * ε + ε ^ 2) * (7 / 1000) ≤ 3 * ε := by nlinarith
      have t3 : (1 + ε) ^ 2 * ε ≤ 4 * ε := by nlinarith
      have e : (1 + ε) ^ 2 * (bandCost B + ε) = bandCost B + (2 * ε + ε ^ 2) * bandCost B + (1 + ε) ^ 2 * ε := by ring
      linarith
    have s3 := mul_le_mul_of_nonneg_left s2 h2eV
    nlinarith
  have hA3 : (1 + ε) ^ 3 * M23 b y ≤ M23 b y + 7 * ε * (C * V) := by
    have t1 : (1 + ε) ^ 3 - 1 ≤ 7 * ε := by
      have e : (1 + ε) ^ 3 - 1 = ε * (3 + 3 * ε + ε ^ 2) := by ring
      have f : 3 + 3 * ε + ε ^ 2 ≤ 7 := by nlinarith
      rw [e]; nlinarith
    have t2 : ((1 + ε) ^ 3 - 1) * M23 b y ≤ 7 * ε * M23 b y := mul_le_mul_of_nonneg_right t1 hM23nn
    have t3 : 7 * ε * M23 b y ≤ 7 * ε * (C * V) := mul_le_mul_of_nonneg_left hM23C (by positivity)
    nlinarith
  have hB1 : 2 * eγ * V * (9 / 1000) ≤ 2 * eγ * V * mvalW := mul_le_mul_of_nonneg_left hmval h2eV
  have hB2 : 2 * eγ * V * bandCost B ≤ 2 * eγ * V * (7 / 1000) := mul_le_mul_of_nonneg_left hcost h2eV
  have hB3 : ε * (3 + 7 * C + 14 * eγ) * V ≤ eγ * μ₀ * V := mul_le_mul_of_nonneg_right hεb hVpos.le
  have hMTlow : μ₀ * eγ * V ≤ MTs b B ε y := by
    rw [hMT]
    have : M1 b y - (1 + ε) * S ≥ 2 * eγ * V * mvalW - 3 * ε * V - 7 * ε * (C * V) -
        2 * eγ * V * (bandCost B + 7 * ε) := by linarith
    rw [hμ₀] at hB3 ⊢
    nlinarith
  obtain hVl := hYV y hyV
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  calc μ₀ * κV / 2 / Real.log y = μ₀ * (κV / (2 * Real.log y)) := by field_simp
    _ ≤ μ₀ * V := mul_le_mul_of_nonneg_left hVl (by norm_num [hμ₀])
    _ ≤ μ₀ * eγ * V := by
        have : 0 ≤ μ₀ * V := by positivity
        nlinarith
    _ ≤ MTs b B ε y := hMTlow

end KappaOmega2
