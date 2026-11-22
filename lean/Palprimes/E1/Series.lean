import Palprimes.E1.Cont

set_option linter.style.longLine false

/-! # E1, phase E7: the limit functions `F_I`, `f_I` (blueprint D1–D3)

Blueprint `lean/e1/E1_BLUEPRINT.md` §5.1.

* D1: `GP s = ∑' k, β⁺_k(s)`, `GM s = ∑' k, β⁻_k(s)` (`β⁻_0 = 0`), `FI = 1 + GP`, `fI = 1 - GM`,
  `AI = 3 FI(3)`, `BI = 2 fI(2)`. The series converge uniformly (`tendstoUniformlyOn_GP` on `s ≥ 1`,
  `tendstoUniformlyOn_GM` on `s ≥ 2`, M-test with `2 A^k`), hence `GP`, `FI` are continuous on `Ici 1` and
  `GM`, `fI` on `Ici 2`; integrable on `Ioi c` (`c ≥ 1`, resp. `c ≥ 2`).
* D2 (integral equations): `mul_GP` (`s G⁺(s) = (3-s)₊ + ∫_{u > max(s-1,2)} G⁻`, `s ≥ 1`),
  `mul_GM` (`s G⁻(s) = ∫_{u > s-1} G⁺`, `s ≥ 2`); sum and integral swapped by
  `integral_tsum_of_summable_integral_norm` with the C.5 majorants.
* D3 (DDE, integral form, `AI`, `BI` symbolic):
  (a) `mul_FI_of_le_three` (`s F_I(s) = A_I`, `1 ≤ s ≤ 3`), `FI_of_le_three`;
  (b) `mul_FI_of_three_le` (`s F_I(s) = A_I + ∫_3^s f_I(u-1)`, `s ≥ 3`);
  (c) `mul_fI` (`s f_I(s) = B_I + ∫_2^s F_I(u-1)`, `s ≥ 2`);
  (d) `mul_fI_of_le_three` (`s f_I(s) = B_I + A_I log(s-1)` on `[2,3]`), `fI_of_le_three`, and
      `mul_FI_sub_mul_fI_of_le_three` (`P(s) = A_I - B_I - A_I log(s-1)` on `[2,3]`, input for D4a);
  (e) decay `abs_FI_sub_one_le`, `abs_fI_sub_one_le`, `decay` (`|F_I - 1| + |f_I - 1| ≤ C e^{-s}`, `s ≥ 2`) and
      `tendsto_pow_mul_FI_sub_one`, `tendsto_pow_mul_fI_sub_one` (`s^n (F_I(s) - 1) → 0`).
* Forms for E9 (D4) and E11 (D6):
  `fIext` (`f_I` on `[2,∞)`, `0` on `(-∞,2)`), `mul_FI_eq_ext` (`s F_I(s) = A_I + ∫_3^s fIext(u-1)` for all
  `s ≥ 1`, the shape of `Fjr_dde`), `continuousOn_fIext` (given `B_I = 0`, on `Ici 1`), derivatives
  `hasDerivAt_mul_FI_of_three_lt` (`(sF_I)' = f_I(s-1)`, `s > 3`), `hasDerivAt_mul_FI_of_lt_three`
  (`= 0` on `(1,3)`), `hasDerivAt_mul_FI_ext` (`= fIext(s-1)`, `s > 1`, `s ≠ 3`),
  `hasDerivAt_mul_fI` (`(sf_I)' = F_I(s-1)`, `s > 2`).
-/

open MeasureTheory Set Real Filter Topology

namespace Palprimes.E1

/-! ## Definitions (D1) -/

/-- `G⁺(s) = ∑_{k ≥ 0} β⁺_k(s)` (meaningful for `s ≥ 1`). -/
noncomputable def GP (s : ℝ) : ℝ := ∑' k, betaP k s

/-- `G⁻(s) = ∑_{k ≥ 1} β⁻_k(s)` (written over all `k`, `β⁻_0 = 0`; meaningful for `s ≥ 2`). -/
noncomputable def GM (s : ℝ) : ℝ := ∑' k, betaM k s

/-- `F_I = 1 + ∑' β⁺_k`. -/
noncomputable def FI (s : ℝ) : ℝ := 1 + GP s

/-- `f_I = 1 - ∑' β⁻_k`. -/
noncomputable def fI (s : ℝ) : ℝ := 1 - GM s

/-- `A_I = 3 F_I(3)`. -/
noncomputable def AI : ℝ := 3 * FI 3

/-- `B_I = 2 f_I(2)`. -/
noncomputable def BI : ℝ := 2 * fI 2

/-- `f_I` extended by `0` below `2` (used in D4b once `B_I = 0`, and in the `Fjr_dde` shape). -/
noncomputable def fIext (s : ℝ) : ℝ := if 2 ≤ s then fI s else 0

theorem FI_def (s : ℝ) : FI s = 1 + ∑' k, betaP k s := rfl

theorem fI_def (s : ℝ) : fI s = 1 - ∑' k, betaM k s := rfl

theorem fIext_of_two_le {s : ℝ} (hs : 2 ≤ s) : fIext s = fI s := by simp [fIext, hs]

theorem fIext_of_lt_two {s : ℝ} (hs : s < 2) : fIext s = 0 := by simp [fIext, not_le.mpr hs]

theorem GM_eq_tsum_succ (s : ℝ) : GM s = ∑' k, betaM (k + 1) s := by
  rw [GM]
  refine (Function.Injective.tsum_eq (g := Nat.succ) Nat.succ_injective (f := fun k => betaM k s) ?_).symm
  intro k hk
  cases k with
  | zero => exact absurd (betaM_zero s) hk
  | succ k => exact ⟨k, rfl⟩

theorem GP_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ GP s := tsum_nonneg fun k => betaP_nonneg k hs

theorem GM_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ GM s := tsum_nonneg fun k => betaM_nonneg k hs

theorem GP_le {s : ℝ} (hs : 1 ≤ s) : GP s ≤ c0 * mPlus s / (1 - rateA) := tsum_betaP_le hs

theorem GM_le {s : ℝ} (hs : 2 ≤ s) : GM s ≤ c0 * theta1 * mMinus s / (1 - rateA) := tsum_betaM_le hs

theorem one_le_FI {s : ℝ} (hs : 0 ≤ s) : 1 ≤ FI s := by
  rw [FI]; linarith [GP_nonneg hs]

theorem fI_le_one {s : ℝ} (hs : 1 ≤ s) : fI s ≤ 1 := by
  rw [fI]; linarith [GM_nonneg hs]

/-! ## Uniform convergence and continuity -/

theorem tendstoUniformlyOn_GP :
    TendstoUniformlyOn (fun N s => ∑ k ∈ Finset.range N, betaP k s) GP atTop (Ici 1) :=
  tendstoUniformlyOn_tsum_nat (f := betaP) summable_two_mul_rateA_pow fun k _ hx => norm_betaP_le k hx

theorem tendstoUniformlyOn_GM :
    TendstoUniformlyOn (fun N s => ∑ k ∈ Finset.range N, betaM k s) GM atTop (Ici 2) :=
  tendstoUniformlyOn_tsum_nat (f := betaM) summable_two_mul_rateA_pow fun k _ hx => norm_betaM_le k hx

theorem continuousOn_GP : ContinuousOn GP (Ici 1) :=
  continuousOn_tsum (f := betaP)
    (fun k => (continuousOn_betaP k).mono fun _ hx => lt_of_lt_of_le one_pos (mem_Ici.mp hx))
    summable_two_mul_rateA_pow (fun k _ hx => norm_betaP_le k hx)

theorem continuousOn_GM : ContinuousOn GM (Ici 2) :=
  continuousOn_tsum (f := betaM)
    (fun k => (continuousOn_betaM k).mono fun _ hx => lt_of_lt_of_le one_lt_two (mem_Ici.mp hx))
    summable_two_mul_rateA_pow (fun k _ hx => norm_betaM_le k hx)

theorem continuousOn_FI : ContinuousOn FI (Ici 1) := continuousOn_const.add continuousOn_GP

theorem continuousOn_fI : ContinuousOn fI (Ici 2) := continuousOn_const.sub continuousOn_GM

theorem continuousAt_FI {s : ℝ} (hs : 1 < s) : ContinuousAt FI s :=
  continuousOn_FI.continuousAt (Ici_mem_nhds hs)

theorem continuousAt_fI {s : ℝ} (hs : 2 < s) : ContinuousAt fI s :=
  continuousOn_fI.continuousAt (Ici_mem_nhds hs)

/-- `u ↦ g (u - 1)` is continuous on `Ici (a + 1)` if `g` is continuous on `Ici a`. -/
lemma continuousOn_comp_sub_one {g : ℝ → ℝ} {a : ℝ} (hg : ContinuousOn g (Ici a)) :
    ContinuousOn (fun u => g (u - 1)) (Ici (a + 1)) :=
  hg.comp (continuous_sub_right 1).continuousOn fun u hu => by
    simp only [mem_Ici] at hu ⊢; linarith

theorem intervalIntegrable_FI {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable FI volume a b :=
  (continuousOn_FI.mono fun x (hx : x ∈ uIcc a b) => mem_Ici.mpr (le_trans (le_inf ha hb) hx.1)).intervalIntegrable

theorem intervalIntegrable_fI {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable fI volume a b :=
  (continuousOn_fI.mono fun x (hx : x ∈ uIcc a b) => mem_Ici.mpr (le_trans (le_inf ha hb) hx.1)).intervalIntegrable

theorem intervalIntegrable_GP {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable GP volume a b :=
  (continuousOn_GP.mono fun x (hx : x ∈ uIcc a b) => mem_Ici.mpr (le_trans (le_inf ha hb) hx.1)).intervalIntegrable

theorem intervalIntegrable_GM {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable GM volume a b :=
  (continuousOn_GM.mono fun x (hx : x ∈ uIcc a b) => mem_Ici.mpr (le_trans (le_inf ha hb) hx.1)).intervalIntegrable

theorem integrableOn_GP {c : ℝ} (hc : 1 ≤ c) : IntegrableOn GP (Ioi c) := by
  have hm : IntegrableOn (fun u => c0 * mPlus u / (1 - rateA)) (Ioi c) :=
    ((integrableOn_mPlus (by linarith)).const_mul c0).div_const _
  refine Integrable.mono' hm
    ((continuousOn_GP.mono fun x hx => mem_Ici.mpr (hc.trans (le_of_lt hx))).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx1 : 1 ≤ x := hc.trans (le_of_lt hx)
  rw [Real.norm_of_nonneg (GP_nonneg (by linarith))]
  exact GP_le hx1

theorem integrableOn_GM {c : ℝ} (hc : 2 ≤ c) : IntegrableOn GM (Ioi c) := by
  have hm : IntegrableOn (fun u => c0 * theta1 * mMinus u / (1 - rateA)) (Ioi c) :=
    ((integrableOn_mMinus c).const_mul (c0 * theta1)).div_const _
  refine Integrable.mono' hm
    ((continuousOn_GM.mono fun x hx => mem_Ici.mpr (hc.trans (le_of_lt hx))).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
  have hx2 : 2 ≤ x := hc.trans (le_of_lt hx)
  rw [Real.norm_of_nonneg (GM_nonneg (by linarith))]
  exact GM_le hx2

/-! ## Integral equations (D2) -/

/-- Swap of `∑'` and `∫_{Ioi c}` for nonnegative terms dominated by `C A^k m`. -/
lemma integral_tsum_Ioi {f : ℕ → ℝ → ℝ} {c C : ℝ} {m : ℝ → ℝ}
    (hint : ∀ k, IntegrableOn (f k) (Ioi c)) (hm : IntegrableOn m (Ioi c))
    (h0 : ∀ k x, c < x → 0 ≤ f k x) (hle : ∀ k x, c < x → f k x ≤ C * rateA ^ k * m x) :
    ∫ x in Ioi c, ∑' k, f k x = ∑' k, ∫ x in Ioi c, f k x := by
  refine (integral_tsum_of_summable_integral_norm hint ?_).symm
  refine summable_of_le_geom (C := C * ∫ x in Ioi c, m x)
    (fun k => integral_nonneg fun x => norm_nonneg _) (fun k => ?_)
  calc ∫ x in Ioi c, ‖f k x‖ ≤ ∫ x in Ioi c, C * rateA ^ k * m x :=
        setIntegral_mono_on (Integrable.norm (hint k)) (hm.const_mul _) measurableSet_Ioi
          fun x hx => by rw [Real.norm_of_nonneg (h0 k x hx)]; exact hle k x hx
    _ = C * (∫ x in Ioi c, m x) * rateA ^ k := by rw [integral_const_mul]; ring

/-- **D2 (+)**: `s G⁺(s) = (3 - s)₊ + ∫_{u > max(s-1,2)} G⁻(u)` for `s ≥ 1`. -/
theorem mul_GP {s : ℝ} (hs : 1 ≤ s) :
    s * GP s = max (3 - s) 0 + ∫ u in Ioi (max (s - 1) 2), GM u := by
  have hs0 : 0 < s := by linarith
  have hc : 2 ≤ max (s - 1) 2 := le_max_right _ _
  have hswap : ∫ x in Ioi (max (s - 1) 2), ∑' k, betaM (k + 1) x
      = ∑' k, ∫ x in Ioi (max (s - 1) 2), betaM (k + 1) x :=
    integral_tsum_Ioi (f := fun k u => betaM (k + 1) u) (C := c0 * theta1) (m := mMinus)
      (fun k => integrableOn_betaM (k + 1) (by linarith)) (integrableOn_mMinus _)
      (fun k x hx => betaM_nonneg _ (by linarith)) (fun k x hx => betaM_succ_le k (by linarith))
  have hGM : ∫ u in Ioi (max (s - 1) 2), GM u = ∫ u in Ioi (max (s - 1) 2), ∑' k, betaM (k + 1) u :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ => GM_eq_tsum_succ u
  rw [hGM, hswap, GP, (summable_betaP hs).tsum_eq_zero_add, mul_add, mul_betaP_zero hs0,
    ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [betaP_succ, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]

/-- **D2 (−)**: `s G⁻(s) = ∫_{u > s-1} G⁺(u)` for `s ≥ 2`. -/
theorem mul_GM {s : ℝ} (hs : 2 ≤ s) : s * GM s = ∫ u in Ioi (s - 1), GP u := by
  have hs0 : 0 < s := by linarith
  have hswap : ∫ x in Ioi (s - 1), GP x = ∑' k, ∫ x in Ioi (s - 1), betaP k x :=
    integral_tsum_Ioi (f := betaP) (C := c0) (m := mPlus)
      (fun k => integrableOn_betaP k (by linarith)) (integrableOn_mPlus (by linarith))
      (fun k x hx => betaP_nonneg k (by linarith)) (fun k x hx => betaP_le k (by linarith))
  rw [hswap, GM_eq_tsum_succ, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [betaM_succ, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]

/-! ## The constants -/

theorem AI_eq : AI = 3 + ∫ u in Ioi 2, GM u := by
  have h := mul_GP (show (1 : ℝ) ≤ 3 by norm_num)
  rw [show max ((3 : ℝ) - 3) 0 = 0 by norm_num, show max ((3 : ℝ) - 1) 2 = 2 by norm_num,
    zero_add] at h
  rw [AI, FI, mul_add, mul_one, h]

theorem BI_eq : BI = 2 - ∫ u in Ioi 1, GP u := by
  have h := mul_GM (show (2 : ℝ) ≤ 2 from le_rfl)
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  rw [BI, fI, mul_sub, mul_one, h]

theorem FI_three : FI 3 = AI / 3 := by rw [AI]; ring

theorem fI_two : fI 2 = BI / 2 := by rw [BI]; ring

theorem three_le_AI : 3 ≤ AI := by
  rw [AI_eq]
  have := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (fun u (hu : u ∈ Ioi (2 : ℝ)) => GM_nonneg (by linarith [mem_Ioi.mp hu]))
  linarith

theorem BI_le_two : BI ≤ 2 := by
  rw [BI_eq]
  have := setIntegral_nonneg (μ := volume) measurableSet_Ioi
    (fun u (hu : u ∈ Ioi (1 : ℝ)) => GP_nonneg (by linarith [mem_Ioi.mp hu]))
  linarith

/-! ## D3: the delay-differential equations in integral form -/

/-- **D3(a)**: `s F_I(s) = A_I` for `1 ≤ s ≤ 3`. -/
theorem mul_FI_of_le_three {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : s * FI s = AI := by
  have h := mul_GP hs1
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 3 - s), max_eq_right (by linarith : s - 1 ≤ 2)] at h
  rw [FI, mul_add, mul_one, h, AI_eq]
  ring

/-- **D3(a)**, divided: `F_I(s) = A_I / s` for `1 ≤ s ≤ 3`. -/
theorem FI_of_le_three {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : FI s = AI / s :=
  eq_div_of_mul_eq (by linarith) (by rw [mul_comm]; exact mul_FI_of_le_three hs1 hs3)

theorem FI_one : FI 1 = AI := by
  rw [FI_of_le_three le_rfl (by norm_num), div_one]

/-- **D3(b)**: `s F_I(s) = A_I + ∫_3^s f_I(u - 1) du` for `s ≥ 3`. -/
theorem mul_FI_of_three_le {s : ℝ} (hs : 3 ≤ s) :
    s * FI s = AI + ∫ u in (3 : ℝ)..s, fI (u - 1) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_GM le_rfl)
    (show (2 : ℝ) ≤ s - 1 by linarith)
  have hGMi : IntervalIntegrable GM volume 2 (s - 1) := intervalIntegrable_GM le_rfl (by linarith)
  have hfI : ∫ x in (2 : ℝ)..s - 1, fI x = (s - 1 - 2) - ∫ x in (2 : ℝ)..s - 1, GM x := by
    simp only [fI]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hGMi, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
  have hP := mul_GP (show (1 : ℝ) ≤ s by linarith)
  rw [max_eq_right (by linarith : 3 - s ≤ 0), max_eq_left (by linarith : (2 : ℝ) ≤ s - 1)] at hP
  rw [intervalIntegral.integral_comp_sub_right fI 1, show (3 : ℝ) - 1 = 2 by norm_num, hfI, AI_eq,
    FI, mul_add, mul_one, hP]
  linarith

/-- **D3(c)**: `s f_I(s) = B_I + ∫_2^s F_I(u - 1) du` for `s ≥ 2`. -/
theorem mul_fI {s : ℝ} (hs : 2 ≤ s) :
    s * fI s = BI + ∫ u in (2 : ℝ)..s, FI (u - 1) := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_GP le_rfl)
    (show (1 : ℝ) ≤ s - 1 by linarith)
  have hGPi : IntervalIntegrable GP volume 1 (s - 1) := intervalIntegrable_GP le_rfl (by linarith)
  have hFI : ∫ x in (1 : ℝ)..s - 1, FI x = (s - 1 - 1) + ∫ x in (1 : ℝ)..s - 1, GP x := by
    simp only [FI]
    rw [intervalIntegral.integral_add intervalIntegrable_const hGPi, intervalIntegral.integral_const,
      smul_eq_mul, mul_one]
  have hM := mul_GM hs
  rw [intervalIntegral.integral_comp_sub_right FI 1, show (2 : ℝ) - 1 = 1 by norm_num, hFI, BI_eq,
    fI, mul_sub, mul_one, hM]
  linarith

/-- **D3(d)**: `s f_I(s) = B_I + A_I log(s - 1)` for `2 ≤ s ≤ 3`. -/
theorem mul_fI_of_le_three {s : ℝ} (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    s * fI s = BI + AI * Real.log (s - 1) := by
  have h1 : (1 : ℝ) ≤ s - 1 := by linarith
  have hcongr : ∫ x in (1 : ℝ)..s - 1, FI x = ∫ x in (1 : ℝ)..s - 1, AI * x⁻¹ := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h1] at hx
    show FI x = AI * x⁻¹
    rw [FI_of_le_three hx.1 (by linarith [hx.2]), div_eq_mul_inv]
  have h0 : (0 : ℝ) ∉ uIcc 1 (s - 1) := by
    rw [uIcc_of_le h1]; intro h; linarith [h.1]
  rw [mul_fI hs2, intervalIntegral.integral_comp_sub_right FI 1, show (2 : ℝ) - 1 = 1 by norm_num,
    hcongr, intervalIntegral.integral_const_mul, integral_inv h0, div_one]

/-- **D3(d)**, divided: `f_I(s) = (B_I + A_I log(s - 1)) / s` on `[2,3]`. -/
theorem fI_of_le_three {s : ℝ} (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    fI s = (BI + AI * Real.log (s - 1)) / s :=
  eq_div_of_mul_eq (by linarith) (by rw [mul_comm]; exact mul_fI_of_le_three hs2 hs3)

/-- `P(s) = s F_I(s) - s f_I(s) = A_I - B_I - A_I log(s - 1)` on `[2,3]` (input for D4a). -/
theorem mul_FI_sub_mul_fI_of_le_three {s : ℝ} (hs2 : 2 ≤ s) (hs3 : s ≤ 3) :
    s * FI s - s * fI s = AI - BI - AI * Real.log (s - 1) := by
  rw [mul_FI_of_le_three (by linarith) hs3, mul_fI_of_le_three hs2 hs3]; ring

/-! ## Forms for D4 / D6: extension by zero and derivatives -/

/-- `s F_I(s) = A_I + ∫_3^s fIext(u - 1) du` for all `s ≥ 1` (the shape of `Fjr_dde`;
for `s ≤ 3` the integrand vanishes a.e.). -/
theorem mul_FI_eq_ext {s : ℝ} (hs : 1 ≤ s) :
    s * FI s = AI + ∫ u in (3 : ℝ)..s, fIext (u - 1) := by
  rcases le_total 3 s with h3 | h3
  · rw [mul_FI_of_three_le h3]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le h3] at hu
    show fI (u - 1) = fIext (u - 1)
    rw [fIext_of_two_le (by linarith [hu.1])]
  · rw [mul_FI_of_le_three hs h3, intervalIntegral.integral_comp_sub_right fIext 1,
      intervalIntegral.integral_symm, intervalIntegral.integral_of_le (show s - 1 ≤ 3 - 1 by linarith),
      integral_Ioc_eq_integral_Ioo, setIntegral_eq_zero_of_forall_eq_zero, neg_zero, add_zero]
    intro x hx
    exact fIext_of_lt_two (by linarith [hx.2])

/-- Given `B_I = 0`, the extension `fIext` is continuous on `[1, ∞)`. -/
theorem continuousOn_fIext (hB : BI = 0) : ContinuousOn fIext (Ici 1) := by
  have hfr : frontier {a : ℝ | 2 ≤ a} = {2} := frontier_Ici
  have hcl : closure {a : ℝ | 2 ≤ a} = Ici 2 := closure_Ici 2
  show ContinuousOn (fun s => if 2 ≤ s then fI s else 0) (Ici 1)
  refine ContinuousOn.if ?_ ?_ continuousOn_const
  · intro a ha
    rw [hfr] at ha
    rw [mem_singleton_iff.mp ha.2, fI_two, hB, zero_div]
  · rw [hcl]; exact continuousOn_fI.mono inter_subset_right

/-- `(s F_I)' = f_I(s - 1)` for `s > 3`. -/
theorem hasDerivAt_mul_FI_of_three_lt {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun x => x * FI x) (fI (s - 1)) s := by
  have hcont : ContinuousOn (fun u => fI (u - 1)) (Ici 3) := by
    have := continuousOn_comp_sub_one continuousOn_fI
    rwa [show (2 : ℝ) + 1 = 3 by norm_num] at this
  have hd : HasDerivAt (fun x => AI + ∫ u in (3 : ℝ)..x, fI (u - 1)) (fI (s - 1)) s := by
    refine (intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_).const_add AI
    · exact (hcont.mono (by rw [uIcc_of_le hs.le]; exact Icc_subset_Ici_self)).intervalIntegrable
    · exact (hcont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi s hs
    · exact hcont.continuousAt (Ici_mem_nhds hs)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact mul_FI_of_three_le (le_of_lt hx)

/-- `(s F_I)' = 0` for `1 < s < 3`. -/
theorem hasDerivAt_mul_FI_of_lt_three {s : ℝ} (h1 : 1 < s) (h3 : s < 3) :
    HasDerivAt (fun x => x * FI x) 0 s := by
  refine (hasDerivAt_const s AI).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds h1 h3] with x hx
  exact mul_FI_of_le_three hx.1.le hx.2.le

/-- `(s F_I)' = fIext(s - 1)` for `s > 1`, `s ≠ 3`. -/
theorem hasDerivAt_mul_FI_ext {s : ℝ} (h1 : 1 < s) (h3 : s ≠ 3) :
    HasDerivAt (fun x => x * FI x) (fIext (s - 1)) s := by
  rcases lt_or_gt_of_ne h3 with h | h
  · rw [fIext_of_lt_two (by linarith)]; exact hasDerivAt_mul_FI_of_lt_three h1 h
  · rw [fIext_of_two_le (by linarith)]; exact hasDerivAt_mul_FI_of_three_lt h

/-- `(s f_I)' = F_I(s - 1)` for `s > 2`. -/
theorem hasDerivAt_mul_fI {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * fI x) (FI (s - 1)) s := by
  have hcont : ContinuousOn (fun u => FI (u - 1)) (Ici 2) := by
    have := continuousOn_comp_sub_one continuousOn_FI
    rwa [show (1 : ℝ) + 1 = 2 by norm_num] at this
  have hd : HasDerivAt (fun x => BI + ∫ u in (2 : ℝ)..x, FI (u - 1)) (FI (s - 1)) s := by
    refine (intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_).const_add BI
    · exact (hcont.mono (by rw [uIcc_of_le hs.le]; exact Icc_subset_Ici_self)).intervalIntegrable
    · exact (hcont.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi s hs
    · exact hcont.continuousAt (Ici_mem_nhds hs)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact mul_fI (le_of_lt hx)

/-! ## D3(e): exponential decay -/

lemma mPlus_le_three_exp {s : ℝ} (hs : 1 ≤ s) : mPlus s ≤ 3 * exp (-s) := by
  rcases le_total s 3 with h | h
  · rw [mPlus_of_le h, div_le_iff₀ (by linarith)]
    have he : exp (-3) ≤ exp (-s) := exp_le_exp.mpr (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (exp_pos (-s)).le]
  · rw [mPlus_of_ge h]; linarith [exp_pos (-s)]

/-- Decay constant for `F_I - 1`. -/
noncomputable def CP : ℝ := 3 * c0 / (1 - rateA)

/-- Decay constant for `f_I - 1`. -/
noncomputable def CM : ℝ := c0 * theta1 / (1 - rateA)

lemma one_sub_rateA_pos : 0 < 1 - rateA := by linarith [rateA_lt_one]

theorem CP_pos : 0 < CP := div_pos (mul_pos (by norm_num) c0_pos) one_sub_rateA_pos

theorem CM_pos : 0 < CM := div_pos (mul_pos c0_pos theta1_pos) one_sub_rateA_pos

theorem GP_le_exp {s : ℝ} (hs : 1 ≤ s) : GP s ≤ CP * exp (-s) := by
  calc GP s ≤ c0 * mPlus s / (1 - rateA) := GP_le hs
    _ ≤ c0 * (3 * exp (-s)) / (1 - rateA) :=
        (div_le_div_iff_of_pos_right one_sub_rateA_pos).mpr
          (mul_le_mul_of_nonneg_left (mPlus_le_three_exp hs) c0_pos.le)
    _ = CP * exp (-s) := by rw [CP]; ring

theorem GM_le_exp {s : ℝ} (hs : 2 ≤ s) : GM s ≤ CM * exp (-s) := by
  calc GM s ≤ c0 * theta1 * mMinus s / (1 - rateA) := GM_le hs
    _ = CM * exp (-s) := by rw [CM, mMinus]; ring

/-- **D3(e) (+)**: `|F_I(s) - 1| ≤ CP e^{-s}` for `s ≥ 1`. -/
theorem abs_FI_sub_one_le {s : ℝ} (hs : 1 ≤ s) : |FI s - 1| ≤ CP * exp (-s) := by
  rw [FI, add_sub_cancel_left, abs_of_nonneg (GP_nonneg (by linarith))]
  exact GP_le_exp hs

/-- **D3(e) (−)**: `|f_I(s) - 1| ≤ CM e^{-s}` for `s ≥ 2`. -/
theorem abs_fI_sub_one_le {s : ℝ} (hs : 2 ≤ s) : |fI s - 1| ≤ CM * exp (-s) := by
  rw [fI, sub_sub_cancel_left, abs_neg, abs_of_nonneg (GM_nonneg (by linarith))]
  exact GM_le_exp hs

/-- **D3(e)**: `|F_I(s) - 1| + |f_I(s) - 1| ≤ (CP + CM) e^{-s}` for `s ≥ 2`. -/
theorem decay {s : ℝ} (hs : 2 ≤ s) :
    |FI s - 1| + |fI s - 1| ≤ (CP + CM) * exp (-s) := by
  have h1 := abs_FI_sub_one_le (show (1 : ℝ) ≤ s by linarith)
  have h2 := abs_fI_sub_one_le hs
  linarith

theorem tendsto_pow_mul_FI_sub_one (n : ℕ) :
    Tendsto (fun s => s ^ n * (FI s - 1)) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul CP
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ s), Real.norm_eq_abs]
  calc s ^ n * |FI s - 1| ≤ s ^ n * (CP * exp (-s)) :=
        mul_le_mul_of_nonneg_left (abs_FI_sub_one_le hs) (pow_nonneg (by linarith) n)
    _ = CP * (s ^ n * exp (-s)) := by ring

theorem tendsto_pow_mul_fI_sub_one (n : ℕ) :
    Tendsto (fun s => s ^ n * (fI s - 1)) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul CM
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ s), Real.norm_eq_abs]
  calc s ^ n * |fI s - 1| ≤ s ^ n * (CM * exp (-s)) :=
        mul_le_mul_of_nonneg_left (abs_fI_sub_one_le hs) (pow_nonneg (by linarith) n)
    _ = CM * (s ^ n * exp (-s)) := by ring

end Palprimes.E1
