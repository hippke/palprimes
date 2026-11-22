import Palprimes.E1.Series
import Palprimes.E1.HFun

set_option linter.style.longLine false

/-! # E1, phase E9: the two constants `B_I = 0` and `A_I = 2 e^γ` (blueprint D4)

Blueprint `lean/e1/E1_BLUEPRINT.md` §5.2.

* D4a (`BI_eq_zero`). `P(s) = s F_I(s) − s f_I(s)` (`Pdiff`, `s ≥ 2`) and
  `Φ(s) = (s − 1) P(s) − ∫_{s−1}^s P` (`Phi4a`, written with the primitive `∫_2^t P`). By D3,
  `Φ' = 0` on `(3, ∞)`; `Φ` is continuous on `[3, ∞)` and tends to `0` (D3(e)), so `Φ(3) = 0`.
  The explicit `[2,3]` form of `P` gives `Φ(3) = −B_I`.
* D4b (`AI_eq_two_mul_exp`). With `B_I = 0`: `n = F_I + fIext − 2` (`nI`, continuous on `[1, ∞)`),
  `Ψ(s) = h(s) · s n(s) + ∫_{s−1}^s h(x + 1) n(x) dx` (`Psi4b`, with the primitive `∫_1^t`).
  `Ψ' = n(s)(s h'(s) + h(s + 1)) = 0` on `(2, ∞) \ {3}` (E8 (H2)), `Ψ → 0`, so `Ψ(2) = 0`; and
  `Ψ(2) = A_I h(1) − 2` by `integral_h_add_one_div` and (H3) at `s = 2`. Hence `A_I = 2/h(1) = 2e^γ` (H4).

The name `AI_eq` is already taken in `Series.lean` (`AI = 3 + ∫_{u>2} G⁻`), hence `AI_eq_two_mul_exp`. -/

open MeasureTheory Set Real Filter Topology

namespace Palprimes.E1

/-! ## Generic tools -/

/-- A function continuous on `[a, ∞)` with derivative `0` on `(a, ∞) \ {c}` and limit `0` at `∞`
vanishes at `a`. -/
lemma eq_zero_of_hasDerivAt_zero_of_tendsto {f : ℝ → ℝ} {a c : ℝ} (hf : ContinuousOn f (Ici a))
    (hd : ∀ x, a < x → x ≠ c → HasDerivAt f 0 x) (hlim : Tendsto f atTop (𝓝 0)) : f a = 0 := by
  have hconst : ∀ b, a ≤ b → f b = f a := by
    intro b hab
    have key := integral_eq_of_hasDerivAt_off_countable_of_le f (fun _ => (0 : ℝ)) hab
      (countable_singleton c) (hf.mono Icc_subset_Ici_self)
      (fun x hx => hd x hx.1.1 hx.2) intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at key
    linarith
  have h2 : Tendsto f atTop (𝓝 (f a)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop a] with b hb using (hconst b hb).symm)
  exact tendsto_nhds_unique h2 hlim

/-- The primitive `t ↦ ∫_c^t g` of a function continuous on `[c, ∞)` is continuous on `[c, ∞)`. -/
lemma continuousOn_primitive_Ici {g : ℝ → ℝ} {c : ℝ} (hg : ContinuousOn g (Ici c)) :
    ContinuousOn (fun t => ∫ x in c..t, g x) (Ici c) := by
  intro t ht
  have ht' : c ≤ t := ht
  have hsub : uIcc c (t + 1) = Icc c (t + 1) := uIcc_of_le (by linarith)
  have h1 : ContinuousOn (fun t => ∫ x in c..t, g x) (Icc c (t + 1)) := by
    rw [← hsub]
    exact intervalIntegral.continuousOn_primitive_interval
      ((hg.mono (by rw [hsub]; exact Icc_subset_Ici_self)).integrableOn_compact isCompact_uIcc)
  refine (h1 t ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- The primitive `t ↦ ∫_c^t g` has derivative `g t` at `t > c`. -/
lemma hasDerivAt_primitive_Ici {g : ℝ → ℝ} {c t : ℝ} (hg : ContinuousOn g (Ici c)) (ht : c < t) :
    HasDerivAt (fun t => ∫ x in c..t, g x) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hg.mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable)
    ((hg.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht)
    (hg.continuousAt (Ici_mem_nhds ht))

/-- `∫_c^s g − ∫_c^{s−1} g = ∫_{s−1}^s g` for `g` continuous on `[c, ∞)`, `s − 1 ≥ c`. -/
lemma primitive_sub_primitive {g : ℝ → ℝ} {c s : ℝ} (hg : ContinuousOn g (Ici c)) (hs : c + 1 ≤ s) :
    (∫ x in c..s, g x) - ∫ x in c..s - 1, g x = ∫ x in (s - 1)..s, g x := by
  refine intervalIntegral.integral_interval_sub_left ?_ ?_
  · exact (hg.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Ici_self)).intervalIntegrable
  · exact (hg.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Ici_self)).intervalIntegrable

/-- If `|g x| ≤ C x e^{−x}` for `x ≥ a ≥ 0`, then `∫_{s−1}^s g → 0`. -/
lemma tendsto_integral_sub_one {g : ℝ → ℝ} {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hg : ∀ x, a ≤ x → |g x| ≤ C * (x * exp (-x))) :
    Tendsto (fun s => ∫ x in (s - 1)..s, g x) atTop (𝓝 0) := by
  have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (C * exp 1)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (a + 1)] with s hs
  have hb : ∀ x ∈ uIoc (s - 1) s, ‖g x‖ ≤ C * exp 1 * (s ^ 1 * exp (-s)) := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    rw [Real.norm_eq_abs]
    refine (hg x (by linarith [hx.1])).trans ?_
    rw [pow_one, show C * exp 1 * (s * exp (-s)) = C * (s * exp (1 + -s)) by rw [exp_add]; ring]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hx.2 (exp_le_exp.mpr (by linarith [hx.1])) (exp_pos _).le (by linarith)) hC
  have key := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [show |s - (s - 1)| = 1 by norm_num, mul_one] at key

lemma CP_add_CM_nonneg : 0 ≤ CP + CM := by linarith [CP_pos, CM_pos]

/-! ## D4a: `B_I = 0` -/

/-- `P(s) = s F_I(s) − s f_I(s)`. -/
noncomputable def Pdiff (s : ℝ) : ℝ := s * FI s - s * fI s

/-- The primitive `∫_2^t P`. -/
noncomputable def PdiffPrim (t : ℝ) : ℝ := ∫ x in (2 : ℝ)..t, Pdiff x

/-- `Φ(s) = (s − 1) P(s) − ∫_{s−1}^s P` (written with the primitive). -/
noncomputable def Phi4a (s : ℝ) : ℝ := (s - 1) * Pdiff s - (PdiffPrim s - PdiffPrim (s - 1))

lemma continuousOn_Pdiff : ContinuousOn Pdiff (Ici 2) :=
  ((continuousOn_id.mul continuousOn_FI).mono (Ici_subset_Ici.mpr one_le_two)).sub
    (continuousOn_id.mul continuousOn_fI)

lemma hasDerivAt_Pdiff {s : ℝ} (hs : 3 < s) : HasDerivAt Pdiff (fI (s - 1) - FI (s - 1)) s :=
  (hasDerivAt_mul_FI_of_three_lt hs).sub (hasDerivAt_mul_fI (by linarith))

lemma abs_Pdiff_le {x : ℝ} (hx : 2 ≤ x) : |Pdiff x| ≤ (CP + CM) * (x * exp (-x)) := by
  have hd := decay hx
  have h0 : 0 ≤ x := by linarith
  rw [Pdiff, show x * FI x - x * fI x = x * ((FI x - 1) - (fI x - 1)) by ring, abs_mul,
    abs_of_nonneg h0]
  calc x * |(FI x - 1) - (fI x - 1)| ≤ x * (|FI x - 1| + |fI x - 1|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) h0
    _ ≤ x * ((CP + CM) * exp (-x)) := mul_le_mul_of_nonneg_left hd h0
    _ = (CP + CM) * (x * exp (-x)) := by ring

lemma continuousOn_Phi4a : ContinuousOn Phi4a (Ici 3) := by
  have hP : ContinuousOn Pdiff (Ici 3) := continuousOn_Pdiff.mono (Ici_subset_Ici.mpr (by norm_num))
  have hprim : ContinuousOn PdiffPrim (Ici 2) := continuousOn_primitive_Ici continuousOn_Pdiff
  have hprim1 : ContinuousOn (fun s => PdiffPrim (s - 1)) (Ici 3) :=
    hprim.comp (continuous_sub_right 1).continuousOn fun s hs => by
      simp only [mem_Ici] at hs ⊢; linarith
  exact ((continuousOn_id.sub continuousOn_const).mul hP).sub
    ((hprim.mono (Ici_subset_Ici.mpr (by norm_num))).sub hprim1)

lemma hasDerivAt_Phi4a {s : ℝ} (hs : 3 < s) : HasDerivAt Phi4a 0 s := by
  have h1 : HasDerivAt (fun x => (x - 1) * Pdiff x)
      (1 * Pdiff s + (s - 1) * (fI (s - 1) - FI (s - 1))) s :=
    ((hasDerivAt_id' s).sub_const 1).mul (hasDerivAt_Pdiff hs)
  have h2 : HasDerivAt PdiffPrim (Pdiff s) s :=
    hasDerivAt_primitive_Ici continuousOn_Pdiff (by linarith)
  have h3 : HasDerivAt (fun x => PdiffPrim (x - 1)) (Pdiff (s - 1)) s :=
    HasDerivAt.comp_sub_const s 1 (hasDerivAt_primitive_Ici continuousOn_Pdiff (by linarith))
  refine (h1.sub (h2.sub h3)).congr_deriv ?_
  simp only [Pdiff]
  ring

lemma tendsto_Phi4a : Tendsto Phi4a atTop (𝓝 0) := by
  have hA : Tendsto (fun s => (s - 1) * Pdiff s) atTop (𝓝 0) := by
    have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (CP + CM)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - 1)]
    calc (s - 1) * |Pdiff s| ≤ s * ((CP + CM) * (s * exp (-s))) :=
          mul_le_mul (by linarith) (abs_Pdiff_le hs) (abs_nonneg _) (by linarith)
      _ = (CP + CM) * (s ^ 2 * exp (-s)) := by ring
  have hB : Tendsto (fun s => ∫ x in (s - 1)..s, Pdiff x) atTop (𝓝 0) :=
    tendsto_integral_sub_one (by norm_num : (0 : ℝ) ≤ 2) CP_add_CM_nonneg fun x hx => abs_Pdiff_le hx
  have hAB := hA.sub hB
  rw [sub_zero] at hAB
  refine hAB.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
  rw [Phi4a, PdiffPrim, PdiffPrim, primitive_sub_primitive continuousOn_Pdiff (by linarith)]

lemma integral_log_sub_one_two_three : ∫ x in (2 : ℝ)..3, log (x - 1) = 2 * log 2 - 1 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => log x) 1, integral_log]
  norm_num
  ring

lemma PdiffPrim_three : PdiffPrim 3 = (AI - BI) - AI * (2 * log 2 - 1) := by
  have hcongr : ∫ x in (2 : ℝ)..3, Pdiff x = ∫ x in (2 : ℝ)..3, ((AI - BI) - AI * log (x - 1)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    exact mul_FI_sub_mul_fI_of_le_three hx.1 hx.2
  have hlog : IntervalIntegrable (fun x => log (x - 1)) volume 2 3 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.log (f := fun x => x - 1) (by fun_prop) fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    exact (show (0 : ℝ) < x - 1 by linarith [hx.1]).ne'
  rw [PdiffPrim, hcongr, intervalIntegral.integral_sub intervalIntegrable_const (hlog.const_mul AI),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_sub_one_two_three]
  norm_num

lemma Phi4a_three : Phi4a 3 = -BI := by
  have hP3 : Pdiff 3 = AI - BI - AI * log 2 := by
    have key := mul_FI_sub_mul_fI_of_le_three (s := 3) (by norm_num) le_rfl
    rw [show (3 : ℝ) - 1 = 2 by norm_num] at key
    exact key
  have h2 : PdiffPrim 2 = 0 := intervalIntegral.integral_same
  rw [Phi4a, show (3 : ℝ) - 1 = 2 by norm_num, hP3, h2, PdiffPrim_three]
  ring

/-- **D4a**: `B_I = 0`. -/
theorem BI_eq_zero : BI = 0 := by
  have key := eq_zero_of_hasDerivAt_zero_of_tendsto (c := 3) continuousOn_Phi4a
    (fun x hx _ => hasDerivAt_Phi4a hx) tendsto_Phi4a
  rw [Phi4a_three] at key
  linarith

/-- `f_I(2) = 0`. -/
theorem fI_two_eq_zero : fI 2 = 0 := by rw [fI_two, BI_eq_zero, zero_div]

/-- `fIext = 0` on `(−∞, 2]`. -/
theorem fIext_of_le_two {x : ℝ} (hx : x ≤ 2) : fIext x = 0 := by
  rcases hx.lt_or_eq with hx | rfl
  · exact fIext_of_lt_two hx
  · rw [fIext_of_two_le le_rfl, fI_two_eq_zero]

/-! ## D4b: `A_I = 2 e^γ` -/

/-- `n = F_I + fIext − 2`. -/
noncomputable def nI (s : ℝ) : ℝ := FI s + fIext s - 2

/-- The integrand `h(x + 1) n(x)`. -/
noncomputable def gI (x : ℝ) : ℝ := h (x + 1) * nI x

/-- The primitive `∫_1^t h(x + 1) n(x) dx`. -/
noncomputable def gIprim (t : ℝ) : ℝ := ∫ x in (1 : ℝ)..t, gI x

/-- `Ψ(s) = h(s) · s n(s) + ∫_{s−1}^s h(x + 1) n(x) dx` (written with the primitive). -/
noncomputable def Psi4b (s : ℝ) : ℝ := h s * (s * nI s) + (gIprim s - gIprim (s - 1))

lemma continuousOn_nI : ContinuousOn nI (Ici 1) :=
  (continuousOn_FI.add (continuousOn_fIext BI_eq_zero)).sub continuousOn_const

lemma continuousOn_h_add_one : ContinuousOn (fun x => h (x + 1)) (Ici 1) :=
  continuousOn_h.comp (continuous_id.add continuous_const).continuousOn fun x hx => by
    simp only [mem_Ici, mem_Ioi] at hx ⊢; linarith

lemma continuousOn_gI : ContinuousOn gI (Ici 1) := continuousOn_h_add_one.mul continuousOn_nI

lemma abs_nI_le {x : ℝ} (hx : 2 ≤ x) : |nI x| ≤ (CP + CM) * exp (-x) := by
  rw [nI, fIext_of_two_le hx, show FI x + fI x - 2 = (FI x - 1) + (fI x - 1) by ring]
  exact (abs_add_le _ _).trans (decay hx)

lemma abs_h_le_one {x : ℝ} (hx : 0 ≤ x) : |h (x + 1)| ≤ 1 := by
  rw [abs_of_nonneg (h_nonneg _)]
  refine (h_le (by linarith)).trans ?_
  rw [div_le_one (by linarith)]
  linarith

lemma abs_gI_le {x : ℝ} (hx : 2 ≤ x) : |gI x| ≤ (CP + CM) * (x * exp (-x)) := by
  rw [gI, abs_mul]
  calc |h (x + 1)| * |nI x| ≤ 1 * ((CP + CM) * exp (-x)) :=
        mul_le_mul (abs_h_le_one (by linarith)) (abs_nI_le hx) (abs_nonneg _) zero_le_one
    _ ≤ (CP + CM) * (x * exp (-x)) := by
        rw [one_mul, ← mul_assoc, mul_comm (CP + CM) x, mul_assoc]
        exact le_mul_of_one_le_left (mul_nonneg CP_add_CM_nonneg (exp_pos _).le) (by linarith)

lemma hasDerivAt_mul_fIext {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * fIext x) (FI (s - 1)) s := by
  refine (hasDerivAt_mul_fI hs).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  rw [fIext_of_two_le (le_of_lt hx)]

lemma hasDerivAt_mul_nI {s : ℝ} (hs : 2 < s) (h3 : s ≠ 3) :
    HasDerivAt (fun x => x * nI x) (nI (s - 1)) s := by
  have key := ((hasDerivAt_mul_FI_ext (by linarith) h3).add (hasDerivAt_mul_fIext hs)).sub
    ((hasDerivAt_id' s).const_mul 2)
  refine (key.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [nI, Pi.add_apply, Pi.sub_apply]; ring
  · simp only [nI]; ring

lemma continuousOn_Psi4b : ContinuousOn Psi4b (Ici 2) := by
  have hh : ContinuousOn h (Ici 2) := continuousOn_h.mono fun x hx => by
    simp only [mem_Ici, mem_Ioi] at hx ⊢; linarith
  have hn : ContinuousOn (fun s => s * nI s) (Ici 2) :=
    continuousOn_id.mul (continuousOn_nI.mono (Ici_subset_Ici.mpr one_le_two))
  have hprim : ContinuousOn gIprim (Ici 1) := continuousOn_primitive_Ici continuousOn_gI
  have hprim1 : ContinuousOn (fun s => gIprim (s - 1)) (Ici 2) :=
    hprim.comp (continuous_sub_right 1).continuousOn fun s hs => by
      simp only [mem_Ici] at hs ⊢; linarith
  exact (hh.mul hn).add ((hprim.mono (Ici_subset_Ici.mpr one_le_two)).sub hprim1)

lemma hasDerivAt_Psi4b {s : ℝ} (hs : 2 < s) (h3 : s ≠ 3) : HasDerivAt Psi4b 0 s := by
  have hs0 : s ≠ 0 := by positivity
  have h1 : HasDerivAt (fun x => h x * (x * nI x))
      (-h (s + 1) / s * (s * nI s) + h s * nI (s - 1)) s :=
    (hasDerivAt_h (by linarith)).mul (hasDerivAt_mul_nI hs h3)
  have h2 : HasDerivAt gIprim (gI s) s := hasDerivAt_primitive_Ici continuousOn_gI (by linarith)
  have h4 : HasDerivAt (fun x => gIprim (x - 1)) (gI (s - 1)) s :=
    HasDerivAt.comp_sub_const s 1 (hasDerivAt_primitive_Ici continuousOn_gI (by linarith))
  refine (h1.add (h2.sub h4)).congr_deriv ?_
  simp only [gI, sub_add_cancel]
  field_simp
  ring

lemma tendsto_Psi4b : Tendsto Psi4b atTop (𝓝 0) := by
  have hA : Tendsto (fun s => h s * (s * nI s)) atTop (𝓝 0) := by
    have hlim := tendsto_exp_neg_atTop_nhds_zero.const_mul (CP + CM)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, ← mul_assoc, abs_mul, mul_comm (h s) s,
      abs_of_nonneg (mul_nonneg hs0.le (h_nonneg s))]
    calc s * h s * |nI s| ≤ 1 * ((CP + CM) * exp (-s)) :=
          mul_le_mul (mul_h_le_one hs0) (abs_nI_le hs) (abs_nonneg _) zero_le_one
      _ = (CP + CM) * exp (-s) := one_mul _
  have hB : Tendsto (fun s => ∫ x in (s - 1)..s, gI x) atTop (𝓝 0) :=
    tendsto_integral_sub_one (by norm_num : (0 : ℝ) ≤ 2) CP_add_CM_nonneg fun x hx => abs_gI_le hx
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine hAB.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  rw [Psi4b, gIprim, gIprim, primitive_sub_primitive continuousOn_gI (by linarith)]

lemma nI_of_mem {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : nI x = AI / x - 2 := by
  rw [nI, FI_of_le_three hx1 (by linarith), fIext_of_le_two hx2, add_zero]

lemma gIprim_two : gIprim 2 = AI * (h 1 - h 2) - 2 * ∫ x in (2 : ℝ)..3, h x := by
  have hcongr : ∫ x in (1 : ℝ)..2, gI x = ∫ x in (1 : ℝ)..2, (AI * (h (x + 1) / x) - 2 * h (x + 1)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    simp only [gI]
    rw [nI_of_mem hx.1 hx.2]
    field_simp
  have hc1 : ContinuousOn (fun x => h (x + 1)) (uIcc 1 2) :=
    continuousOn_h_add_one.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Ici_self)
  have hi1 : IntervalIntegrable (fun x => h (x + 1) / x) volume 1 2 := by
    refine (hc1.div continuousOn_id fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by norm_num)] at hx
    exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
  have hi2 : IntervalIntegrable (fun x => h (x + 1)) volume 1 2 := hc1.intervalIntegrable
  rw [gIprim, hcongr, intervalIntegral.integral_sub (hi1.const_mul AI) (hi2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_h_add_one_div one_pos two_pos, intervalIntegral.integral_comp_add_right (fun x => h x) 1]
  norm_num

lemma Psi4b_two : Psi4b 2 = AI * h 1 - 2 := by
  have hn2 : nI 2 = AI / 2 - 2 := nI_of_mem one_le_two le_rfl
  have h1 : gIprim 1 = 0 := intervalIntegral.integral_same
  have H3 := mul_h_add_integral_h (show (0 : ℝ) < 2 by norm_num)
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at H3
  rw [Psi4b, show (2 : ℝ) - 1 = 1 by norm_num, h1, gIprim_two, hn2]
  linear_combination (-2) * H3

/-- **D4b**: `A_I = 2 e^γ`. (The name `AI_eq` is taken by `Series.lean`.) -/
theorem AI_eq_two_mul_exp : AI = 2 * exp eulerMascheroniConstant := by
  have key := eq_zero_of_hasDerivAt_zero_of_tendsto (c := 3) continuousOn_Psi4b
    (fun x hx hx3 => hasDerivAt_Psi4b hx hx3) tendsto_Psi4b
  rw [Psi4b_two, h_one, exp_neg] at key
  have he : exp eulerMascheroniConstant ≠ 0 := (exp_pos _).ne'
  field_simp at key
  linarith

end Palprimes.E1
