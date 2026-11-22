import Mathlib

/-! # E8: the adjoint function `h` of Iwaniec 1980 §7 for `κ = 1` (blueprint §5.2)

`E(z) = ∫₀^z (1 − e^{−u})/u du` (the integrand `Eint`; at `u = 0` Lean's `0/0 = 0`, harmless) and
`h(s) = ∫₀^∞ e^{−sz−E(z)} dz`.

* `E_nonneg`, `E_le`, `hasDerivAt_E`, `continuousOn_E`: `0 ≤ E(z) ≤ z`, `E' = (1 − e^{−z})/z`;
* (H1) `h_pos`, `h_le`, `mul_h_le_one`, `h_nonneg`: `0 < h(s) ≤ 1/s`;
* `continuousOn_h`: `h` is continuous on `(0, ∞)`;
* (H3) `mul_h_add_integral_h`: `s h(s) + ∫_s^{s+1} h = 1` (Fubini plus integration by parts);
* (H2) `hasDerivAt_h`, `mul_deriv_h`: `h'(s) = −h(s+1)/s`, i.e. `s h'(s) = −h(s+1)` (from (H3));
  `hasDerivAt_h_integral`: `h'(s) = −∫₀^∞ z e^{−sz−E(z)} dz`;
* `integral_h_add_one_div`: `∫_a^b h(x+1)/x dx = h(a) − h(b)` (used in D4b);
* (H4) `h_one`: `h(1) = e^{−γ}`
  (via Mathlib's `Real.eulerMascheroniConstant_eq_neg_integral_log`). -/

set_option linter.style.longLine false

open MeasureTheory Set Real Filter Topology

namespace Palprimes.E1

/-! ## The function `E` -/

/-- The integrand of `E`: `(1 − e^{−u})/u` (value `0` at `u = 0`). -/
noncomputable def Eint (u : ℝ) : ℝ := (1 - exp (-u)) / u

/-- `E(z) = ∫₀^z (1 − e^{−u})/u du`. -/
noncomputable def E (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, Eint u

/-- The adjoint function `h(s) = ∫₀^∞ e^{−sz−E(z)} dz`. -/
noncomputable def h (s : ℝ) : ℝ := ∫ z in Ioi (0 : ℝ), exp (-s * z - E z)

theorem E_def (z : ℝ) : E z = ∫ u in (0 : ℝ)..z, (1 - exp (-u)) / u := rfl

lemma Eint_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Eint u := by
  unfold Eint
  have : exp (-u) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  exact div_nonneg (by linarith) hu

lemma Eint_le_one {u : ℝ} (hu : 0 ≤ u) : Eint u ≤ 1 := by
  unfold Eint
  rcases hu.eq_or_lt with rfl | hu
  · simp
  rw [div_le_one hu]
  have := add_one_le_exp (-u)
  linarith

lemma measurable_Eint : Measurable Eint := by
  unfold Eint; fun_prop

lemma continuousAt_Eint {u : ℝ} (hu : u ≠ 0) : ContinuousAt Eint u := by
  unfold Eint
  exact ((continuous_const.sub (continuous_exp.comp continuous_neg)).continuousAt).div
    continuousAt_id hu

lemma continuousOn_Eint : ContinuousOn Eint (Ioi 0) :=
  fun _ hu => (continuousAt_Eint (ne_of_gt hu)).continuousWithinAt

lemma mul_Eint {u : ℝ} (hu : u ≠ 0) : u * Eint u = 1 - exp (-u) := by
  unfold Eint; field_simp

lemma mem_uIoc_nonneg {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : u ∈ uIoc a b) : 0 ≤ u :=
  (le_inf ha hb).trans (le_of_lt hu.1)

lemma intervalIntegrable_Eint {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable Eint volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    measurable_Eint.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc fun u hu => ?_
  have hu0 := mem_uIoc_nonneg ha hb hu
  change ‖Eint u‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Eint_nonneg hu0)]
  exact Eint_le_one hu0

theorem E_zero : E 0 = 0 := by simp [E]

theorem E_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ E z :=
  intervalIntegral.integral_nonneg hz fun _ hu => Eint_nonneg hu.1

theorem E_le {z : ℝ} (hz : 0 ≤ z) : E z ≤ z := by
  have : E z ≤ ∫ _ in (0 : ℝ)..z, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hz (intervalIntegrable_Eint le_rfl hz)
      intervalIntegrable_const fun _ hu => Eint_le_one hu.1
  simpa using this

lemma abs_E_sub_le {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) : |E z - E w| ≤ |z - w| := by
  have hsub : E z - E w = ∫ u in w..z, Eint u :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_Eint le_rfl hz)
      (intervalIntegrable_Eint le_rfl hw)
  rw [hsub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := w) (b := z) (C := 1)
    (f := Eint) fun u hu => by
      have hu0 := mem_uIoc_nonneg hw hz hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Eint_nonneg hu0)]
      exact Eint_le_one hu0
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

theorem continuousOn_E : ContinuousOn E (Ici 0) := by
  have : LipschitzOnWith 1 E (Ici 0) := LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    simpa [Real.dist_eq] using abs_E_sub_le (mem_Ici.mp hx) (mem_Ici.mp hy)
  exact this.continuousOn

theorem hasDerivAt_E {z : ℝ} (hz : 0 < z) : HasDerivAt E (Eint z) z :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_Eint le_rfl hz.le)
    measurable_Eint.stronglyMeasurable.stronglyMeasurableAtFilter (continuousAt_Eint hz.ne')

/-! ## Integrability of the `h` integrand -/

lemma continuousOn_hint (s : ℝ) : ContinuousOn (fun z => exp (-s * z - E z)) (Ici 0) := by
  have := continuousOn_E
  fun_prop

lemma hint_le {s z : ℝ} (hz : 0 ≤ z) : exp (-s * z - E z) ≤ exp (-s * z) :=
  exp_le_exp.mpr (by linarith [E_nonneg hz])

lemma integrableOn_of_le_exp {f : ℝ → ℝ} {a C : ℝ} (ha : 0 < a) (hf : ContinuousOn f (Ioi 0))
    (hb : ∀ z, 0 < z → |f z| ≤ C * exp (-a * z)) : IntegrableOn f (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 ha).const_mul C)
    (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
  rw [Real.norm_eq_abs]
  exact hb z hz

lemma integrableOn_hint {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun z => exp (-s * z - E z)) (Ioi 0) :=
  integrableOn_of_le_exp (C := 1) hs ((continuousOn_hint s).mono Ioi_subset_Ici_self)
    fun z hz => by rw [abs_of_pos (exp_pos _), one_mul]; exact hint_le hz.le

lemma integral_exp_neg_mul {a : ℝ} (ha : 0 < a) : ∫ z in Ioi (0 : ℝ), exp (-a * z) = 1 / a := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ha) 0]
  simp

/-! ## (H1) bounds -/

theorem h_nonneg (s : ℝ) : 0 ≤ h s :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (exp_pos _).le

theorem h_le {s : ℝ} (hs : 0 < s) : h s ≤ 1 / s := by
  rw [← integral_exp_neg_mul hs]
  exact setIntegral_mono_on (integrableOn_hint hs) (exp_neg_integrableOn_Ioi 0 hs)
    measurableSet_Ioi fun z hz => hint_le (le_of_lt hz)

theorem one_div_add_one_le_h {s : ℝ} (hs : 0 < s) : 1 / (s + 1) ≤ h s := by
  rw [← integral_exp_neg_mul (by linarith : 0 < s + 1)]
  refine setIntegral_mono_on (exp_neg_integrableOn_Ioi 0 (by linarith)) (integrableOn_hint hs)
    measurableSet_Ioi fun z hz => exp_le_exp.mpr ?_
  have := E_le (le_of_lt hz)
  nlinarith

theorem h_pos {s : ℝ} (hs : 0 < s) : 0 < h s :=
  lt_of_lt_of_le (by positivity) (one_div_add_one_le_h hs)

theorem mul_h_le_one {s : ℝ} (hs : 0 < s) : s * h s ≤ 1 := by
  have := h_le hs
  rw [le_div_iff₀ hs] at this
  linarith

/-! ## Continuity of `h` -/

theorem continuousOn_h : ContinuousOn h (Ioi 0) := by
  intro s₀ hs₀
  have hs₀ : 0 < s₀ := hs₀
  have : ContinuousAt (fun s => ∫ z in Ioi (0 : ℝ), exp (-s * z - E z)) s₀ := by
    refine continuousAt_of_dominated (bound := fun z => exp (-(s₀ / 2) * z)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        ((continuousOn_hint s).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioi_mem_nhds (half_lt_self hs₀)] with s hs
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      have hz : 0 < z := hz
      have hs : s₀ / 2 < s := hs
      exact exp_le_exp.mpr (by nlinarith [E_nonneg hz.le])
    · exact exp_neg_integrableOn_Ioi 0 (half_pos hs₀)
    · exact Eventually.of_forall fun z => by fun_prop
  exact this.continuousWithinAt

lemma uIcc_subset_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : uIcc a b ⊆ Ioi 0 :=
  fun _ hx => lt_of_lt_of_le (lt_inf_iff.mpr ⟨ha, hb⟩) hx.1

lemma intervalIntegrable_h {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable h volume a b :=
  (continuousOn_h.mono (uIcc_subset_Ioi ha hb)).intervalIntegrable

/-! ## (H3) `s h(s) + ∫_s^{s+1} h = 1` -/

lemma integral_Ioc_hint {s z : ℝ} (hz : 0 < z) :
    ∫ x in Ioc s (s + 1), exp (-x * z - E z) = Eint z * exp (-s * z - E z) := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hd : ∀ x ∈ uIcc s (s + 1),
      HasDerivAt (fun x => -exp (-x * z - E z) / z) (exp (-x * z - E z)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -x * z - E z) (-1 * z) x :=
      ((hasDerivAt_id' x).neg.mul_const z).sub_const (E z)
    exact (h1.exp.neg.div_const z).congr_deriv (by field_simp [hz.ne'])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x => exp (-x * z - E z)).intervalIntegrable _ _)]
  have : exp (-(s + 1) * z - E z) = exp (-s * z - E z) * exp (-z) := by
    rw [← exp_add]; ring_nf
  rw [this]
  unfold Eint
  field_simp
  ring

lemma integrable_prod_hint {s : ℝ} (hs : 0 < s) :
    Integrable (Function.uncurry fun (x z : ℝ) => exp (-x * z - E z))
      ((volume.restrict (Ioc s (s + 1))).prod (volume.restrict (Ioi 0))) := by
  have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * exp (-s * p.2))
      ((volume.restrict (Ioc s (s + 1))).prod (volume.restrict (Ioi 0))) :=
    Integrable.mul_prod (integrableOn_const measure_Ioc_lt_top.ne) (exp_neg_integrableOn_Ioi 0 hs)
  have hmeas : MeasurableSet (Ioc s (s + 1) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioc.prod measurableSet_Ioi
  refine hg.mono' ?_ ?_
  · rw [Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ hmeas
    have hE : ContinuousOn (fun p : ℝ × ℝ => E p.2) (Ioc s (s + 1) ×ˢ Ioi (0 : ℝ)) :=
      continuousOn_E.comp continuous_snd.continuousOn fun p hp => mem_Ici.mpr (le_of_lt hp.2)
    simp only [Function.uncurry_def]
    fun_prop
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem hmeas fun p hp => ?_
    obtain ⟨⟨hx1, _⟩, hz⟩ := hp
    have hz : 0 < p.2 := hz
    simp only [Function.uncurry_def, Real.norm_eq_abs, abs_of_pos (exp_pos _), one_mul]
    exact exp_le_exp.mpr (by nlinarith [E_nonneg hz.le])

lemma integral_h_eq {s : ℝ} (hs : 0 < s) :
    ∫ x in s..s + 1, h x = ∫ z in Ioi 0, Eint z * exp (-s * z - E z) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  unfold h
  rw [integral_integral_swap (integrable_prod_hint hs)]
  exact setIntegral_congr_fun measurableSet_Ioi fun z hz => integral_Ioc_hint hz

lemma integrableOn_Eint_hint {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun z => Eint z * exp (-s * z - E z)) (Ioi 0) :=
  integrableOn_of_le_exp (C := 1) hs
    (continuousOn_Eint.mul ((continuousOn_hint s).mono Ioi_subset_Ici_self)) fun z hz => by
      rw [abs_mul, abs_of_nonneg (Eint_nonneg hz.le), abs_of_pos (exp_pos _)]
      exact mul_le_mul (Eint_le_one hz.le) (hint_le hz.le) (exp_pos _).le zero_le_one

/-- (H3) `s h(s) + ∫_s^{s+1} h = 1` for `s > 0`. -/
theorem mul_h_add_integral_h {s : ℝ} (hs : 0 < s) : s * h s + ∫ x in s..s + 1, h x = 1 := by
  rw [integral_h_eq hs]
  have hcont : ContinuousWithinAt (fun z => -exp (-s * z - E z)) (Ici 0) 0 :=
    (continuousOn_hint s).neg 0 (mem_Ici.mpr le_rfl)
  have hderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt (fun z => -exp (-s * z - E z))
      (s * exp (-s * z - E z) + Eint z * exp (-s * z - E z)) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => -s * z - E z) (-s * 1 - Eint z) z :=
      ((hasDerivAt_id' z).const_mul (-s)).sub (hasDerivAt_E hz)
    exact h1.exp.neg.congr_deriv (by ring)
  have hint : IntegrableOn (fun z => s * exp (-s * z - E z) + Eint z * exp (-s * z - E z))
      (Ioi 0) := ((integrableOn_hint hs).const_mul s).add (integrableOn_Eint_hint hs)
  have hlim : Tendsto (fun z => -exp (-s * z - E z)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun z => exp (-s * z)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hs))
    have h1 : Tendsto (fun z => exp (-s * z - E z)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => (exp_pos _).le) ?_ h0
      filter_upwards [eventually_ge_atTop 0] with z hz using hint_le hz
    simpa using h1.neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_add ((integrableOn_hint hs).const_mul s) (integrableOn_Eint_hint hs),
    integral_const_mul] at key
  simpa [E_zero, h] using key

/-! ## (H2) `h'(s) = −h(s+1)/s` -/

/-- (H2) `h` is differentiable on `(0, ∞)` with `h'(s) = −h(s+1)/s`. -/
theorem hasDerivAt_h {s : ℝ} (hs : 0 < s) : HasDerivAt h (-h (s + 1) / s) s := by
  set Φ : ℝ → ℝ := fun t => ∫ x in (1 : ℝ)..t, h x with hΦdef
  have hΦ : ∀ t, 0 < t → HasDerivAt Φ (h t) t := fun t ht =>
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_h one_pos ht)
      (continuousOn_h.stronglyMeasurableAtFilter isOpen_Ioi t ht)
      (continuousOn_h.continuousAt (Ioi_mem_nhds ht))
  have hsub : ∀ t, 0 < t → Φ (t + 1) - Φ t = ∫ x in t..t + 1, h x := fun t ht =>
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_h one_pos (by linarith))
      (intervalIntegrable_h one_pos ht)
  have hG : HasDerivAt (fun t => (1 - (Φ (t + 1) - Φ t)) / t) (-h (s + 1) / s) s := by
    have h1 : HasDerivAt (fun t => Φ (t + 1)) (h (s + 1)) s :=
      HasDerivAt.comp_add_const s 1 (hΦ (s + 1) (by linarith))
    have H3 := mul_h_add_integral_h hs
    rw [← hsub s hs] at H3
    have he : 1 - (Φ (s + 1) - Φ s) = s * h s := by linarith
    have hval : (-(h (s + 1) - h s) * s - (1 - (Φ (s + 1) - Φ s)) * 1) / s ^ 2 =
        -h (s + 1) / s := by
      rw [he]
      field_simp
      ring
    exact (((h1.sub (hΦ s hs)).const_sub 1).div (hasDerivAt_id' s) hs.ne').congr_deriv hval
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with t ht
  have ht : 0 < t := ht
  have H3 := mul_h_add_integral_h ht
  rw [← hsub t ht] at H3
  rw [eq_div_iff ht.ne']
  linarith

theorem differentiableAt_h {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ h s :=
  (hasDerivAt_h hs).differentiableAt

theorem deriv_h {s : ℝ} (hs : 0 < s) : deriv h s = -h (s + 1) / s :=
  (hasDerivAt_h hs).deriv

/-- (H2) `s h'(s) = −h(s+1)`. -/
theorem mul_deriv_h {s : ℝ} (hs : 0 < s) : s * deriv h s = -h (s + 1) := by
  rw [deriv_h hs]
  field_simp

/-- `∫_a^b h(x+1)/x dx = h(a) − h(b)` for `a, b > 0` (from (H2)). -/
theorem integral_h_add_one_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, h (x + 1) / x = h a - h b := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt h (-h (x + 1) / x) x := fun x hx =>
    hasDerivAt_h (uIcc_subset_Ioi ha hb hx)
  have hc : ContinuousOn (fun x => -h (x + 1) / x) (uIcc a b) := by
    refine (continuousOn_h.comp (continuous_id.add continuous_const).continuousOn
      fun x hx => ?_).neg.div continuousOn_id fun x hx => ne_of_gt (uIcc_subset_Ioi ha hb hx)
    have : (0 : ℝ) < x := uIcc_subset_Ioi ha hb hx
    change (0 : ℝ) < x + 1
    linarith
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simp only [neg_div, intervalIntegral.integral_neg] at this
  linarith

/-! ## (H2), integral form: `h'(s) = −∫₀^∞ z e^{−sz−E(z)} dz` -/

lemma mul_hint_le {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    z * exp (-s * z - E z) ≤ 2 / s * exp (-(s / 2) * z) := by
  have h1 : s / 2 * z ≤ exp (s / 2 * z) := by linarith [add_one_le_exp (s / 2 * z)]
  have h2 : z ≤ 2 / s * exp (s / 2 * z) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith
  have h3 : exp (-s * z) = exp (-(s / 2) * z) * exp (-(s / 2) * z) := by
    rw [← exp_add]; ring_nf
  have h4 : exp (s / 2 * z) * exp (-(s / 2) * z) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  calc z * exp (-s * z - E z) ≤ z * exp (-s * z) := mul_le_mul_of_nonneg_left (hint_le hz) hz
    _ = z * exp (-(s / 2) * z) * exp (-(s / 2) * z) := by rw [h3]; ring
    _ ≤ 2 / s * exp (s / 2 * z) * exp (-(s / 2) * z) * exp (-(s / 2) * z) := by gcongr
    _ = 2 / s * exp (-(s / 2) * z) := by rw [mul_assoc (2 / s), h4, mul_one]

lemma integrableOn_mul_hint {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun z => z * exp (-s * z - E z)) (Ioi 0) :=
  integrableOn_of_le_exp (C := 2 / s) (half_pos hs)
    (continuousOn_id.mul ((continuousOn_hint s).mono Ioi_subset_Ici_self)) fun z hz => by
      rw [abs_of_nonneg (mul_nonneg hz.le (exp_pos _).le)]
      exact mul_hint_le hs hz.le

/-- Integration by parts: `s ∫₀^∞ z e^{−sz−E(z)} dz = h(s+1)`. -/
lemma mul_integral_mul_hint {s : ℝ} (hs : 0 < s) :
    s * ∫ z in Ioi 0, z * exp (-s * z - E z) = h (s + 1) := by
  have hcont : ContinuousWithinAt (fun z => z * exp (-s * z - E z)) (Ici 0) 0 :=
    (continuousOn_id.mul (continuousOn_hint s)) 0 (mem_Ici.mpr le_rfl)
  have hderiv : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt (fun z => z * exp (-s * z - E z))
      (exp (-(s + 1) * z - E z) - s * (z * exp (-s * z - E z))) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => -s * z - E z) (-s * 1 - Eint z) z :=
      ((hasDerivAt_id' z).const_mul (-s)).sub (hasDerivAt_E hz)
    refine ((hasDerivAt_id' z).mul h1.exp).congr_deriv ?_
    have hm := mul_Eint (ne_of_gt hz)
    rw [show -(s + 1) * z - E z = (-s * z - E z) + -z by ring, exp_add]
    linear_combination (-exp (-s * z - E z)) * hm
  have hint : IntegrableOn
      (fun z => exp (-(s + 1) * z - E z) - s * (z * exp (-s * z - E z))) (Ioi 0) :=
    (integrableOn_hint (by linarith)).sub ((integrableOn_mul_hint hs).const_mul s)
  have hlim : Tendsto (fun z => z * exp (-s * z - E z)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun z => 2 / s * exp (-(s / 2) * z)) atTop (𝓝 0) := by
      have := tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (half_pos hs)))
      simpa using this.const_mul (2 / s)
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_ge_atTop 0] with z hz using mul_nonneg hz (exp_pos _).le
    · filter_upwards [eventually_ge_atTop 0] with z hz using mul_hint_le hs hz
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_sub (integrableOn_hint (by linarith)) ((integrableOn_mul_hint hs).const_mul s),
    integral_const_mul] at key
  simp only [zero_mul, sub_zero] at key
  unfold h
  linarith

/-- (H2), blueprint form: `h'(s) = −∫₀^∞ z e^{−sz−E(z)} dz`. -/
theorem hasDerivAt_h_integral {s : ℝ} (hs : 0 < s) :
    HasDerivAt h (-∫ z in Ioi 0, z * exp (-s * z - E z)) s := by
  have e : -∫ z in Ioi 0, z * exp (-s * z - E z) = -h (s + 1) / s := by
    rw [← mul_integral_mul_hint hs, neg_div, mul_div_cancel_left₀ _ hs.ne']
  rw [e]
  exact hasDerivAt_h hs

/-! ## (H4) `h(1) = e^{−γ}` -/

lemma integrableOn_log_mul_exp_neg : IntegrableOn (fun t => log t * exp (-t)) (Ioi 0) := by
  by_contra hni
  have h1 := eulerMascheroniConstant_eq_neg_integral_log
  rw [integral_undef hni, neg_zero] at h1
  linarith [one_half_lt_eulerMascheroniConstant]

/-- Integration by parts: `E(Z) = (1 − e^{−Z}) log Z − ∫₀^Z log u e^{−u} du`. -/
lemma E_eq_ibp {Z : ℝ} (hZ : 0 < Z) :
    E Z = (1 - exp (-Z)) * log Z - ∫ u in (0 : ℝ)..Z, log u * exp (-u) := by
  have hcont : ContinuousOn (fun u => (1 - exp (-u)) * log u) (Icc 0 Z) := by
    intro u hu
    rcases hu.1.eq_or_lt with rfl | hu0
    · have hml : Tendsto (fun u => u * log u) (𝓝[Icc 0 Z] 0) (𝓝 0) := by
        have := continuous_mul_log.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have : Tendsto (fun u => (1 - exp (-u)) * log u) (𝓝[Icc 0 Z] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hml.norm
        refine eventually_nhdsWithin_of_forall fun x hx => ?_
        have hx0 : 0 ≤ x := hx.1
        have e1 : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
        have e2 := add_one_le_exp (-x)
        simp only [norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - exp (-x)), abs_of_nonneg hx0]
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      simpa [ContinuousWithinAt] using this
    · exact ((continuous_const.sub (continuous_exp.comp continuous_neg)).continuousAt.mul
        (continuousAt_log hu0.ne')).continuousWithinAt
  have hderiv : ∀ x ∈ Ioo 0 Z, HasDerivAt (fun u => (1 - exp (-u)) * log u)
      (log x * exp (-x) + Eint x) x := by
    intro x hx
    have := (((hasDerivAt_neg x).exp).const_sub 1).mul (hasDerivAt_log hx.1.ne')
    convert this using 1
    unfold Eint
    field_simp
  have hint1 : IntervalIntegrable (fun u => log u * exp (-u)) volume 0 Z :=
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (by fun_prop : Continuous fun u : ℝ => exp (-u)).continuousOn
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hZ.le hcont hderiv
    (hint1.add (intervalIntegrable_Eint le_rfl hZ.le))
  rw [intervalIntegral.integral_add hint1 (intervalIntegrable_Eint le_rfl hZ.le)] at this
  simp only [neg_zero, exp_zero, sub_self, log_zero, mul_zero, sub_zero] at this
  rw [E]
  linarith

lemma tendsto_E_sub_log :
    Tendsto (fun Z => E Z - log Z) atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun Z => exp (-Z) * log Z) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
    · filter_upwards [eventually_ge_atTop 1] with Z hZ
      exact mul_nonneg (exp_pos _).le (log_nonneg hZ)
    · filter_upwards [eventually_ge_atTop 1] with Z hZ
      rw [pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith [log_le_sub_one_of_pos (by linarith : 0 < Z)])
        (exp_pos _).le
  have h2 := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_log_mul_exp_neg tendsto_id
  have h3 := h1.neg.sub h2
  rw [eulerMascheroniConstant_eq_neg_integral_log]
  convert h3.congr' ?_ using 2
  · simp
  · filter_upwards [eventually_gt_atTop 0] with Z hZ
    rw [E_eq_ibp hZ, id]
    ring

lemma tendsto_mul_exp_neg_E :
    Tendsto (fun Z => Z * exp (-E Z)) atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  have := (continuous_exp.tendsto _).comp tendsto_E_sub_log.neg
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Z hZ
  simp only [Function.comp_apply, neg_sub]
  rw [exp_sub, exp_log hZ, div_eq_mul_inv, ← exp_neg]

/-- (H4) `h(1) = e^{−γ}`. -/
theorem h_one : h 1 = exp (-eulerMascheroniConstant) := by
  have hd : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt (fun z => z * exp (-E z)) (exp (-1 * z - E z)) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => -E z) (-Eint z) z := (hasDerivAt_E hz).neg
    refine ((hasDerivAt_id' z).mul h1.exp).congr_deriv ?_
    have hm := mul_Eint (ne_of_gt hz)
    rw [show -1 * z - E z = -z + -E z by ring, exp_add]
    linear_combination (-exp (-E z)) * hm
  have hcont : ContinuousWithinAt (fun z => z * exp (-E z)) (Ici 0) 0 := by
    have := continuousOn_E
    exact (by fun_prop : ContinuousOn (fun z => z * exp (-E z)) (Ici 0)) 0 (mem_Ici.mpr le_rfl)
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd (integrableOn_hint one_pos)
    tendsto_mul_exp_neg_E
  rw [h, this]
  simp

end Palprimes.E1
