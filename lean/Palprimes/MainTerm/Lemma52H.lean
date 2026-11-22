import Palprimes.MainTerm.Lemma52

/-! # `h_2(x, 1)` in one variable and a volume bound for `h_4(x, 1)`

DOSSIER (r160) Lemmas 3.6–3.8:
* `hk2_eq_zero`: `h_4(x, 1) = 0` for `x ≥ 1/6`; `hk1_eq_zero`: `h_2(x, 1) = 0` for `x ≥ 1/4`;
* `hk2_le`: `h_4(x, 1) ≤ (1 − 6x)^4 / (576 x^5)` for `0 < x < 1/6` (the ordered simplex has volume
  `w^4/(4!)^2`, `simplex_sorted_volume`);
* `hk1_formula`: the one-variable formula of Lemma 3.7 for `0 < x < 1/4`. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real Filter

namespace Palprimes.MT

/-! ## Vanishing -/

lemma hk_eq_zero_of_le {k : ℕ} {x : ℝ} (hkx : (2 * k + 2 : ℝ) * x ≥ 1) : hk k x = 0 := by
  classical
  unfold hk
  refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
  simp only [Pi.zero_apply]
  split_ifs with h
  · exfalso
    have hl := hRegion_zvec_gt h (Fin.last _)
    simp only [zvec_last] at hl
    have hsum : ((2 * k : ℕ) : ℝ) * x ≤ ∑ i, v i := by
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h.2.1 i).le)
      simpa [mul_comm] using this
    push_cast at hsum
    nlinarith
  · rfl

theorem hk1_eq_zero {x : ℝ} (hx : 1 / 4 ≤ x) : hk 1 x = 0 :=
  hk_eq_zero_of_le (k := 1) (by norm_num; linarith)

theorem hk2_eq_zero {x : ℝ} (hx : 1 / 6 ≤ x) : hk 2 x = 0 :=
  hk_eq_zero_of_le (k := 2) (by norm_num; linarith)

/-! ## Simplex volumes -/

/-- The open simplex `{y > 0, Σ y < w}`. -/
def SimpS (n : ℕ) (w : ℝ) : Set (Fin n → ℝ) := {y | (∀ i, 0 < y i) ∧ ∑ i, y i < w}

lemma measurableSet_SimpS (n : ℕ) (w : ℝ) : MeasurableSet (SimpS n w) := by
  have hs : Measurable fun y : Fin n → ℝ => ∑ i, y i := Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact measurableSet_setOfPred.mpr ((Measurable.forall fun i =>
    measurable_lt_fun measurable_const (measurable_pi_apply i)).and (measurable_lt_fun hs measurable_const))

lemma integral_simplex_step (n : ℕ) (w : ℝ) :
    ∫ t, (if 0 < t then (if 0 < w - t then (w - t) ^ n / n.factorial else 0) else 0) =
      if 0 < w then w ^ (n + 1) / (n + 1).factorial else 0 := by
  by_cases hw : 0 < w
  · rw [if_pos hw]
    have hfun : (fun t : ℝ => if 0 < t then (if 0 < w - t then (w - t) ^ n / n.factorial else 0) else 0) =
        Set.indicator (Set.Ioo 0 w) (fun t => (w - t) ^ n / n.factorial) := by
      funext t
      simp only [Set.indicator, Set.mem_Ioo]
      by_cases h1 : 0 < t <;> by_cases h2 : t < w <;> simp [h1, h2, sub_pos]
    rw [hfun, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hw.le, intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun t => t ^ n) w, integral_pow]
    simp only [sub_self, sub_zero]
    rw [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ]
    push_cast
    field_simp
  · rw [if_neg hw]
    refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
    simp only [Pi.zero_apply]
    split_ifs with h1 h2
    · exfalso; linarith
    · rfl
    · rfl

theorem volume_SimpS (n : ℕ) (w : ℝ) :
    volume (SimpS n w) = ENNReal.ofReal (if 0 < w then w ^ n / n.factorial else 0) := by
  induction n generalizing w with
  | zero =>
    by_cases hw : 0 < w
    · have : SimpS 0 w = Set.univ := by
        ext y; simp [SimpS, hw]
      rw [this, if_pos hw, MeasureTheory.volume_pi, Measure.pi_of_empty]
      simp
    · have : SimpS 0 w = ∅ := by
        ext y; simp [SimpS, hw]
      rw [this, if_neg hw]; simp
  | succ n ih =>
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hE : MeasurePreserving E volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    set S' : Set (ℝ × (Fin n → ℝ)) := {p | 0 < p.1 ∧ p.2 ∈ SimpS n (w - p.1)} with hS'
    have hS'm : MeasurableSet S' := by
      have hs : Measurable fun p : ℝ × (Fin n → ℝ) => ∑ i, p.2 i :=
        Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd
      refine measurableSet_setOfPred.mpr ((measurable_lt_fun measurable_const measurable_fst).and ?_)
      refine (Measurable.forall fun i => measurable_lt_fun measurable_const
        ((measurable_pi_apply i).comp measurable_snd)).and ?_
      exact measurable_lt_fun hs (measurable_const.sub measurable_fst)
    have hEy : ∀ y, E y = (y 0, fun j => y j.succ) := by
      intro y
      simp only [E, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    have hpre : SimpS (n + 1) w = E ⁻¹' S' := by
      ext y
      simp only [Set.mem_preimage, hEy, hS', SimpS, Set.mem_setOf_eq, Fin.forall_fin_succ,
        Fin.sum_univ_succ]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, by linarith⟩
      · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, by linarith⟩
    rw [hpre, hE.measure_preimage hS'm.nullMeasurableSet, Measure.prod_apply hS'm]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' S') =
        ENNReal.ofReal (if 0 < t then (if 0 < w - t then (w - t) ^ n / n.factorial else 0) else 0) := by
      intro t
      by_cases ht : 0 < t
      · have : Prod.mk t ⁻¹' S' = SimpS n (w - t) := by
          ext y; simp [hS', ht]
        rw [this, ih, if_pos ht]
      · have : Prod.mk t ⁻¹' S' = ∅ := by
          ext y; simp [hS', ht]
        rw [this, if_neg ht]; simp
    simp_rw [hslice]
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_simplex_step]
    · -- integrability
      by_cases hw : 0 < w
      · have hfun : (fun t : ℝ => if 0 < t then (if 0 < w - t then (w - t) ^ n / n.factorial else 0) else 0) =
            Set.indicator (Set.Ioo 0 w) (fun t => (w - t) ^ n / n.factorial) := by
          funext t
          simp only [Set.indicator, Set.mem_Ioo]
          by_cases h1 : 0 < t <;> by_cases h2 : t < w <;> simp [h1, h2, sub_pos]
        rw [hfun, integrable_indicator_iff measurableSet_Ioo]
        exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioo_subset_Icc_self
      · have hfun : (fun t : ℝ => if 0 < t then (if 0 < w - t then (w - t) ^ n / n.factorial else 0) else 0) = 0 := by
          funext t
          simp only [Pi.zero_apply]
          split_ifs with h1 h2
          · exfalso; linarith
          · rfl
          · rfl
        rw [hfun]; exact integrable_zero _ _ _
    · refine ae_of_all _ fun t => ?_
      simp only [Pi.zero_apply]
      split_ifs with h1 h2
      · exact div_nonneg (pow_nonneg (by linarith) _) (by positivity)
      · exact le_rfl
      · exact le_rfl

lemma volume_eq_null {n : ℕ} {i j : Fin n} (hij : i ≠ j) : volume {y : Fin n → ℝ | y i = y j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : L ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp [L, Pi.single_apply, hij.symm] at this
  have := volume_linear_level_null L hL 0
  convert this using 2
  simp [L, sub_eq_zero]

lemma ae_injective_volume {n : ℕ} : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), Function.Injective y := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), {y : Fin n → ℝ | y i = y j}) ?_ ?_
  · intro y hy
    simp only [Set.mem_setOf_eq, Function.Injective, not_forall] at hy
    obtain ⟨i, j, h, hne⟩ := hy
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, h⟩
  · exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => volume_eq_null hij

/-- The ordered part of the simplex has `1/n!` of its volume. -/
theorem simplex_sorted_volume (n : ℕ) {w : ℝ} (hw : 0 < w) :
    volume.real {y : Fin n → ℝ | StrictAnti y ∧ y ∈ SimpS n w} = w ^ n / (n.factorial : ℝ) ^ 2 := by
  classical
  have hS := volume_SimpS n w
  rw [if_pos hw] at hS
  have hfin : volume (SimpS n w) ≠ ⊤ := by rw [hS]; exact ENNReal.ofReal_ne_top
  have hint : Integrable ((SimpS n w).indicator (1 : (Fin n → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff (measurableSet_SimpS n w)]
    exact integrableOn_const hfin
  have hsort := integral_sort volume measurePreserving_permE_volume ae_injective_volume hint
  have hsym : ∀ (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), (y ∘ σ ∈ SimpS n w ↔ y ∈ SimpS n w) := by
    intro y σ
    simp only [SimpS, Set.mem_setOf_eq, Function.comp]
    rw [Equiv.sum_comp σ y]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun i => by simpa using h1 (σ.symm i), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i => h1 _, h2⟩
  have hrhs : ∀ y : Fin n → ℝ, (if StrictAnti y then ∑ σ : Equiv.Perm (Fin n), (SimpS n w).indicator 1 (y ∘ σ) else 0) =
      (n.factorial : ℝ) * {y : Fin n → ℝ | StrictAnti y ∧ y ∈ SimpS n w}.indicator 1 y := by
    intro y
    simp only [Set.indicator, Set.mem_setOf_eq, hsym]
    split_ifs with h1 h2 h3 <;> simp_all [Fintype.card_perm]
  simp_rw [hrhs] at hsort
  rw [integral_const_mul, integral_indicator_one (measurableSet_SimpS n w),
    integral_indicator_one] at hsort
  · rw [Measure.real, hS, ENNReal.toReal_ofReal (by positivity)] at hsort
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff (by positivity), sq, ← mul_assoc]
    have h2 : volume.real {y : Fin n → ℝ | StrictAnti y ∧ y ∈ SimpS n w} * n.factorial = w ^ n / n.factorial := by
      rw [hsort]; ring
    rw [h2, div_mul_cancel₀ _ hf]
  · exact measurableSet_setOfPred.mpr (measurable_strictAnti.and
      (measurableSet_setOfPred.mp (measurableSet_SimpS n w)))

/-! ## The volume bound for `h_4` -/

theorem hk2_le {x : ℝ} (hx : 0 < x) (hx6 : x < 1 / 6) :
    hk 2 x ≤ (1 - 6 * x) ^ 4 / (576 * x ^ 5) := by
  classical
  set T' : Set (Fin 4 → ℝ) := {v | StrictAnti v ∧ (∀ i, x < v i) ∧ ∑ i, v i < 1 - 2 * x} with hT'
  set T : Set (Fin 4 → ℝ) := {y | StrictAnti y ∧ y ∈ SimpS 4 (1 - 6 * x)} with hT
  have hTm : MeasurableSet T := measurableSet_setOfPred.mpr (measurable_strictAnti.and
      (measurableSet_setOfPred.mp (measurableSet_SimpS 4 _)))
  have hpre : T' = (fun v => v + (fun _ => -x)) ⁻¹' T := by
    ext v
    simp only [hT', hT, SimpS, Set.mem_setOf_eq, Set.mem_preimage, Pi.add_apply]
    have hsum : ∑ i, (v i + -x) = ∑ i, v i - 4 * x := by
      rw [Finset.sum_add_distrib]; simp; ring
    have hSA : StrictAnti (fun i => v i + -x) ↔ StrictAnti v := by
      constructor
      · intro h i j hij; have := h hij; simp only at this; linarith
      · intro h i j hij; have := h hij; simp only; linarith
    rw [hsum]
    change _ ↔ StrictAnti (fun i => v i + -x) ∧ _
    rw [hSA]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun i => by linarith [h2 i], by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun i => by linarith [h2 i], by linarith⟩
  have hvolT' : volume.real T' = (1 - 6 * x) ^ 4 / 576 := by
    rw [hpre, Measure.real, measure_preimage_add_right, ← Measure.real,
      simplex_sorted_volume 4 (by linarith)]
    norm_num [Nat.factorial]
  have hT'm : MeasurableSet T' := by
    rw [hpre]; exact hTm.preimage (measurable_id.add measurable_const)
  have hT'fin : volume T' ≠ ⊤ := by
    rw [hpre, measure_preimage_add_right]
    exact ne_top_of_le_ne_top (by rw [volume_SimpS]; exact ENNReal.ofReal_ne_top)
      (measure_mono fun y hy => hy.2)
  -- pointwise bound
  have hbound : ∀ v : Fin (2 * 2) → ℝ,
      (if HRegion 2 x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) ≤ T'.indicator (fun _ => 1 / x ^ 5) v := by
    intro v
    split_ifs with h
    · have hl := hRegion_zvec_gt h (Fin.last _)
      simp only [zvec_last] at hl
      have hvT : v ∈ T' := ⟨h.1, h.2.1, by linarith⟩
      rw [Set.indicator_of_mem hvT]
      have hp : x ^ 4 ≤ ∏ i, v i := by
        have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => x) (g := v)
          (h0 := fun i _ => hx.le) (h1 := fun i _ => (h.2.1 i).le)
        simpa using this
      have : x ^ 5 ≤ (∏ i, v i) * (1 - x - ∑ i, v i) := by
        rw [pow_succ]; exact mul_le_mul hp hl.le hx.le (le_trans (by positivity) hp)
      exact one_div_le_one_div_of_le (by positivity) this
    · exact Set.indicator_nonneg (fun _ _ => by positivity) v
  have hnn : ∀ v : Fin (2 * 2) → ℝ, 0 ≤ (if HRegion 2 x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) := by
    intro v
    split_ifs with h
    · have hl := hRegion_zvec_gt h (Fin.last _)
      simp only [zvec_last] at hl
      have : 0 < ∏ i, v i := Finset.prod_pos fun i _ => lt_trans hx (h.2.1 i)
      have : 0 < 1 - x - ∑ i, v i := by linarith
      positivity
    · exact le_rfl
  have hint : Integrable (T'.indicator (fun _ : Fin 4 → ℝ => 1 / x ^ 5)) := by
    rw [integrable_indicator_iff hT'm]
    exact integrableOn_const hT'fin
  unfold hk
  calc (∫ v : Fin (2 * 2) → ℝ, if HRegion 2 x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0)
      ≤ ∫ v : Fin 4 → ℝ, T'.indicator (fun _ => 1 / x ^ 5) v :=
        integral_mono_of_nonneg (ae_of_all _ hnn) hint (ae_of_all _ hbound)
    _ = (1 - 6 * x) ^ 4 / (576 * x ^ 5) := by
        rw [integral_indicator hT'm, setIntegral_const, smul_eq_mul, hvolT']
        field_simp

/-! ## `h_2(x, 1)` in one variable (DOSSIER Lemma 3.7) -/

/-- First integrand of Lemma 3.7 (on `1/4 < x₁ < (1 − x)/3`). -/
noncomputable def h2f1 (x a : ℝ) : ℝ :=
  (Real.log (a / (1 - x - 2 * a)) - Real.log ((1 - a) / (2 - 3 * x - 2 * a))) / (a * (1 - x - a))

/-- Second integrand of Lemma 3.7 (on `(1 − x)/3 < x₁ < 1 − 3x`). -/
noncomputable def h2f2 (x a : ℝ) : ℝ :=
  Real.log ((2 - 3 * x - 2 * a) / (1 - a)) / (a * (1 - x - a))

lemma integral_inv_mul_sub {A lo hi : ℝ} (h0 : 0 < lo) (hlh : lo ≤ hi) (hA : hi < A) :
    ∫ b in lo..hi, 1 / (b * (A - b)) =
      (Real.log (hi / (A - hi)) - Real.log (lo / (A - lo))) / A := by
  have hApos : 0 < A := by linarith
  have hderiv : ∀ b ∈ Set.uIcc lo hi,
      HasDerivAt (fun b => (Real.log b - Real.log (A - b)) / A) (1 / (b * (A - b))) b := by
    intro b hb
    rw [Set.uIcc_of_le hlh] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb0 : 0 < b := by linarith
    have hAb : 0 < A - b := by linarith
    have h1 := Real.hasDerivAt_log hb0.ne'
    have h2 := ((hasDerivAt_id b).const_sub A).log hAb.ne'
    have := (h1.sub h2).div_const A
    exact this.congr_deriv (by simp only [id]; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
    ring
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hlh]
    refine ContinuousOn.div continuousOn_const
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id))) ?_
    intro b ⟨hb1, hb2⟩
    have h1 : 0 < b := by linarith
    have h2 : 0 < A - b := by linarith
    exact (mul_pos h1 h2).ne'

/-- The two-variable integrand of `h_2(x, 1)`. -/
noncomputable def H2 (x a b : ℝ) : ℝ :=
  open Classical in
  if b < a ∧ x < a ∧ x < b ∧ a < 1 ∧ b < 1 ∧ 1 < a + 3 * b ∧ b < 1 - x - (a + b) then
    1 / (a * b * (1 - x - (a + b))) else 0

lemma hk1_integrand (x : ℝ) (v : Fin 2 → ℝ) :
    (open Classical in if HRegion 1 x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) =
      H2 x (v 0) (v 1) := by
  classical
  have hsa : StrictAnti v ↔ v 1 < v 0 := by
    rw [Fin.strictAnti_iff_succ_lt]
    constructor
    · intro h; exact h 0
    · intro h i; fin_cases i; exact h
  have c0 : chainX x v 0 = v 0 := by simp [chainX]
  have c1 : chainX x v 1 = v 1 := by simp [chainX]
  have hs : (∑ i ∈ Finset.range (2 * 1 - 1), chainX x v i) = v 0 := by
    norm_num [c0]
  have hsum : ∑ i, v i = v 0 + v 1 := Fin.sum_univ_two v
  have hvac : ∀ P : ℕ → Prop, (∀ j : ℕ, 1 ≤ j → j < 1 → P j) := fun P j h1 h2 => absurd h2 (by omega)
  have hiff : HRegion 1 x v ↔ (v 1 < v 0 ∧ x < v 0 ∧ x < v 1 ∧ v 0 < 1 ∧ v 1 < 1 ∧ 1 < v 0 + 3 * v 1 ∧
      v 1 < 1 - x - (v 0 + v 1)) := by
    unfold HRegion
    rw [hsa, Fin.forall_fin_two, Fin.forall_fin_two, show 2 * 1 - 1 = 1 from rfl, hs, c1, hsum]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, -, h6, h7⟩; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, hvac _, h6, h7⟩
  unfold H2
  rw [Fin.prod_univ_two, hsum]
  by_cases h : HRegion 1 x v
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

lemma hk1_eq_iter {x : ℝ} (hx : 0 < x) : hk 1 x = ∫ a, ∫ b, H2 x a b := by
  classical
  have hint0 : Integrable (fun v : Fin (2 * 1) → ℝ => gH 1 x (zvec (1 - x) v)) :=
    (integrable_smeas_iff (1 - x)).mp (integrable_gH hx (1 - x))
  have hpt : ∀ v : Fin (2 * 1) → ℝ, gH 1 x (zvec (1 - x) v) = H2 x (v 0) (v 1) := by
    intro v
    rw [← hk1_integrand x v]
    have hiff : HReg 1 x (zvec (1 - x) v) ↔ HRegion 1 x v := by
      simp only [HReg, zvec_castSucc]
      exact ⟨fun h => h.2, fun h => ⟨hRegion_zvec_gt h, h⟩⟩
    unfold gH
    by_cases h : HRegion 1 x v
    · rw [if_pos h, if_pos (hiff.mpr h), prod_zvec]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  have hint : Integrable (fun v : Fin 2 → ℝ => H2 x (v 0) (v 1)) := by
    convert hint0 using 1
    funext v; exact (hpt v).symm
  have hMP := volume_preserving_finTwoArrow ℝ
  have hint2 : Integrable (fun p : ℝ × ℝ => H2 x p.1 p.2) (volume.prod volume) := by
    have := (hMP.symm.integrable_comp_emb (MeasurableEquiv.finTwoArrow).symm.measurableEmbedding).mpr hint
    convert this using 1
    funext p
    simp [MeasurableEquiv.finTwoArrow_symm_apply]
  rw [hk_eq_gH]
  simp_rw [hpt]
  rw [← integral_prod (fun p : ℝ × ℝ => H2 x p.1 p.2) hint2]
  have := hMP.integral_comp' (fun p : ℝ × ℝ => H2 x p.1 p.2)
  exact this

lemma inner_H2 {x a : ℝ} (hx : 0 < x) (hx4 : x < 1 / 4) :
    ∫ b, H2 x a b = (Set.Ioo (1 / 4) ((1 - x) / 3)).indicator (h2f1 x) a +
      (Set.Ico ((1 - x) / 3) (1 - 3 * x)).indicator (h2f2 x) a := by
  classical
  set A := 1 - x - a with hA
  -- the generic evaluation on an interval `lo < b < hi`
  have heval : ∀ lo hi : ℝ, 0 < lo → lo ≤ hi → hi < A → 0 < a →
      (∀ b, H2 x a b = (Set.Ioo lo hi).indicator (fun b => (1 / a) * (1 / (b * (A - b)))) b) →
      ∫ b, H2 x a b = (1 / a) * ((Real.log (hi / (A - hi)) - Real.log (lo / (A - lo))) / A) := by
    intro lo hi h0 hlh hhA ha hH
    simp_rw [hH]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hlh, intervalIntegral.integral_const_mul,
      integral_inv_mul_sub h0 hlh hhA]
  by_cases h1 : 1 / 4 < a ∧ a < (1 - x) / 3
  · obtain ⟨h1a, h1b⟩ := h1
    have ha : 0 < a := by linarith
    rw [Set.indicator_of_mem (show a ∈ Set.Ioo (1 / 4) ((1 - x) / 3) from ⟨h1a, h1b⟩),
      Set.indicator_of_notMem (show a ∉ Set.Ico ((1 - x) / 3) (1 - 3 * x) from fun h => by linarith [h.1]),
      add_zero]
    rw [heval ((1 - a) / 3) a (by linarith) (by linarith) (by linarith) ha]
    · unfold h2f1
      have e1 : (1 - a) / 3 / (A - (1 - a) / 3) = (1 - a) / (2 - 3 * x - 2 * a) := by
        rw [hA]; field_simp; ring
      have e2 : a / (A - a) = a / (1 - x - 2 * a) := by rw [hA]; ring_nf
      rw [e1, e2, hA]
      field_simp
    · intro b
      unfold H2
      simp only [Set.indicator, Set.mem_Ioo]
      by_cases hb : (1 - a) / 3 < b ∧ b < a
      · rw [if_pos hb, if_pos ⟨hb.2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩]
        rw [hA, one_div_mul_one_div]; congr 1; ring
      · rw [if_neg hb, if_neg]
        rintro ⟨c1, -, -, -, -, c6, -⟩
        exact hb ⟨by linarith, c1⟩
  by_cases h2 : (1 - x) / 3 ≤ a ∧ a < 1 - 3 * x
  · obtain ⟨h2a, h2b⟩ := h2
    have ha : 0 < a := by linarith
    rw [Set.indicator_of_notMem (show a ∉ Set.Ioo (1 / 4) ((1 - x) / 3) from fun h => by linarith [h.2]),
      Set.indicator_of_mem (show a ∈ Set.Ico ((1 - x) / 3) (1 - 3 * x) from ⟨h2a, h2b⟩), zero_add]
    rw [heval ((1 - a) / 3) (A / 2) (by linarith) (by rw [hA]; linarith) (by rw [hA]; linarith) ha]
    · unfold h2f2
      have e1 : (1 - a) / 3 / (A - (1 - a) / 3) = (1 - a) / (2 - 3 * x - 2 * a) := by
        rw [hA]; field_simp; ring
      have e2 : A / 2 / (A - A / 2) = 1 := by
        have : A ≠ 0 := by rw [hA]; linarith
        field_simp; ring
      have e3 : Real.log ((2 - 3 * x - 2 * a) / (1 - a)) = - Real.log ((1 - a) / (2 - 3 * x - 2 * a)) := by
        rw [← Real.log_inv, inv_div]
      rw [e1, e2, Real.log_one, e3, hA]
      field_simp
      ring
    · intro b
      unfold H2
      simp only [Set.indicator, Set.mem_Ioo]
      by_cases hb : (1 - a) / 3 < b ∧ b < A / 2
      · rw [if_pos hb, if_pos ⟨by rw [hA] at hb; linarith, by linarith, by linarith, by linarith,
          by rw [hA] at hb; linarith, by linarith, by rw [hA] at hb; linarith⟩]
        rw [hA, one_div_mul_one_div]; congr 1; ring
      · rw [if_neg hb, if_neg]
        rintro ⟨-, -, -, -, -, c6, c7⟩
        exact hb ⟨by linarith, by rw [hA]; linarith⟩
  -- outside: the region is empty
  rw [Set.indicator_of_notMem (show a ∉ Set.Ioo (1 / 4) ((1 - x) / 3) from fun h => h1 h),
    Set.indicator_of_notMem (show a ∉ Set.Ico ((1 - x) / 3) (1 - 3 * x) from fun h => h2 h), add_zero]
  refine integral_eq_zero_of_ae (ae_of_all _ fun b => ?_)
  simp only [Pi.zero_apply]
  unfold H2
  rw [if_neg]
  rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩
  by_cases ha : a ≤ 1 / 4
  · linarith
  · push_neg at ha
    have : 1 - 3 * x ≤ a := by
      by_contra hc; push_neg at hc
      by_cases hh : a < (1 - x) / 3
      · exact h1 ⟨ha, hh⟩
      · push_neg at hh; exact h2 ⟨hh, hc⟩
    linarith

/-- **DOSSIER Lemma 3.7**: `h_2(x, 1)` as a one-variable integral, `0 < x < 1/4`. -/
theorem hk1_formula {x : ℝ} (hx : 0 < x) (hx4 : x < 1 / 4) :
    hk 1 x = (∫ a in (1 / 4)..((1 - x) / 3), h2f1 x a) + ∫ a in ((1 - x) / 3)..(1 - 3 * x), h2f2 x a := by
  have hle1 : (1 : ℝ) / 4 ≤ (1 - x) / 3 := by linarith
  have hle2 : (1 - x) / 3 ≤ 1 - 3 * x := by linarith
  -- continuity of the integrands on the closed ranges
  have hd : ∀ a : ℝ, ContinuousAt (fun a : ℝ => a * (1 - x - a)) a := fun a =>
    continuousAt_id.mul (continuousAt_const.sub continuousAt_id)
  have hc1 : ContinuousOn (h2f1 x) (Set.Icc (1 / 4) ((1 - x) / 3)) := by
    intro a ⟨ha1, ha2⟩
    have p1 : 0 < a := by linarith
    have p2 : 0 < 1 - x - 2 * a := by linarith
    have p3 : 0 < 1 - a := by linarith
    have p4 : 0 < 2 - 3 * x - 2 * a := by linarith
    have p5 : 0 < 1 - x - a := by linarith
    have hl1 : ContinuousAt (fun a : ℝ => Real.log (a / (1 - x - 2 * a))) a :=
      (continuousAt_id.div (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) p2.ne').log
        (div_pos p1 p2).ne'
    have hl2 : ContinuousAt (fun a : ℝ => Real.log ((1 - a) / (2 - 3 * x - 2 * a))) a :=
      ((continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) p4.ne').log (div_pos p3 p4).ne'
    exact ((hl1.sub hl2).div (hd a) (mul_pos p1 p5).ne').continuousWithinAt
  have hc2 : ContinuousOn (h2f2 x) (Set.Icc ((1 - x) / 3) (1 - 3 * x)) := by
    intro a ⟨ha1, ha2⟩
    have p1 : 0 < a := by linarith
    have p3 : 0 < 1 - a := by linarith
    have p4 : 0 < 2 - 3 * x - 2 * a := by linarith
    have p5 : 0 < 1 - x - a := by linarith
    have hl : ContinuousAt (fun a : ℝ => Real.log ((2 - 3 * x - 2 * a) / (1 - a))) a :=
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).div
        (continuousAt_const.sub continuousAt_id) p3.ne').log (div_pos p4 p3).ne'
    exact (hl.div (hd a) (mul_pos p1 p5).ne').continuousWithinAt
  have hi1 : IntegrableOn (h2f1 x) (Set.Ioo (1 / 4) ((1 - x) / 3)) :=
    (hc1.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hi2 : IntegrableOn (h2f2 x) (Set.Ico ((1 - x) / 3) (1 - 3 * x)) :=
    (hc2.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  rw [hk1_eq_iter hx]
  simp_rw [inner_H2 hx hx4]
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioo).mpr hi1)
      ((integrable_indicator_iff measurableSet_Ico).mpr hi2),
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ico,
    intervalIntegral.integral_of_le hle1, intervalIntegral.integral_of_le hle2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]

end Palprimes.MT
