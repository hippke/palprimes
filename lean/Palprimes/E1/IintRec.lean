import Palprimes.MainTerm.Simplex

/-! # E10: the recursion for `I_t` (E1 blueprint D5) and the delay equations of `Fjr`, `fjr` (D5′)

* `Iint_rec` (D5): `s · I_t(s) = ∫_0^s I_{t-1}(u − 1) du` for `t ≥ 2` and every real `s`;
* `Fjr_dde`, `fjr_dde` (D5′): `s F(s) = 2e^γ + ∫_3^s f(u − 1) du` (`s > 1`) and
  `s f(s) = ∫_2^s F(u − 1) du` (`s ≥ 2`), with `F = Fjr`, `f = fjr`.

Proof of D5. In the coordinates of `Defs.lean` (`w = (u_1, …, u_{t-1})`, `u_t = s − Σ w` the
smallest coordinate) the measure-preserving shear `swapW` of `Simplex.lean` makes `a = u_t` a free
coordinate (Fubini on it). For fixed `a` the scaling `u_i = a v_i` (`i ≤ t − 2`) maps the region of
`I_{t-1}(s/a − 1)` onto the slice, with `u_{t-1} = a · (s/a − 1 − Σ v)` the eliminated coordinate of
`I_{t-1}`. This gives `I_t(s) = ∫_1^∞ a^{-2} I_{t-1}(s/a − 1) da`, and `u = s/a` gives D5. No
permutation of coordinates is needed. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real Filter Topology

namespace Palprimes.E1

open Palprimes.MT

/-! ## Fubini on the last coordinate (copy of `MainTerm/Identify.lean`, kept local for the import depth) -/

lemma snoc_eq_symm' {n : ℕ} (t : ℝ) (v : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm (t, v) = Fin.snoc v t := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_last' t v

lemma integral_snoc_split {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F) :
    (∫ x, F x) = ∫ t : ℝ, ∫ v : Fin n → ℝ, F (Fin.snoc v t) := by
  have hs := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.snoc p.2 p.1)) (volume.prod volume) := by
    have h := (hs.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := F)).2 hF
    rw [← Measure.volume_eq_prod]
    convert h using 1
    funext p
    rcases p with ⟨t, v⟩
    simp only [Function.comp, snoc_eq_symm']
  have h := hs.integral_comp (MeasurableEquiv.measurableEmbedding _) F
  rw [← h, Measure.volume_eq_prod, integral_prod _ (by
    convert hint using 1; funext p; rcases p with ⟨t, v⟩; simp only [snoc_eq_symm'])]
  congr 1; funext t; congr 1; funext v
  rw [snoc_eq_symm']

lemma strictAnti_snoc' {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    StrictAnti (Fin.snoc v t : Fin (n + 1) → ℝ) ↔ StrictAnti v ∧ ∀ i, t < v i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (Fin.castSucc_lt_castSucc_iff.2 hij)
      simpa using this
    · have := h (Fin.castSucc_lt_last i)
      simpa using this
  · rintro ⟨h1, h2⟩ a b hab
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]; exact h1 (Fin.castSucc_lt_castSucc_iff.1 hab)
      · exact absurd hab (not_lt.2 (Fin.le_last _))
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact h2 a'
      · exact absurd hab (lt_irrefl _)

lemma strictAnti_smul {m : ℕ} {a : ℝ} (ha : 0 < a) (v : Fin m → ℝ) :
    StrictAnti (a • v) ↔ StrictAnti v := by
  constructor
  · intro h i j hij
    have := h hij
    simp only [Pi.smul_apply, smul_eq_mul] at this
    nlinarith
  · intro h i j hij
    have := h hij
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith

/-! ## The integrand of `I_t` after the shear and the scaling -/

lemma integrable_Ifun (n : ℕ) (s : ℝ) : Integrable (Ifun n s) :=
  (integrable_boxI n s).mono' (measurable_Ifun n s).aestronglyMeasurable
    (ae_of_all _ fun w => by rw [Real.norm_of_nonneg (Ifun_nonneg _ _ _)]; exact Ifun_le_box le_rfl w)

lemma swapW_snoc {m : ℕ} (c : ℝ) (v : Fin m → ℝ) (a : ℝ) :
    swapW c (Fin.snoc v a : Fin (m + 1) → ℝ) = Fin.snoc v (c - ∑ i, v i - a) := by
  simp only [swapW, Fin.init_snoc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1; ring

lemma lastU_snoc_sub {m : ℕ} (s a : ℝ) (v : Fin m → ℝ) :
    lastU s (Fin.snoc v (s - ∑ i, v i - a) : Fin (m + 1) → ℝ) = a := by
  simp only [lastU, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- `a = u_t` as a free coordinate: `I_{m+2}(s) = ∫_a ∫_v Ifun(v, s − Σ v − a)`. -/
lemma Iint_eq_iter (m : ℕ) (s : ℝ) :
    Iint (m + 2) s = ∫ a : ℝ, ∫ v : Fin m → ℝ, Ifun (m + 1) s (Fin.snoc v (s - ∑ i, v i - a)) := by
  rw [Iint_succ']
  have hmp := measurePreserving_swapW (m := m) s
  have h1 := integral_map (μ := volume) hmp.measurable.aemeasurable
    (f := Ifun (m + 1) s) (measurable_Ifun _ _).aestronglyMeasurable
  rw [hmp.map_eq] at h1
  have hint : Integrable (fun w => Ifun (m + 1) s (swapW s w)) :=
    (hmp.integrable_comp (measurable_Ifun _ _).aestronglyMeasurable).2 (integrable_Ifun _ _)
  rw [h1, integral_snoc_split _ hint]
  simp_rw [swapW_snoc]

/-- The slice at `u_t = a > 1`, scaled by `a`, is the integrand of `I_{m+1}(s/a − 1)`. -/
lemma Ifun_scale {m : ℕ} {s a : ℝ} (ha : 1 < a) (v : Fin m → ℝ) :
    Ifun (m + 1) s (Fin.snoc (a • v) (s - ∑ i, (a • v) i - a)) =
      (a ^ (m + 2))⁻¹ * Ifun m (s / a - 1) v := by
  have ha0 : 0 < a := by linarith
  have hsum : ∑ i, (a • v) i = a * ∑ i, v i := by simp [Pi.smul_apply, Finset.mul_sum]
  have hy : s - ∑ i, (a • v) i - a = a * lastU (s / a - 1) v := by
    rw [hsum, lastU]; field_simp; ring
  unfold Ifun
  rw [lastU_snoc_sub, hy]
  set L := lastU (s / a - 1) v with hL
  have hreg : IRegion (m + 1) s (Fin.snoc (a • v) (a * L)) ↔ IRegion m (s / a - 1) v := by
    have hlast : lastU s (Fin.snoc (a • v) (a * L) : Fin (m + 1) → ℝ) = a := by
      rw [← hy]; exact lastU_snoc_sub s a _
    unfold IRegion
    rw [hlast, strictAnti_snoc', Fin.forall_fin_succ', Fin.forall_fin_succ', strictAnti_smul ha0, ← hL]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨⟨hA, hB⟩, -, -, hD1, hD2⟩
      refine ⟨hA, fun i => ?_, ?_, fun i => ?_⟩
      · have := hD1 i; nlinarith
      · nlinarith
      · have := hB i; nlinarith
    · rintro ⟨hA, hB, hC, hD⟩
      refine ⟨⟨hA, fun i => ?_⟩, ⟨fun i => ?_, ?_⟩, ha, fun i => ?_, ?_⟩
      · have := hD i; nlinarith
      · have := hB i; nlinarith
      · nlinarith
      · have := hB i; nlinarith
      · nlinarith
  by_cases h : IRegion m (s / a - 1) v
  · rw [ite_eq_left (hreg.2 h), ite_eq_left h, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [one_div, one_div, ← mul_inv]
    congr 1
    ring
  · rw [ite_eq_right (fun h' => h (hreg.1 h')), ite_eq_right h, mul_zero]

lemma Ifun_snoc_of_le {m : ℕ} {s a : ℝ} (ha : a ≤ 1) (v : Fin m → ℝ) :
    Ifun (m + 1) s (Fin.snoc v (s - ∑ i, v i - a)) = 0 := by
  unfold Ifun
  rw [ite_eq_right]
  rintro ⟨-, -, h, -⟩
  rw [lastU_snoc_sub] at h
  linarith

/-- The inner integral: `a^{-2} I_{m+1}(s/a − 1)` for `a > 1`, `0` otherwise. -/
lemma inner_eq (m : ℕ) (s a : ℝ) :
    ∫ v : Fin m → ℝ, Ifun (m + 1) s (Fin.snoc v (s - ∑ i, v i - a)) =
      (Set.Ioi 1).indicator (fun a => (a ^ 2)⁻¹ * Iint (m + 1) (s / a - 1)) a := by
  by_cases ha : 1 < a
  · rw [Set.indicator_of_mem ha]
    have ha0 : 0 < a := by linarith
    have h := Measure.integral_comp_smul (μ := (volume : Measure (Fin m → ℝ)))
      (fun v => Ifun (m + 1) s (Fin.snoc v (s - ∑ i, v i - a))) a
    simp only [Module.finrank_fin_fun] at h
    simp_rw [Ifun_scale ha] at h
    rw [integral_const_mul, ← Iint_succ', abs_of_pos (by positivity), smul_eq_mul] at h
    set X := ∫ v : Fin m → ℝ, Ifun (m + 1) s (Fin.snoc v (s - ∑ i, v i - a))
    have hX : X = a ^ m * ((a ^ (m + 2))⁻¹ * Iint (m + 1) (s / a - 1)) := by
      rw [h]; field_simp
    rw [hX, pow_add]
    field_simp
  · rw [Set.indicator_of_notMem ha]
    simp [Ifun_snoc_of_le (not_lt.1 ha)]

/-- `I_{m+2}(s) = ∫_1^∞ a^{-2} I_{m+1}(s/a − 1) da`. -/
lemma Iint_eq_Ioi (m : ℕ) (s : ℝ) :
    Iint (m + 2) s = ∫ a in Set.Ioi 1, (a ^ 2)⁻¹ * Iint (m + 1) (s / a - 1) := by
  rw [Iint_eq_iter]
  simp_rw [inner_eq]
  rw [integral_indicator measurableSet_Ioi]

/-! ## D5 -/

lemma image_mul_inv_Ioi {s : ℝ} (hs : 0 < s) : (fun a => s * a⁻¹) '' Set.Ioi 1 = Set.Ioo 0 s := by
  ext u
  simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha0 : 0 < a := by linarith
    refine ⟨by positivity, ?_⟩
    rw [← div_eq_mul_inv, div_lt_iff₀ ha0]
    nlinarith
  · rintro ⟨h0, hsu⟩
    refine ⟨s / u, ?_, ?_⟩
    · rw [lt_div_iff₀ h0]; linarith
    · field_simp

/-- **D5.** `s · I_t(s) = ∫_0^s I_{t-1}(u − 1) du` for `t ≥ 2` and every real `s`
(for `t = 2` the integrand is `[u > 2]/(u − 1)`, the strict region of `Iint 1`). -/
theorem Iint_rec {t : ℕ} (ht : 2 ≤ t) (s : ℝ) :
    s * Iint t s = ∫ u in (0 : ℝ)..s, Iint (t - 1) (u - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  rcases le_or_gt s 0 with hs | hs
  · rw [Iint_eq_zero (by omega) (by push_cast; linarith), mul_zero]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro u hu
    rw [Set.uIcc_of_ge hs] at hu
    exact Iint_eq_zero (by omega) (by push_cast; linarith [hu.2])
  · rw [intervalIntegral.integral_of_le hs.le, integral_Ioc_eq_integral_Ioo, ← image_mul_inv_Ioi hs]
    have hderiv : ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivWithinAt (fun a => s * a⁻¹) (s * -(x ^ 2)⁻¹) (Set.Ioi 1) x :=
      fun x hx => ((hasDerivAt_inv (by have : (1 : ℝ) < x := hx; linarith)).const_mul s).hasDerivWithinAt
    have hinj : Set.InjOn (fun a : ℝ => s * a⁻¹) (Set.Ioi 1) := by
      intro x _ y _ hxy
      simpa using mul_left_cancel₀ hs.ne' hxy
    rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj, Iint_eq_Ioi,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    have ha0 : 0 < a := by have : (1 : ℝ) < a := ha; linarith
    simp only [smul_eq_mul, mul_neg, abs_neg, abs_mul, abs_of_pos hs, abs_inv, abs_of_pos (pow_pos ha0 2),
      div_eq_mul_inv]
    ring

/-! ## Interval integrability of `u ↦ I_r(u − 1)`, `F(u − 1)`, `f(u − 1)` -/

lemma Iint_one_eq_indicator : Iint 1 = (Set.Ioi 1).indicator (fun x => 1 / x) := by
  funext x
  by_cases hx : 1 < x
  · rw [Set.indicator_of_mem hx, Iint_one hx]
  · rw [Set.indicator_of_notMem hx, Iint_one_of_le (not_lt.1 hx)]

lemma intervalIntegrable_Iint_sub (r : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => Iint r (u - 1)) volume a b := by
  rcases r with _ | _ | n
  · simp [Iint]
  · rw [Iint_one_eq_indicator, intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
    · exact (measure_mono Set.uIoc_subset_uIcc).trans_lt (by rw [Real.volume_interval]; exact ENNReal.ofReal_lt_top) |>.ne
    · exact (((measurable_const.div measurable_id).indicator measurableSet_Ioi).comp
        (measurable_id.sub_const 1)).aestronglyMeasurable
    · refine ae_of_all _ fun u => ?_
      by_cases h : 1 < u - 1
      · simp only [Set.indicator_of_mem (show u - 1 ∈ Set.Ioi 1 from h), Real.norm_eq_abs]
        rw [abs_of_pos (by positivity), div_le_one (by linarith)]
        linarith
      · simp [Set.indicator_of_notMem (show u - 1 ∉ Set.Ioi 1 from h)]
  · exact ((continuous_Iint_two_le n).comp (continuous_sub_right 1)).intervalIntegrable a b

lemma intervalIntegrable_sum_Iint_sub (S : Finset ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => ∑ r ∈ S, Iint r (u - 1)) volume a b := by
  have := IntervalIntegrable.sum S (fun r _ => intervalIntegrable_Iint_sub r a b)
  convert this using 1
  funext u
  simp

lemma intervalIntegrable_Fjr_sub (a b : ℝ) :
    IntervalIntegrable (fun u => Fjr (u - 1)) volume a b := by
  obtain ⟨M, hM⟩ := exists_nat_gt (|a| + |b|)
  refine ((intervalIntegrable_sum_Iint_sub ((Finset.range (M + 1)).filter Odd) a b).const_mul
    (2 * Real.exp Real.eulerMascheroniConstant)).congr ?_
  intro u hu
  have hu' := Set.uIoc_subset_uIcc hu
  rw [Set.mem_uIcc] at hu'
  have : u < M := by
    rcases hu' with h | h <;> linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b, h.2]
  exact (Fjr_eq_sum (by omega) (by push_cast; linarith)).symm

lemma intervalIntegrable_fjr_sub (a b : ℝ) :
    IntervalIntegrable (fun u => fjr (u - 1)) volume a b :=
  (continuous_fjr.comp (continuous_sub_right 1)).intervalIntegrable a b

/-! ## D5′: the delay equations of `Fjr` and `fjr` -/

/-- D5 summed over a finite set of indices `t ≥ 2`. -/
lemma sum_Iint_rec (S : Finset ℕ) (hS : ∀ t ∈ S, 2 ≤ t) (s : ℝ) :
    s * ∑ t ∈ S, Iint t s = ∫ u in (0 : ℝ)..s, ∑ t ∈ S, Iint (t - 1) (u - 1) := by
  rw [Finset.mul_sum, intervalIntegral.integral_finsetSum (fun t _ => intervalIntegrable_Iint_sub _ _ _)]
  exact Finset.sum_congr rfl fun t ht => Iint_rec (hS t ht) s

/-- Odd `t ≥ 3` correspond to even `r = t − 1 ≥ 2`. -/
lemma sum_odd_shift (M : ℕ) (x : ℝ) :
    ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Odd t ∧ 3 ≤ t), Iint (t - 1) x =
      ∑ r ∈ (Finset.range M).filter (fun r => Even r ∧ 2 ≤ r), Iint r x := by
  refine Finset.sum_nbij' (fun t => t - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff, Nat.even_iff] at ht ⊢
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff, Nat.even_iff] at hr ⊢
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff] at ht
    omega
  · intro r _
    simp

/-- Even `t ≥ 2` correspond to odd `r = t − 1`. -/
lemma sum_even_shift (M : ℕ) (x : ℝ) :
    ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint (t - 1) x =
      ∑ r ∈ (Finset.range M).filter Odd, Iint r x := by
  refine Finset.sum_nbij' (fun t => t - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff, Nat.even_iff] at ht ⊢
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Nat.odd_iff, Nat.even_iff] at hr ⊢
    omega
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at ht
    omega
  · intro r _
    simp

/-- The odd indices split into `t = 1` and `t ≥ 3`. -/
lemma sum_odd_split (M : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ (Finset.range (M + 2)).filter Odd, f t =
      f 1 + ∑ t ∈ (Finset.range (M + 2)).filter (fun t => Odd t ∧ 3 ≤ t), f t := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range (M + 2)).filter Odd) (fun t => 3 ≤ t),
    Finset.filter_filter, add_comm]
  congr 1
  have : ((Finset.range (M + 2)).filter Odd).filter (fun t => ¬ 3 ≤ t) = {1} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.odd_iff]
    omega
  rw [this, Finset.sum_singleton]

/-- **D5′ for `F`.** `s F(s) = 2e^γ + ∫_3^s f(u − 1) du` for `s > 1` (for `1 < s ≤ 3` the
integral vanishes and this is `Fjr_eq`). -/
theorem Fjr_dde {s : ℝ} (hs : 1 < s) :
    s * Fjr s = 2 * Real.exp Real.eulerMascheroniConstant + ∫ u in (3 : ℝ)..s, fjr (u - 1) := by
  set c := 2 * Real.exp Real.eulerMascheroniConstant with hc
  obtain ⟨M, hM⟩ := exists_nat_gt s
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := hs.trans hM
    exact_mod_cast this.le
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  -- `s F(s) = c + ∫_0^s f(u − 1) du`
  have key : s * Fjr s = c + ∫ u in (0 : ℝ)..s, fjr (u - 1) := by
    rw [Fjr_eq_sum (M := K + 2) (by omega) (by push_cast at hM ⊢; linarith), sum_odd_split,
      mul_add, mul_add, Iint_one hs, show s * (c * ∑ t ∈ (Finset.range (K + 2)).filter (fun t => Odd t ∧ 3 ≤ t), Iint t s) =
        c * (s * ∑ t ∈ (Finset.range (K + 2)).filter (fun t => Odd t ∧ 3 ≤ t), Iint t s) by ring,
      sum_Iint_rec _ (fun t ht => by simp only [Finset.mem_filter] at ht; omega), ← intervalIntegral.integral_const_mul]
    congr 1
    · rw [hc]; field_simp
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith)] at hu
      rw [sum_odd_shift, fjr_eq_sum (M := K + 1) (by omega) (by push_cast at hM ⊢; linarith [hu.2])]
  rw [key, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_fjr_sub 0 3)
    (intervalIntegrable_fjr_sub 3 s)]
  have h0 : ∫ u in (0 : ℝ)..3, fjr (u - 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact fjr_le_two (by linarith [hu.2])
  rw [h0, zero_add]

/-- **D5′ for `f`.** `s f(s) = ∫_2^s F(u − 1) du` for `s ≥ 2`. -/
theorem fjr_dde {s : ℝ} (hs : 2 ≤ s) :
    s * fjr s = ∫ u in (2 : ℝ)..s, Fjr (u - 1) := by
  set c := 2 * Real.exp Real.eulerMascheroniConstant with hc
  obtain ⟨M, hM⟩ := exists_nat_gt s
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := by linarith
    exact_mod_cast this.le
  have key : s * fjr s = ∫ u in (0 : ℝ)..s, Fjr (u - 1) := by
    rw [fjr_eq_sum (M := M + 1) (by omega) (by push_cast; linarith),
      show s * (c * ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint t s) =
        c * (s * ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint t s) by ring,
      sum_Iint_rec _ (fun t ht => by simp only [Finset.mem_filter] at ht; omega), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by linarith)] at hu
    rw [sum_even_shift, Fjr_eq_sum (M := M) hM1 (by linarith [hu.2])]
  rw [key, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_Fjr_sub 0 2)
    (intervalIntegrable_Fjr_sub 2 s)]
  have h0 : ∫ u in (0 : ℝ)..2, Fjr (u - 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact Fjr_le_one (by linarith [hu.2])
  rw [h0, zero_add]

end Palprimes.E1
