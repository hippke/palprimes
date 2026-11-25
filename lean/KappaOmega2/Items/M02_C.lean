import KappaOmega2.Items.M02_R

/-! # M02 helpers, part C: step-function Riemann sums, continuity of `Â`, the identity for `c_η`. -/

namespace KappaOmega2

open Finset Palprimes MeasureTheory

set_option linter.style.longLine false

/-- Integrability of `G v / v` on `[0, 1]` for bounded `G` vanishing below `a > 0`. -/
lemma m02_intble2 (G : ℝ → ℝ) (hG : AEStronglyMeasurable G (volume.restrict (Set.uIoc 0 1))) (M a : ℝ)
    (hM : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |G v| ≤ M) (ha : 0 < a) (h0 : ∀ v, v < a → G v = 0) :
    IntervalIntegrable (fun v => G v / v) volume 0 1 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 1 ⟨one_pos, le_rfl⟩)
  apply IntervalIntegrable.mono_fun' (g := fun _ => M / a) intervalIntegrable_const
  · have h := hG.mul (measurable_inv.aestronglyMeasurable (μ := volume.restrict (Set.uIoc 0 1)))
    have e : (G * Inv.inv : ℝ → ℝ) = fun v => G v / v := by funext v; simp [div_eq_mul_inv]
    rw [e] at h; exact h
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro v hv
    rw [Set.uIoc_of_le zero_le_one] at hv
    simp only [Real.norm_eq_abs]
    by_cases hva : v < a
    · rw [h0 v hva]; simp only [zero_div, abs_zero]; positivity
    · push_neg at hva
      have hv0 : 0 < v := hv.1
      rw [abs_div, abs_of_pos hv0, div_le_div_iff₀ hv0 ha]
      exact mul_le_mul (hM v hv) hva ha.le hM0

lemma m02_F_aesm (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc 0 1)) :
    AEStronglyMeasurable F (volume.restrict (Set.uIoc 0 1)) := by
  have := hF.aestronglyMeasurable (μ := volume) measurableSet_Icc
  refine this.mono_measure (Measure.restrict_mono ?_ le_rfl)
  rw [Set.uIoc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self

/-- The piece integral against a continuous weight. -/
lemma m02_int_pieceF (a m : ℝ) (ha : 0 < a) (F : ℝ → ℝ) :
    ∫ v in (0 : ℝ)..1, (if a ≤ v ∧ v < m then (1 : ℝ) else 0) * F v / v =
      if a < min m 1 then ∫ v in a..min m 1, F v / v else 0 := by
  classical
  set b' := min m 1 with hb'
  have hb'1 : b' ≤ 1 := min_le_right _ _
  have hb'm : b' ≤ m := min_le_left _ _
  have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0 : ℝ) 1 →
      (if a ≤ v ∧ v < m then (1 : ℝ) else 0) * F v / v = Set.indicator (Set.Ioc a b') (fun v => F v / v) v := by
    have h1 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ a := by rw [ae_iff]; simp [measure_singleton]
    have h2 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ m := by rw [ae_iff]; simp [measure_singleton]
    filter_upwards [h1, h2] with v hva hvm hv
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hv
    simp only [Set.indicator, Set.mem_Ioc]
    split_ifs with hA hB hB
    · ring
    · exfalso; apply hB
      exact ⟨lt_of_le_of_ne hA.1 (Ne.symm hva), le_min hA.2.le hv.2⟩
    · exfalso
      exact hA ⟨hB.1.le, lt_of_le_of_ne (le_trans hB.2 hb'm) hvm⟩
    · ring
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Ioc]
  split_ifs with hab
  · have hsub : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc a b' = Set.Ioc a b' := by
      apply Set.inter_eq_right.2
      intro v hv; rw [Set.mem_Ioc] at hv ⊢; exact ⟨by linarith [hv.1], le_trans hv.2 hb'1⟩
    rw [hsub, ← intervalIntegral.integral_of_le hab.le]
  · push_neg at hab
    have : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc a b' = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (fun v hv => by
        simp only [Set.mem_inter_iff, Set.mem_Ioc] at hv; linarith [hv.2.1, hv.2.2])
    rw [this]; simp

/-- **Step-function Riemann lemma**: `Σ_p η̂(u_p)F(u_p)/p → ∫₀¹ η̂(v)F(v)/v`. -/
theorem m02_RS (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc 0 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z : ℝ, 1 < z → K ≤ Real.log z →
      |∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * F (m02u z p) -
        ∫ v in (0 : ℝ)..1, StepFn.eval e v * F v / v| ≤ ε := by
  classical
  obtain ⟨MF, hMF⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hF
  have hFaesm := m02_F_aesm F hF
  have hMFv : ∀ v ∈ Set.Ioc (0 : ℝ) 1, |F v| ≤ MF := fun v hv => by
    have := hMF v (Set.Ioc_subset_Icc_self hv); rwa [Real.norm_eq_abs] at this
  induction e with
  | nil =>
    intro ε hε
    refine ⟨0, fun z _ _ => ?_⟩
    simp only [StepFn.eval, List.foldl_nil, mul_zero, zero_mul, zero_div, Finset.sum_const_zero,
      intervalIntegral.integral_zero, sub_zero, abs_zero]
    exact hε.le
  | cons pr rest ih =>
    intro ε hε
    have hpr : (0 : ℚ) < pr.1 := he pr List.mem_cons_self
    have hrest : ∀ pr' ∈ rest, (0 : ℚ) < pr'.1 := fun pr' h => he pr' (List.mem_cons_of_mem _ h)
    have ha : (0 : ℝ) < pr.1 := by exact_mod_cast hpr
    set a : ℝ := (pr.1 : ℝ) with hadef
    set c : ℝ := (pr.2 : ℝ) with hcdef
    set mL := m02mL rest
    set b' := min mL 1 with hb'
    set ind : ℝ → ℝ := fun u => if a ≤ u ∧ u < mL then 1 else 0 with hind
    obtain ⟨K1, hK1⟩ := ih hrest (ε / 2) (by linarith)
    -- the piece
    have hpiece : ∃ K2 : ℝ, ∀ z : ℝ, 1 < z → K2 ≤ Real.log z →
        |∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * F (m02u z p) -
          ∫ v in (0 : ℝ)..1, ind v * F v / v| ≤ ε / (2 * (|c| + 1)) := by
      have hsum : ∀ z : ℝ, 1 < z → ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * F (m02u z p) =
          ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b'), (1 / (p : ℝ)) * F (m02u z p) := by
        intro z hz
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro p hp
        have hu1 := m02_u_lt_one z hz p hp
        simp only [hind]
        by_cases h1 : a ≤ m02u z p ∧ m02u z p < mL
        · rw [if_pos h1, if_pos ⟨h1.1, lt_min h1.2 hu1⟩]; ring
        · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.1, lt_of_lt_of_le h2.2 (min_le_left _ _)⟩)]; ring
      have hint := m02_int_pieceF a mL ha F
      by_cases hab : a < b'
      · obtain ⟨K2, hK2⟩ := m02_riemann a b' ha hab (min_le_right _ _) F
          (hF.mono (fun v hv => ⟨by linarith [hv.1], le_trans hv.2 (min_le_right _ _)⟩))
          (ε / (2 * (|c| + 1))) (by positivity)
        refine ⟨K2, fun z hz hK => ?_⟩
        rw [hsum z hz, hint, if_pos hab]
        exact hK2 z hz hK
      · refine ⟨0, fun z hz _ => ?_⟩
        rw [hsum z hz, hint, if_neg hab, Finset.sum_eq_zero]
        · simp only [sub_zero, abs_zero]; positivity
        · intro p hp; rw [Finset.mem_filter] at hp
          exact absurd (lt_of_le_of_lt hp.2.1 hp.2.2) hab
    obtain ⟨K2, hK2⟩ := hpiece
    refine ⟨max K1 K2, fun z hz hK => ?_⟩
    have hsum : ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval (pr :: rest) (m02u z p) * F (m02u z p) =
        c * ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * F (m02u z p) +
          ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval rest (m02u z p) * F (m02u z p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hu2 : m02u z p < 2 := by linarith [m02_u_lt_one z hz p hp]
      rw [m02_eval_cons]
      simp only [m02_mL_iff rest _ hu2, hind]
      split_ifs <;> ring
    have hintg : ∫ v in (0 : ℝ)..1, StepFn.eval (pr :: rest) v * F v / v =
        c * (∫ v in (0 : ℝ)..1, ind v * F v / v) + ∫ v in (0 : ℝ)..1, StepFn.eval rest v * F v / v := by
      have hcongr : ∫ v in (0 : ℝ)..1, StepFn.eval (pr :: rest) v * F v / v =
          ∫ v in (0 : ℝ)..1, (c * (ind v * F v / v) + StepFn.eval rest v * F v / v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hv
        have hv2 : v < 2 := by linarith
        simp only
        rw [m02_eval_cons]
        simp only [m02_mL_iff rest _ hv2, hind]
        split_ifs <;> ring
      have hpi : IntervalIntegrable (fun v => ind v * F v / v) volume 0 1 := by
        apply m02_intble2 (fun v => ind v * F v) _ MF a _ ha
        · intro v hv; simp only [hind]; rw [if_neg (fun h => by linarith [h.1]), zero_mul]
        · exact (Measurable.ite (measurableSet_Ici.inter measurableSet_Iio) measurable_const
            measurable_const).aestronglyMeasurable.mul hFaesm
        · intro v hv; simp only [hind]
          have := hMFv v hv
          split_ifs <;> simp [this, le_trans (abs_nonneg _) this]
      have hri : IntervalIntegrable (fun v => StepFn.eval rest v * F v / v) volume 0 1 := by
        apply m02_intble2 (fun v => StepFn.eval rest v * F v) _ (m02Mv rest * MF) (m02u0 rest) _ (m02_u0_pos rest hrest)
        · intro v hv; rw [m02_eval_zero rest v hv, zero_mul]
        · exact (m02_eval_meas rest).aestronglyMeasurable.mul hFaesm
        · intro v hv; rw [abs_mul]
          exact mul_le_mul (m02_eval_abs rest v) (hMFv v hv) (abs_nonneg _) (m02_Mv_nonneg rest)
      rw [hcongr, intervalIntegral.integral_add (hpi.const_mul c) hri, intervalIntegral.integral_const_mul]
    rw [hsum, hintg]
    have hp := hK2 z hz (le_trans (le_max_right _ _) hK)
    have hr := hK1 z hz (le_trans (le_max_left _ _) hK)
    have hc : |c| * (ε / (2 * (|c| + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg c]
    calc _ = |c * (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * F (m02u z p) - ∫ v in (0 : ℝ)..1, ind v * F v / v) +
          (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval rest (m02u z p) * F (m02u z p) -
            ∫ v in (0 : ℝ)..1, StepFn.eval rest v * F v / v)| := by ring_nf
      _ ≤ |c| * (ε / (2 * (|c| + 1))) + ε / 2 := by
          refine le_trans (abs_add_le _ _) (add_le_add ?_ hr)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ ε := by linarith

/-! ### `Â` is continuous on `[0, 1]` -/

lemma m02_Ip_eq (a m s : ℝ) (ha : 0 < a) :
    m02Ip a m s = s * (Real.log (max (min m s) a) - Real.log a) - (max (min m s) a - a) := by
  unfold m02Ip
  split_ifs with h
  · rw [max_eq_left h.le]
  · push_neg at h; rw [max_eq_right h]; ring

lemma m02_Ip_cont (a m : ℝ) (ha : 0 < a) : Continuous (fun s => m02Ip a m s) := by
  have : (fun s => m02Ip a m s) = fun s => s * (Real.log (max (min m s) a) - Real.log a) - (max (min m s) a - a) := by
    funext s; exact m02_Ip_eq a m s ha
  rw [this]
  have hc : Continuous (fun s : ℝ => max (min m s) a) := (continuous_const.min continuous_id).max continuous_const
  have hlog : Continuous (fun s : ℝ => Real.log (max (min m s) a)) :=
    hc.log (fun s => (lt_of_lt_of_le ha (le_max_right _ _)).ne')
  exact (continuous_id.mul (hlog.sub continuous_const)).sub (hc.sub continuous_const)

lemma m02_Ahat_cons (pr : ℚ × ℚ) (rest : StepFn) (ha : (0 : ℝ) < pr.1) (hrest : ∀ pr' ∈ rest, (0 : ℚ) < pr'.1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Ahat (pr :: rest) s = (pr.2 : ℝ) * m02Ip (pr.1 : ℝ) (m02mL rest) s + Ahat rest s := by
  classical
  unfold Ahat
  set a : ℝ := (pr.1 : ℝ)
  set c : ℝ := (pr.2 : ℝ)
  set mL := m02mL rest
  set ind : ℝ → ℝ := fun u => if a ≤ u ∧ u < mL then 1 else 0 with hind
  have hcongr : ∫ v in (0 : ℝ)..s, StepFn.eval (pr :: rest) v * (s - v) / v =
      ∫ v in (0 : ℝ)..s, (c * (ind v * (s - v) / v) + StepFn.eval rest v * (s - v) / v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hs0, Set.mem_Icc] at hv
    have hv2 : v < 2 := by linarith
    simp only
    rw [m02_eval_cons]
    simp only [m02_mL_iff rest _ hv2, hind]
    split_ifs <;> ring
  have hpi : IntervalIntegrable (fun v => ind v * (s - v) / v) volume 0 s := by
    apply m02_intble ind _ 1 a s _ ha _ hs0
    · exact Measurable.ite (measurableSet_Ici.inter measurableSet_Iio) measurable_const measurable_const
    · intro v; simp only [hind]; split_ifs <;> simp
    · intro v hv; simp only [hind]; rw [if_neg]; intro h; linarith [h.1]
  rw [hcongr, intervalIntegral.integral_add (hpi.const_mul c) (m02_eval_intble rest hrest s hs0),
    intervalIntegral.integral_const_mul]
  congr 2
  exact m02_int_piece a mL s ha hs0

lemma m02_Ahat_cont (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) : ContinuousOn (Ahat e) (Set.Icc 0 1) := by
  induction e with
  | nil =>
    have : Ahat [] = fun _ => 0 := by
      funext s; unfold Ahat; simp [StepFn.eval]
    rw [this]; exact continuousOn_const
  | cons pr rest ih =>
    have hrest : ∀ pr' ∈ rest, (0 : ℚ) < pr'.1 := fun pr' h => he pr' (List.mem_cons_of_mem _ h)
    have ha : (0 : ℝ) < pr.1 := by exact_mod_cast he pr List.mem_cons_self
    apply ContinuousOn.congr (f := fun s => (pr.2 : ℝ) * m02Ip (pr.1 : ℝ) (m02mL rest) s + Ahat rest s)
    · exact (continuousOn_const.mul (m02_Ip_cont _ _ ha).continuousOn).add (ih hrest)
    · intro s hs; exact m02_Ahat_cons pr rest ha hrest s hs.1 hs.2

end KappaOmega2
