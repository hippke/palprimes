import KappaOmega2.Items.M02_C

/-! # M02 helpers, part I: `c_η = 1 + J₁ + J₂ − Â(1)²`. -/

namespace KappaOmega2

open Finset Palprimes MeasureTheory

set_option linter.style.longLine false

lemma m02_min_id (u1 u2 : ℝ) (h1 : 0 < u1) (h2 : 0 < u2) :
    u1 * u2 * min 1 ((1 - u1) / u1 * ((1 - u2) / u2)) = (1 - u1) * (1 - u2) - max (1 - u1 - u2) 0 := by
  have hX : (1 - u1) / u1 * ((1 - u2) / u2) * (u1 * u2) = (1 - u1) * (1 - u2) := by field_simp
  have hp : 0 < u1 * u2 := mul_pos h1 h2
  rcases le_total 0 (1 - u1 - u2) with hc | hc
  · have : 1 ≤ (1 - u1) / u1 * ((1 - u2) / u2) := by
      by_contra hlt; push_neg at hlt
      have := mul_lt_mul_of_pos_right hlt hp
      rw [hX] at this; nlinarith
    rw [min_eq_left this, max_eq_left hc]; ring
  · have : (1 - u1) / u1 * ((1 - u2) / u2) ≤ 1 := by
      by_contra hlt; push_neg at hlt
      have := mul_lt_mul_of_pos_right hlt hp
      rw [hX] at this; nlinarith
    rw [min_eq_right this, max_eq_right hc]; linarith [hX]

lemma m02_eval_pos (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) (u : ℝ) (h : StepFn.eval e u ≠ 0) : 0 < u :=
  lt_of_lt_of_le (m02_u0_pos e he) (by by_contra hc; push_neg at hc; exact h (m02_eval_zero e u hc))

lemma m02_max_intble (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) (s : ℝ) (hs1 : s ≤ 1) :
    IntervalIntegrable (fun v => StepFn.eval e v * max (s - v) 0 / v) volume 0 1 := by
  apply m02_intble2 (fun v => StepFn.eval e v * max (s - v) 0) _ (m02Mv e) (m02u0 e) _ (m02_u0_pos e he)
  · intro v hv; rw [m02_eval_zero e v hv, zero_mul]
  · exact ((m02_eval_meas e).mul ((measurable_const.sub measurable_id).max measurable_const)).aestronglyMeasurable
  · intro v hv
    rw [abs_mul]
    have h0 : 0 ≤ max (s - v) 0 := le_max_right _ _
    have h1 : max (s - v) 0 ≤ 1 := max_le (by linarith [hv.1]) zero_le_one
    rw [abs_of_nonneg h0]
    calc |StepFn.eval e v| * max (s - v) 0 ≤ m02Mv e * 1 :=
          mul_le_mul (m02_eval_abs e v) h1 h0 (m02_Mv_nonneg e)
      _ = m02Mv e := mul_one _

lemma m02_Ahat_max (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ v in (0 : ℝ)..1, StepFn.eval e v * max (s - v) 0 / v = Ahat e s := by
  have hI := m02_max_intble e he s hs1
  have hI1 : IntervalIntegrable (fun v => StepFn.eval e v * max (s - v) 0 / v) volume 0 s :=
    hI.mono_set (by rw [Set.uIcc_of_le hs0, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hs1)
  have hI2 : IntervalIntegrable (fun v => StepFn.eval e v * max (s - v) 0 / v) volume s 1 :=
    hI.mono_set (by rw [Set.uIcc_of_le hs1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc hs0 le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have h1 : ∫ v in (0 : ℝ)..s, StepFn.eval e v * max (s - v) 0 / v = Ahat e s := by
    unfold Ahat
    apply intervalIntegral.integral_congr
    intro v hv; rw [Set.uIcc_of_le hs0] at hv
    simp only; rw [max_eq_left (by linarith [hv.2])]
  have h2 : ∫ v in s..1, StepFn.eval e v * max (s - v) 0 / v = 0 := by
    have : ∫ v in s..1, StepFn.eval e v * max (s - v) 0 / v = ∫ v in s..(1 : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv; rw [Set.uIcc_of_le hs1] at hv
      simp only; rw [max_eq_right (by linarith [hv.1])]; ring
    rw [this]; simp
  rw [h1, h2, add_zero]

/-- **The identity** `c_η = 1 + J₁ + J₂ − Â(1)²`. -/
theorem m02_cEta (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) :
    cEta e = 1 + (∫ u in (0 : ℝ)..1, StepFn.eval e u ^ 2 * (1 - u) / u) +
      (∫ u in (0 : ℝ)..1, StepFn.eval e u * Ahat e (1 - u) / u) - Ahat e 1 ^ 2 := by
  classical
  set A1 := Ahat e 1 with hA1
  have hA1' : A1 = ∫ v in (0 : ℝ)..1, StepFn.eval e v * (1 - v) / v := rfl
  have hint1 := m02_eval_intble e he 1 zero_le_one
  -- inner integral
  have hinner : ∀ u1 ∈ Set.uIcc (0 : ℝ) 1,
      (∫ u2 in (0 : ℝ)..1, StepFn.eval e u1 * StepFn.eval e u2 * min 1 ((1 - u1) / u1 * ((1 - u2) / u2))) =
        A1 * (StepFn.eval e u1 * (1 - u1) / u1) - StepFn.eval e u1 * Ahat e (1 - u1) / u1 := by
    intro u1 hu1
    rw [Set.uIcc_of_le zero_le_one] at hu1
    by_cases h0 : StepFn.eval e u1 = 0
    · simp [h0]
    have hu1p : 0 < u1 := m02_eval_pos e he u1 h0
    have hcongr : ∫ u2 in (0 : ℝ)..1, StepFn.eval e u1 * StepFn.eval e u2 * min 1 ((1 - u1) / u1 * ((1 - u2) / u2)) =
        ∫ u2 in (0 : ℝ)..1, (StepFn.eval e u1 / u1) *
          ((1 - u1) * (StepFn.eval e u2 * (1 - u2) / u2) - StepFn.eval e u2 * max (1 - u1 - u2) 0 / u2) := by
      apply intervalIntegral.integral_congr
      intro u2 _
      simp only
      by_cases h2 : StepFn.eval e u2 = 0
      · rw [h2]; ring
      have hu2p : 0 < u2 := m02_eval_pos e he u2 h2
      have hid := m02_min_id u1 u2 hu1p hu2p
      have e1 : (StepFn.eval e u1 / u1) * ((1 - u1) * (StepFn.eval e u2 * (1 - u2) / u2) -
          StepFn.eval e u2 * max (1 - u1 - u2) 0 / u2) =
          StepFn.eval e u1 * StepFn.eval e u2 * ((1 - u1) * (1 - u2) - max (1 - u1 - u2) 0) / (u1 * u2) := by
        field_simp
      rw [e1, ← hid]
      field_simp
    rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hint1.const_mul (1 - u1))
      (m02_max_intble e he (1 - u1) (by linarith [hu1.1])), intervalIntegral.integral_const_mul,
      m02_Ahat_max e he (1 - u1) (by linarith [hu1.2]) (by linarith [hu1.1]), ← hA1']
    field_simp
  -- outer integral
  have hcontA : ContinuousOn (fun u => Ahat e (1 - u)) (Set.Icc 0 1) := by
    apply (m02_Ahat_cont e he).comp (continuousOn_const.sub continuousOn_id)
    intro u hu
    have h1 : (0 : ℝ) ≤ u := hu.1
    have h2 : u ≤ 1 := hu.2
    exact ⟨show (0 : ℝ) ≤ 1 - u by linarith, show 1 - u ≤ (1 : ℝ) by linarith⟩
  obtain ⟨MA, hMA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcontA
  have hint2 : IntervalIntegrable (fun u => StepFn.eval e u * Ahat e (1 - u) / u) volume 0 1 := by
    apply m02_intble2 (fun u => StepFn.eval e u * Ahat e (1 - u)) _ (m02Mv e * MA) (m02u0 e) _ (m02_u0_pos e he)
    · intro v hv; rw [m02_eval_zero e v hv, zero_mul]
    · exact (m02_eval_meas e).aestronglyMeasurable.mul (m02_F_aesm _ hcontA)
    · intro v hv
      rw [abs_mul]
      have := hMA v (Set.Ioc_subset_Icc_self hv)
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul (m02_eval_abs e v) this (abs_nonneg _) (m02_Mv_nonneg e)
  have houter : ∫ u1 in (0 : ℝ)..1, ∫ u2 in (0 : ℝ)..1,
      StepFn.eval e u1 * StepFn.eval e u2 * min 1 ((1 - u1) / u1 * ((1 - u2) / u2)) =
      A1 * A1 - ∫ u in (0 : ℝ)..1, StepFn.eval e u * Ahat e (1 - u) / u := by
    rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_sub (hint1.const_mul A1) hint2,
      intervalIntegral.integral_const_mul, ← hA1']
  unfold cEta
  rw [houter]
  ring

end KappaOmega2
