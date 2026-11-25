import Omega3.DefsSieve
import Palprimes.MainTerm.MvalPos

/-!
# M12 helper: the `W`-part of `MvalLower`,
`−∫_{1/2}^1 (W(1) − W)/((1 − t)t) + ∫_0^{1/2} W/((1 − t)t) ≥ 0.0320` (exact value 0.0321844),
and `∫_a^b W/t ≤ min((b − a)(1 − m/b), k²(b² − a²)/2)` on `[m, 1/3]`.
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real

namespace Omega3.M12

open Omega3 Palprimes.MT

lemma Wf_eq (t : ℝ) : Wf t = if t ≤ 1 / 85 then 0 else if t ≤ 1 / 3 then min (9999 / 1000 * t ^ 2) (t - 1 / 85)
    else if t ≤ 83 / 85 then t - 1 / 85 else 82 / 85 := by
  unfold Wf mm kSq UU W1
  split_ifs <;> rfl

lemma Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  rw [Wf_eq]
  split_ifs with h1 h2 h3
  · exact le_rfl
  · push_neg at h1; exact le_min (by positivity) (by linarith)
  · push_neg at h1; linarith
  · norm_num

lemma Wf_le_lin {t : ℝ} (h1 : 1 / 85 ≤ t) (h2 : t ≤ 83 / 85) : Wf t ≤ t - 1 / 85 := by
  rw [Wf_eq]
  split_ifs <;> first | linarith | exact min_le_right _ _

lemma Wf_le_quad {t : ℝ} (h2 : t ≤ 1 / 3) : Wf t ≤ 9999 / 1000 * t ^ 2 := by
  rw [Wf_eq]
  split_ifs <;> first | positivity | exact min_le_left _ _ | (exfalso; linarith)

lemma Wf_lin {t : ℝ} (h1 : 1 / 85 < t) (h2 : t ≤ 17 / 1250 ∨ (54 / 625 ≤ t ∧ t ≤ 83 / 85)) : Wf t = t - 1 / 85 := by
  rw [Wf_eq, if_neg (not_le.mpr h1)]
  split_ifs with b c
  · apply min_eq_right
    rcases h2 with h2 | ⟨h2, -⟩
    · nlinarith
    · nlinarith
  · rfl
  · rcases h2 with h2 | ⟨-, h2⟩ <;> [linarith; exact absurd h2 c]

lemma Wf_quad {t : ℝ} (h1 : 681 / 50000 ≤ t) (h2 : t ≤ 4319 / 50000) : Wf t = 9999 / 1000 * t ^ 2 := by
  rw [Wf_eq, if_neg (by norm_num; linarith), if_pos (by linarith)]
  apply min_eq_left
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

lemma Wf_zero {t : ℝ} (h : t ≤ 1 / 85) : Wf t = 0 := by rw [Wf_eq, if_pos h]

lemma Wf_top {t : ℝ} (h : 83 / 85 ≤ t) : Wf t = 82 / 85 := by
  rw [Wf_eq, if_neg (by linarith), if_neg (by linarith)]
  split_ifs with c
  · have : t = 83 / 85 := le_antisymm c h
    subst this; norm_num
  · rfl

lemma measurable_Wf : Measurable Wf := by
  have : Wf = fun t => if t ≤ 1 / 85 then 0 else if t ≤ 1 / 3 then min (9999 / 1000 * t ^ 2) (t - 1 / 85)
      else if t ≤ 83 / 85 then t - 1 / 85 else 82 / 85 := funext Wf_eq
  rw [this]
  refine Measurable.ite measurableSet_Iic measurable_const (Measurable.ite measurableSet_Iic ?_ (Measurable.ite measurableSet_Iic ?_ measurable_const))
  · exact (measurable_const.mul (continuous_pow 2).measurable).min (measurable_id.sub measurable_const)
  · exact measurable_id.sub measurable_const

lemma Wf_le_one (t : ℝ) : Wf t ≤ 1 := by
  rw [Wf_eq]
  split_ifs with a b c
  · norm_num
  · push_neg at a; exact (min_le_right _ _).trans (by linarith)
  · linarith
  · norm_num

/-! ## Interval integrability -/

lemma ii_Wg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable (fun t => Wf t / ((1 - t) * t)) volume a b := by
  refine ii_of_bound hab (measurable_Wf.div ((measurable_const.sub measurable_id).mul measurable_id))
    (C := 1 / ((1 - b) * a)) fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  rw [abs_of_nonneg (div_nonneg (Wf_nonneg t) (by positivity))]
  calc Wf t / ((1 - t) * t) ≤ 1 / ((1 - t) * t) := div_le_div_of_nonneg_right (Wf_le_one t) (by positivity)
    _ ≤ 1 / ((1 - b) * a) := one_div_le_one_div_of_le (mul_pos (by linarith) ha)
        (mul_le_mul (by linarith [ht.2]) ht.1 ha.le ht1.le)

lemma ii_W1g {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable (fun t => (82 / 85 - Wf t) / ((1 - t) * t)) volume a b := by
  refine ii_of_bound hab ((measurable_const.sub measurable_Wf).div ((measurable_const.sub measurable_id).mul measurable_id))
    (C := 1 / ((1 - b) * a)) fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hW := Wf_nonneg t
  have hW1 : Wf t ≤ 82 / 85 ∨ 82 / 85 < Wf t := le_or_gt _ _
  rw [abs_div, abs_of_pos (mul_pos ht1 ht0)]
  have : |82 / 85 - Wf t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [Wf_le_one t]
  calc |82 / 85 - Wf t| / ((1 - t) * t) ≤ 1 / ((1 - t) * t) := div_le_div_of_nonneg_right this (by positivity)
    _ ≤ 1 / ((1 - b) * a) := one_div_le_one_div_of_le (mul_pos (by linarith) ha)
        (mul_le_mul (by linarith [ht.2]) ht.1 ha.le ht1.le)

/-! ## Closed forms -/

/-- Antiderivative of `k² t/(1 − t)`. -/
theorem integral_quad {lo hi : ℝ} (h0 : 0 < lo) (hlh : lo ≤ hi) (h1 : hi < 1) :
    ∫ t in lo..hi, 9999 / 1000 * t ^ 2 / ((1 - t) * t) =
      9999 / 1000 * ((lo - hi) + (Real.log (1 - lo) - Real.log (1 - hi))) := by
  have hderiv : ∀ t ∈ Set.uIcc lo hi, HasDerivAt (fun t => 9999 / 1000 * (-t - Real.log (1 - t)))
      (9999 / 1000 * t ^ 2 / ((1 - t) * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hlh] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun t => Real.log (1 - t)) ((-1) / (1 - t)) t := h1.log ht1.ne'
    have h3 : HasDerivAt (fun t => -t - Real.log (1 - t)) (-1 - (-1) / (1 - t)) t := (hasDerivAt_neg t).sub h2
    have h4 := h3.const_mul (9999 / 1000 : ℝ)
    convert h4 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hlh]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_const.mul (continuousAt_id.pow 2)).div ((continuousAt_const.sub continuousAt_id).mul continuousAt_id)
      (mul_pos ht1 ht0).ne'

/-! ## The value -/

lemma I1_eq : ∫ t in (1 / 2 : ℝ)..1, (82 / 85 - Wf t) / ((1 - t) * t) = -(Fd (83 / 85) (83 / 85) - Fd (83 / 85) (1 / 2)) := by
  have hii1 : IntervalIntegrable (fun t => (82 / 85 - Wf t) / ((1 - t) * t)) volume (1 / 2) (83 / 85) :=
    ii_W1g (by norm_num) (by norm_num) (by norm_num)
  have hz : ∀ t ∈ Set.uIcc (83 / 85 : ℝ) 1, (82 / 85 - Wf t) / ((1 - t) * t) = 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (83 / 85 : ℝ) ≤ 1)] at ht
    rw [Wf_top ht.1]; simp
  have hii2 : IntervalIntegrable (fun t => (82 / 85 - Wf t) / ((1 - t) * t)) volume (83 / 85) 1 :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr (fun t ht => (hz t (Set.uIoc_subset_uIcc ht)).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals hii1 hii2, intervalIntegral.integral_congr hz, intervalIntegral.integral_zero,
    add_zero, ← integral_lin _ (by norm_num) (by norm_num) (by norm_num), ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 83 / 85)] at ht
  try dsimp only
  rw [Wf_lin (by linarith [ht.1]) (Or.inr ⟨by linarith [ht.1], ht.2⟩)]
  ring

theorem I2_ge : Fd (1 / 85) (17 / 1250) - Fd (1 / 85) (1 / 85) +
      9999 / 1000 * ((681 / 50000 - 4319 / 50000) + (Real.log (1 - 681 / 50000) - Real.log (1 - 4319 / 50000))) +
      (Fd (1 / 85) (1 / 2) - Fd (1 / 85) (54 / 625)) ≤ ∫ t in (0 : ℝ)..(1 / 2), Wf t / ((1 - t) * t) := by
  set f := fun t => Wf t / ((1 - t) * t) with hf
  have hnn : ∀ t, 0 < t → t < 1 → 0 ≤ f t := fun t h0 h1 => div_nonneg (Wf_nonneg t) (mul_pos (by linarith) h0).le
  have hz : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 85), f t = 0 := by
    intro t ht; rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 85)] at ht
    simp only [hf]; rw [Wf_zero ht.2]; simp
  have hii0 : IntervalIntegrable f volume 0 (1 / 85) :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr (fun t ht => (hz t (Set.uIoc_subset_uIcc ht)).symm)
  have i1 := ii_Wg (a := 1 / 85) (b := 17 / 1250) (by norm_num) (by norm_num) (by norm_num)
  have i2 := ii_Wg (a := 17 / 1250) (b := 681 / 50000) (by norm_num) (by norm_num) (by norm_num)
  have i3 := ii_Wg (a := 681 / 50000) (b := 4319 / 50000) (by norm_num) (by norm_num) (by norm_num)
  have i4 := ii_Wg (a := 4319 / 50000) (b := 54 / 625) (by norm_num) (by norm_num) (by norm_num)
  have i5 := ii_Wg (a := 54 / 625) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [← intervalIntegral.integral_add_adjacent_intervals hii0 (((((i1.trans i2).trans i3).trans i4).trans i5)),
    intervalIntegral.integral_congr hz, intervalIntegral.integral_zero, zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals i1 ((((i2.trans i3).trans i4).trans i5)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (((i3.trans i4).trans i5)),
    ← intervalIntegral.integral_add_adjacent_intervals i3 ((i4.trans i5)),
    ← intervalIntegral.integral_add_adjacent_intervals i4 i5]
  have e1 : ∫ t in (1 / 85 : ℝ)..(17 / 1250), f t = Fd (1 / 85) (17 / 1250) - Fd (1 / 85) (1 / 85) := by
    rw [← integral_lin _ (by norm_num) (by norm_num) (by norm_num)]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1 / 85 : ℝ) ≤ 17 / 1250)] at ht
    simp only [hf]; rw [Wf_lin ht.1 (Or.inl ht.2)]
  have e3 : ∫ t in (681 / 50000 : ℝ)..(4319 / 50000), f t =
      9999 / 1000 * ((681 / 50000 - 4319 / 50000) + (Real.log (1 - 681 / 50000) - Real.log (1 - 4319 / 50000))) := by
    rw [← integral_quad (by norm_num) (by norm_num) (by norm_num)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num : (681 / 50000 : ℝ) ≤ 4319 / 50000)] at ht
    simp only [hf]; rw [Wf_quad ht.1 ht.2]
  have e5 : ∫ t in (54 / 625 : ℝ)..(1 / 2), f t = Fd (1 / 85) (1 / 2) - Fd (1 / 85) (54 / 625) := by
    rw [← integral_lin _ (by norm_num) (by norm_num) (by norm_num)]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (54 / 625 : ℝ) ≤ 1 / 2)] at ht
    simp only [hf]; rw [Wf_lin (by linarith [ht.1]) (Or.inr ⟨ht.1.le, by linarith [ht.2]⟩)]
  have g2 : 0 ≤ ∫ t in (17 / 1250 : ℝ)..(681 / 50000), f t :=
    intervalIntegral.integral_nonneg (by norm_num) fun t ht => hnn t (by linarith [ht.1]) (by linarith [ht.2])
  have g4 : 0 ≤ ∫ t in (4319 / 50000 : ℝ)..(54 / 625), f t :=
    intervalIntegral.integral_nonneg (by norm_num) fun t ht => hnn t (by linarith [ht.1]) (by linarith [ht.2])
  rw [e1, e3, e5]
  linarith

/-- The numerical value. -/
theorem base_ge : (32 / 1000 : ℝ) ≤ -(∫ t in (1 / 2 : ℝ)..1, (W1 - Wf t) / ((1 - t) * t)) +
    ∫ t in (0 : ℝ)..(1 / 2), Wf t / ((1 - t) * t) := by
  have hW1 : W1 = 82 / 85 := rfl
  rw [hW1, I1_eq]
  have h2 := I2_ge
  suffices key : (32 / 1000 : ℝ) ≤ -(-(Fd (83 / 85) (83 / 85) - Fd (83 / 85) (1 / 2))) +
      (Fd (1 / 85) (17 / 1250) - Fd (1 / 85) (1 / 85) +
      9999 / 1000 * ((681 / 50000 - 4319 / 50000) + (Real.log (1 - 681 / 50000) - Real.log (1 - 4319 / 50000))) +
      (Fd (1 / 85) (1 / 2) - Fd (1 / 85) (54 / 625))) by linarith
  simp only [Fd]
  -- logarithms
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  norm_num at l2a l2b
  have eA : Real.log (83 / 85 : ℝ) = Real.log (1 - 2 / 85) := by norm_num
  have eB : Real.log (1 - 83 / 85 : ℝ) = -(5 * Real.log 2) - Real.log (1 - 43 / 128) - Real.log 2 := by
    rw [show (1 : ℝ) - 83 / 85 = (2 ^ 6)⁻¹ * (1 - 43 / 128)⁻¹ by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast; ring
  have eC : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have eC' : Real.log (1 - 1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  have eD : Real.log (17 / 1250 : ℝ) = Real.log (1 / 85) - Real.log (1 - 39 / 289) := by
    rw [show (17 / 1250 : ℝ) = (1 / 85) * (1 - 39 / 289)⁻¹ by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_inv]
    ring
  have eE : Real.log (1 - 1 / 85 : ℝ) = Real.log (1 - 17 / 1250) - Real.log (1 - 39 / 21000) := by
    rw [show (1 : ℝ) - 1 / 85 = (1 - 17 / 1250) * (1 - 39 / 21000)⁻¹ by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_inv]
    ring
  have eF : Real.log (54 / 625 : ℝ) = -(4 * Real.log 2) - Real.log (1 - 239 / 864) := by
    rw [show (54 / 625 : ℝ) = (2 ^ 4)⁻¹ * (1 - 239 / 864)⁻¹ by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast; ring
  have eG : Real.log (1 - 681 / 50000 : ℝ) = Real.log (1 - 4319 / 50000) - Real.log (1 - 3638 / 49319) := by
    rw [show (1 : ℝ) - 681 / 50000 = (1 - 4319 / 50000) * (1 - 3638 / 49319)⁻¹ by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_inv]
    ring
  rw [eA, eB, eC, eC', eD, eE, eF, eG]
  have b1 := (log_one_sub_bounds (y := 2 / 85) (by norm_num) (by norm_num) 4).2
  have b2 := (log_one_sub_bounds (y := 43 / 128) (by norm_num) (by norm_num) 14).1
  have b3 := (log_one_sub_bounds (y := 39 / 289) (by norm_num) (by norm_num) 8).1
  have b4 := (log_one_sub_bounds (y := 39 / 21000) (by norm_num) (by norm_num) 2).2
  have b5 := (log_one_sub_bounds (y := 239 / 864) (by norm_num) (by norm_num) 12).2
  have b6 := (log_one_sub_bounds (y := 3638 / 49319) (by norm_num) (by norm_num) 6).2
  have b7 := (log_one_sub_bounds (y := 54 / 625) (by norm_num) (by norm_num) 6).1
  norm_num [Finset.sum_range_succ] at b1 b2 b3 b4 b5 b6 b7
  linarith [b1, b2, b3, b4, b5, b6, b7, l2a, l2b]

/-! ## `∫ W/t` on a cell -/

theorem intW_le {a b : ℝ} (ha : 1 / 85 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 3) :
    ∫ t in a..b, Wf t / t ≤ min ((b - a) * (1 - (1 / 85) / b)) (9999 / 1000 * (b ^ 2 - a ^ 2) / 2) := by
  have ha0 : 0 < a := by linarith
  have hii : IntervalIntegrable (fun t => Wf t / t) volume a b := by
    refine ii_of_bound hab (measurable_Wf.div measurable_id) (C := 1 / a) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    rw [abs_of_nonneg (div_nonneg (Wf_nonneg t) ht0.le)]
    calc Wf t / t ≤ 1 / t := div_le_div_of_nonneg_right (Wf_le_one t) ht0.le
      _ ≤ 1 / a := one_div_le_one_div_of_le ha0 ht.1
  apply le_min
  · have hlin : IntervalIntegrable (fun t => (t - 1 / 85) / t) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
      exact ((continuousAt_id.sub continuousAt_const).div continuousAt_id ht0.ne').continuousWithinAt
    calc ∫ t in a..b, Wf t / t ≤ ∫ t in a..b, (t - 1 / 85) / t :=
          intervalIntegral.integral_mono_on hab hii hlin fun t ht => by
            have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
            exact div_le_div_of_nonneg_right (Wf_le_lin (by linarith [ht.1]) (by linarith [ht.2])) ht0.le
      _ = (b - a) - (1 / 85) * Real.log (b / a) := by
          have e : ∀ t ∈ Set.uIcc a b, (t - 1 / 85) / t = 1 - (1 / 85) * t⁻¹ := by
            intro t ht; rw [Set.uIcc_of_le hab] at ht
            have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
            field_simp
          have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
            apply ContinuousOn.intervalIntegrable
            rw [Set.uIcc_of_le hab]
            intro t ht
            exact (continuousAt_inv₀ (lt_of_lt_of_le ha0 ht.1).ne').continuousWithinAt
          rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub intervalIntegrable_const (hinv.const_mul _),
            intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 (by linarith)]
          simp
      _ ≤ (b - a) * (1 - (1 / 85) / b) := by
          have hb0 : 0 < b := by linarith
          have := Real.one_sub_inv_le_log_of_pos (show 0 < b / a by positivity)
          rw [inv_div] at this
          have e : (b - a) * (1 - (1 / 85) / b) = (b - a) - (1 / 85) * (1 - a / b) := by field_simp
          rw [e]
          nlinarith
  · have hq : IntervalIntegrable (fun t => 9999 / 1000 * t) volume a b := (continuous_const.mul continuous_id).intervalIntegrable _ _
    calc ∫ t in a..b, Wf t / t ≤ ∫ t in a..b, 9999 / 1000 * t :=
          intervalIntegral.integral_mono_on hab hii hq fun t ht => by
            have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
            rw [div_le_iff₀ ht0]
            have := Wf_le_quad (t := t) (by linarith [ht.2])
            nlinarith
      _ = 9999 / 1000 * (b ^ 2 - a ^ 2) / 2 := by
          rw [intervalIntegral.integral_const_mul, integral_id]; ring

end Omega3.M12
