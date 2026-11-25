import KappaOmega2.Items.M12_G

/-!
# M12 helper: crude bound `G_i(x, c) ≤ (1/x) log(min(c, 1/2)/x)^i / i!` (used for levels `≥ 18`)
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real
open scoped ENNReal

namespace KappaOmega2.M12

open KappaOmega2

/-- The crude majorant. -/
noncomputable def crude (i : ℕ) (x c : ℝ) : ℝ := (1 / x) * (max 0 (Real.log (min c (1 / 2) / x))) ^ i / (i.factorial)

lemma crude_nonneg (i : ℕ) {x : ℝ} (hx : 0 < x) (c : ℝ) : 0 ≤ crude i x c := by
  unfold crude
  have : 0 ≤ max 0 (Real.log (min c (1 / 2) / x)) := le_max_left _ _
  positivity

/-- `∫_x^b (1/(x y)) log(y/x)^i/i! dy = (1/x) log(b/x)^{i+1}/(i+1)!`. -/
lemma integral_crude (i : ℕ) {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    ∫ y in x..b, (1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial) =
      (1 / x) * Real.log (b / x) ^ (i + 1) / ((i + 1).factorial) := by
  have hF : ∀ y ∈ Set.uIcc x b, HasDerivAt (fun y => (1 / x) * Real.log (y / x) ^ (i + 1) / ((i + 1).factorial))
      ((1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial)) y := by
    intro y hy
    rw [Set.uIcc_of_le hxb] at hy
    have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
    have h1 : HasDerivAt (fun y => y / x) (1 / x) y := by
      simpa using (hasDerivAt_id y).div_const x
    have h2 : HasDerivAt (fun y => Real.log (y / x)) ((1 / x) / (y / x)) y :=
      h1.log (div_pos hy0 hx).ne'
    have h3 := (h2.pow (i + 1)).const_mul (1 / x) |>.div_const ((i + 1).factorial : ℝ)
    convert h3 using 1
    rw [Nat.factorial_succ]
    push_cast
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
  · simp
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxb]
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
    apply ContinuousAt.continuousWithinAt
    have : ContinuousAt (fun y => Real.log (y / x)) y :=
      (continuousAt_id.div_const x).log (div_pos hy0 hx).ne'
    exact ((continuousAt_const.div (continuousAt_const.mul continuousAt_id) (mul_pos hx hy0).ne').mul (this.pow i)).div_const _

lemma lintegral_crude (i : ℕ) {x b : ℝ} (hx : 0 < x) :
    ∫⁻ y, (Set.Ioc x b).indicator (fun y => ENNReal.ofReal ((1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial))) y ≤
      ENNReal.ofReal ((1 / x) * (max 0 (Real.log (b / x))) ^ (i + 1) / ((i + 1).factorial)) := by
  rcases le_or_gt b x with hb | hb
  · rw [Set.Ioc_eq_empty (not_lt.mpr hb)]; simp
  rw [lintegral_indicator measurableSet_Ioc]
  have hcont : ContinuousOn (fun y => (1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial)) (Set.Icc x b) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hx hy.1
    apply ContinuousAt.continuousWithinAt
    have : ContinuousAt (fun y => Real.log (y / x)) y :=
      (continuousAt_id.div_const x).log (div_pos hy0 hx).ne'
    exact ((continuousAt_const.div (continuousAt_const.mul continuousAt_id) (mul_pos hx hy0).ne').mul (this.pow i)).div_const _
  have hint : IntegrableOn (fun y => (1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial)) (Set.Ioc x b) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc x b)] (fun y => (1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun y hy => ?_)
    have hy0 : 0 < y := lt_trans hx hy.1
    have : 0 ≤ Real.log (y / x) := Real.log_nonneg (by rw [le_div_iff₀ hx]; linarith [hy.1])
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hb.le, integral_crude i hx hb.le]
  apply ENNReal.ofReal_le_ofReal
  have : Real.log (b / x) ≤ max 0 (Real.log (b / x)) := le_max_right _ _
  have h0 : 0 ≤ Real.log (b / x) := Real.log_nonneg (by rw [le_div_iff₀ hx]; linarith)
  have := pow_le_pow_left₀ h0 this (i + 1)
  have : (0 : ℝ) < ((i + 1).factorial : ℝ) := by positivity
  gcongr

theorem G_crude : ∀ i, 1 ≤ i → ∀ {x : ℝ}, 0 < x → ∀ c, G i x c ≤ ENNReal.ofReal (crude i x c) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro x hx c
    rcases le_or_gt (1 / 3) x with h3 | h3
    · rw [G_eq_zero le_rfl (Or.inl h3)]; exact zero_le
    refine (G_one_le hx.le).trans ?_
    have hpt : ∀ z, (S1 x c).indicator (fun z => ENNReal.ofReal (1 / (z * (1 - x - z)))) z ≤
        (Set.Ioc x (min c (1 / 2))).indicator (fun y => ENNReal.ofReal ((1 / (x * y)) * Real.log (y / x) ^ 0 / ((0 : ℕ).factorial))) z := by
      intro z
      by_cases hz : z ∈ S1 x c
      swap
      · rw [Set.indicator_of_notMem hz]; exact zero_le
      obtain ⟨hz1, hz2, hz3⟩ := hz
      have hmem : z ∈ Set.Ioc x (min c (1 / 2)) := ⟨by linarith, le_min hz3.le (by linarith)⟩
      rw [Set.indicator_of_mem (show z ∈ S1 x c from ⟨hz1, hz2, hz3⟩), Set.indicator_of_mem hmem]
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      have hz0 : 0 < z := by linarith
      apply one_div_le_one_div_of_le (mul_pos hx hz0)
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ hz0.le
      linarith
    refine (lintegral_mono hpt).trans ((lintegral_crude 0 hx).trans (le_of_eq ?_))
    unfold crude
    simp
  | succ i hi ih =>
    intro x hx c
    refine (G_succ_le hi hx.le).trans ?_
    have hpt : ∀ y, (Sy x c).indicator (fun y => ENNReal.ofReal (1 / (y * (1 - y))) * G i (x / (1 - y)) (y / (1 - y))) y ≤
        (Set.Ioc x (min c (1 / 3))).indicator (fun y => ENNReal.ofReal ((1 / (x * y)) * Real.log (y / x) ^ i / (i.factorial))) y := by
      intro y
      by_cases hy : y ∈ Sy x c
      swap
      · rw [Set.indicator_of_notMem hy]; exact zero_le
      obtain ⟨hy1, hy2, hy3⟩ := hy
      have hmem : y ∈ Set.Ioc x (min c (1 / 3)) := ⟨hy1, le_min hy3.le hy2⟩
      rw [Set.indicator_of_mem (show y ∈ Sy x c from ⟨hy1, hy2, hy3⟩), Set.indicator_of_mem hmem]
      have hy0 : 0 < y := lt_trans hx hy1
      have h1y : 0 < 1 - y := by linarith
      refine (mul_le_mul' le_rfl (ih (div_pos hx h1y) (y / (1 - y)))).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold crude
      have hmin : min (y / (1 - y)) (1 / 2) = y / (1 - y) := by
        apply min_eq_left; rw [div_le_iff₀ h1y]; linarith
      have hratio : y / (1 - y) / (x / (1 - y)) = y / x := by field_simp
      rw [hmin, hratio, max_eq_right (Real.log_nonneg (by rw [le_div_iff₀ hx]; linarith))]
      field_simp
    refine (lintegral_mono hpt).trans ?_
    rcases le_or_gt (min c (1 / 3)) x with hb | hb
    · rw [Set.Ioc_eq_empty (not_lt.mpr hb)]; simp
    refine (lintegral_crude i hx).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold crude
    have h1 : max 0 (Real.log (min c (1 / 3) / x)) ≤ max 0 (Real.log (min c (1 / 2) / x)) := by
      apply max_le_max le_rfl
      apply Real.log_le_log (div_pos (lt_trans hx hb) hx)
      apply div_le_div_of_nonneg_right _ hx.le
      exact min_le_min le_rfl (by norm_num)
    have h0 : 0 ≤ max 0 (Real.log (min c (1 / 3) / x)) := le_max_left _ _
    have := pow_le_pow_left₀ h0 h1 (i + 1)
    have : (0 : ℝ) < ((i + 1).factorial : ℝ) := by positivity
    have : 0 < 1 / x := by positivity
    gcongr

end KappaOmega2.M12
