import KappaOmega2.Statements
import KappaOmega2.Items.M06_Comb

namespace KappaOmega2

open Finset Filter Topology Palprimes Palprimes.MT Palprimes.Greaves

set_option linter.style.longLine false

/-! Item M06: Lemma 7 from `E1.rosserAsymp_of_two_le`.  For `s ≤ 3` all `T⁺(y, y^{1/s})` equal `σ⁺(y)`
(`M06.I1`), and `σ⁺(y) = S⁺(z, s')` with `z = ⌈y⌉ − 1`, `s' = 3 log z / log y` (so `z^{1/s'} = y^{1/3}`). -/

lemma m06_mertens (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun x : ℝ => VB b x * Real.log x) atTop (𝓝 (kappaB b)) := by
  have hκ := kappaB_pos b
  rw [tendsto_order]
  constructor
  · intro a ha
    set η := (kappaB b - a) / (2 * kappaB b) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨x0, _, h⟩ := E1.VB_log_bounds b hb hη0
    filter_upwards [eventually_ge_atTop x0] with x hx
    have := (h x hx).1
    have e : (1 - η) * kappaB b = kappaB b - (kappaB b - a) / 2 := by rw [hη]; field_simp
    linarith
  · intro a ha
    set η := (a - kappaB b) / (2 * kappaB b) with hη
    have hη0 : 0 < η := by
      have : 0 < a - kappaB b := by linarith
      positivity
    obtain ⟨x0, _, h⟩ := E1.VB_log_bounds b hb hη0
    filter_upwards [eventually_ge_atTop x0] with x hx
    have := (h x hx).2
    have e : (1 + η) * kappaB b = kappaB b + (a - kappaB b) / 2 := by rw [hη]; field_simp
    linarith

/-- For `s ≤ 3`, `T⁺(y, y^{1/s}) = T⁺(y, y^{1/3})`. -/
lemma m06_collapse (b : ℕ) {y s : ℝ} (hy : 1 ≤ y) (hs : 0 < s) (hs3 : s ≤ 3) :
    Tpm b true y (y ^ (1 / s)) = Tpm b true y (y ^ ((1 : ℝ) / 3)) := by
  have h1 := M06.I1 b (by linarith : 0 < y) (y ^ (1 / s))
  have h2 := M06.I1 b (by linarith : 0 < y) (y ^ ((1 : ℝ) / 3))
  have hw : y ^ ((1 : ℝ) / 3) ≤ y ^ (1 / s) :=
    Real.rpow_le_rpow_of_exponent_le hy (by rw [div_le_div_iff₀ (by norm_num) hs]; linarith)
  have e1 : ((primesBelow (y ^ ((1 : ℝ) / 3))).filter (fun p : ℕ => y ^ (1 / s) ≤ (p : ℝ))) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro p hp
    have := ((mem_primesBelow _ p).1 hp).2
    linarith
  have e2 : ((primesBelow (y ^ ((1 : ℝ) / 3))).filter (fun p : ℕ => y ^ ((1 : ℝ) / 3) ≤ (p : ℝ))) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro p hp
    have := ((mem_primesBelow _ p).1 hp).2
    linarith
  rw [h1, h2, e1, e2]

noncomputable def m06z (y : ℝ) : ℝ := (⌈y⌉₊ : ℝ) - 1

noncomputable def m06s (y : ℝ) : ℝ := 3 * Real.log (m06z y) / Real.log y

lemma m06_z_bounds {y : ℝ} (hy : 4 ≤ y) : y - 1 ≤ m06z y ∧ m06z y < y := by
  unfold m06z
  have h1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  constructor <;> linarith

lemma m06_logz {y : ℝ} (hy : 4 ≤ y) :
    Real.log y - Real.log 2 ≤ Real.log (m06z y) ∧ Real.log (m06z y) ≤ Real.log y := by
  obtain ⟨h1, h2⟩ := m06_z_bounds hy
  constructor
  · have : Real.log (y / 2) ≤ Real.log (m06z y) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_div (by linarith) (by norm_num)] at this
  · exact Real.log_le_log (by linarith) h2.le

lemma m06_s_tendsto : Tendsto m06s atTop (𝓝 3) := by
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hlow : Tendsto (fun y : ℝ => 3 - 3 * Real.log 2 / Real.log y) atTop (𝓝 3) := by
    have := (tendsto_const_nhds (x := 3 * Real.log 2)).div_atTop hL
    simpa using (tendsto_const_nhds (x := (3 : ℝ))).sub this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
    have hLy : 0 < Real.log y := Real.log_pos (by linarith)
    have := (m06_logz hy).1
    unfold m06s
    rw [le_div_iff₀ hLy]
    have e : (3 - 3 * Real.log 2 / Real.log y) * Real.log y = 3 * Real.log y - 3 * Real.log 2 := by
      field_simp
    rw [e]; linarith
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
    have hLy : 0 < Real.log y := Real.log_pos (by linarith)
    have := (m06_logz hy).2
    unfold m06s
    rw [div_le_iff₀ hLy]; linarith

lemma m06_z_tendsto : Tendsto m06z atTop atTop := by
  apply tendsto_atTop_mono' _ _ (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with y hy
  have := (m06_z_bounds hy).1
  simp only [id]; linarith

lemma m06_pow (y : ℝ) (hy : 4 ≤ y) :
    (m06z y) ^ (1 / m06s y) = y ^ ((1 : ℝ) / 3) := by
  have hz := m06_z_bounds hy
  have hz0 : 0 < m06z y := by linarith [hz.1]
  have hLz : 0 < Real.log (m06z y) := Real.log_pos (by linarith [hz.1])
  have hLy : 0 < Real.log y := Real.log_pos (by linarith)
  rw [Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos (by linarith)]
  congr 1
  unfold m06s
  field_simp

lemma m06_Tpm_eq_Splus (b : ℕ) (y : ℝ) (hy : 4 ≤ y) :
    Tpm b true y (y ^ ((1 : ℝ) / 3)) = Splus b (m06z y) (m06s y) := by
  unfold Splus
  rw [m06_pow y hy, M06.Sg_eq_TS b _ (fun p hp => M06.primesBelow_prime hp) true y (m06z y)
    (M06.ceil_rel (by linarith)), M06.Tpm_eq_TS]

lemma m06_ratio1 (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun y : ℝ => Tpm b true y (y ^ ((1 : ℝ) / 3)) / VB b (y ^ ((1 : ℝ) / 3))) atTop
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / 3)) := by
  have hs := m06_s_tendsto
  have h2 : Tendsto (fun y : ℝ => 2 * Real.exp Real.eulerMascheroniConstant / m06s y) atTop
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / 3)) :=
    tendsto_const_nhds.div hs (by norm_num)
  have h0 : Tendsto (fun y : ℝ => Tpm b true y (y ^ ((1 : ℝ) / 3)) / VB b (y ^ ((1 : ℝ) / 3)) -
      2 * Real.exp Real.eulerMascheroniConstant / m06s y) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨z0, hz0⟩ := E1.rosserAsymp_of_two_le b hb (ε / 2) (by positivity)
    have hzt := m06_z_tendsto.eventually (eventually_ge_atTop z0)
    have hs2 := hs.eventually (eventually_ge_nhds (by norm_num : (2 : ℝ) < 3))
    filter_upwards [hzt, hs2, eventually_ge_atTop (4 : ℝ)] with y hz hs2 hy4
    have hs3 : m06s y ≤ 3 := by
      have := (m06_logz hy4).2
      have hLy : 0 < Real.log y := Real.log_pos (by linarith)
      unfold m06s
      rw [div_le_iff₀ hLy]; linarith
    have hmain := (hz0 (m06z y) hz).1 (m06s y) (by linarith) (by linarith)
    have hFC : FjrC (m06s y) = 2 * Real.exp Real.eulerMascheroniConstant / m06s y := by
      unfold FjrC
      rw [if_neg (by intro h; rw [h] at hs2; norm_num at hs2)]
      exact Fjr_eq (by linarith) hs3
    rw [hFC, m06_pow y hy4, ← m06_Tpm_eq_Splus b y hy4] at hmain
    have hV := E1.VB_pos' b (y ^ ((1 : ℝ) / 3))
    rw [Real.dist_eq, sub_zero]
    have e : Tpm b true y (y ^ ((1 : ℝ) / 3)) / VB b (y ^ ((1 : ℝ) / 3)) -
        2 * Real.exp Real.eulerMascheroniConstant / m06s y =
        (Tpm b true y (y ^ ((1 : ℝ) / 3)) - VB b (y ^ ((1 : ℝ) / 3)) *
          (2 * Real.exp Real.eulerMascheroniConstant / m06s y)) / VB b (y ^ ((1 : ℝ) / 3)) := by
      field_simp
    rw [e, abs_div, abs_of_pos hV, div_lt_iff₀ hV]
    have : |Tpm b true y (y ^ ((1 : ℝ) / 3)) - VB b (y ^ ((1 : ℝ) / 3)) *
          (2 * Real.exp Real.eulerMascheroniConstant / m06s y)| ≤ ε / 2 * VB b (y ^ ((1 : ℝ) / 3)) := by
      exact hmain
    nlinarith
  simpa using h0.add h2

lemma m06_ratio2 (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (fun y : ℝ => VB b (y ^ ((1 : ℝ) / 3)) / VB b (Real.sqrt y)) atTop (𝓝 (3 / 2)) := by
  have hκ := kappaB_pos b
  have hA : Tendsto (fun y : ℝ => VB b (y ^ ((1 : ℝ) / 3)) * Real.log (y ^ ((1 : ℝ) / 3))) atTop (𝓝 (kappaB b)) :=
    (m06_mertens b hb).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have hB : Tendsto (fun y : ℝ => VB b (Real.sqrt y) * Real.log (Real.sqrt y)) atTop (𝓝 (kappaB b)) :=
    (m06_mertens b hb).comp Real.tendsto_sqrt_atTop
  have hAB := (hA.div hB hκ.ne').const_mul (3 / 2 : ℝ)
  rw [div_self hκ.ne', mul_one] at hAB
  apply hAB.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  have hL : 0 < Real.log y := Real.log_pos hy
  have h1 : Real.log (y ^ ((1 : ℝ) / 3)) = Real.log y / 3 := by
    rw [Real.log_rpow (by linarith)]; ring
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt (by linarith)
  have hV := E1.VB_pos' b (Real.sqrt y)
  simp only [Pi.div_apply]
  rw [h1, h2]
  field_simp

theorem itemM06 : ItemM06 := by
  intro b hb ε hε
  have hR : Tendsto (fun y : ℝ => Tpm b true y (y ^ ((1 : ℝ) / 3)) / VB b (Real.sqrt y)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
    have := (m06_ratio1 b hb).mul (m06_ratio2 b hb)
    have e : 2 * Real.exp Real.eulerMascheroniConstant / 3 * (3 / 2) = Real.exp Real.eulerMascheroniConstant := by
      ring
    rw [e] at this
    apply this.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hV := E1.VB_pos' b (y ^ ((1 : ℝ) / 3))
    field_simp
  rw [Metric.tendsto_nhds] at hR
  obtain ⟨y1, hy1⟩ := eventually_atTop.1 (hR ε hε)
  refine ⟨max y1 1, fun y hy s hs hs3 => ?_⟩
  have hy1' := hy1 y (le_trans (le_max_left _ _) hy)
  have hy0 : 1 ≤ y := le_trans (le_max_right _ _) hy
  rw [m06_collapse b hy0 hs hs3]
  have hV := E1.VB_pos' b (Real.sqrt y)
  rw [Real.dist_eq] at hy1'
  have e : Tpm b true y (y ^ ((1 : ℝ) / 3)) - Real.exp Real.eulerMascheroniConstant * VB b (Real.sqrt y) =
      (Tpm b true y (y ^ ((1 : ℝ) / 3)) / VB b (Real.sqrt y) - Real.exp Real.eulerMascheroniConstant) *
        VB b (Real.sqrt y) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hV]
  exact mul_le_mul_of_nonneg_right hy1'.le hV.le

end KappaOmega2
