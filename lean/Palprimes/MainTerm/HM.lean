import Palprimes.MainTerm.Identify

/-! # Hypothesis HM of the Ω ≤ 4 skeleton from E1

`HM_of_E1`: under Greaves' Lemma 4.2 (`RosserAsymp b`), `T₀ ≥ 1/8` and `𝓜 > 0`,
`MT(x^θ) ≥ c / log x` for all large `N`, `x = b^{2N+1}`. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology

namespace Palprimes.MT

open Palprimes.Greaves

theorem MT_lower (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hT8 : 1 / 8 ≤ P.T0) (hM : 0 < Mval P) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y → c / Real.log y ≤ MT P b y := by
  have hT9 : 1 / 9 ≤ P.T0 := by linarith
  set L := 2 * Real.exp Real.eulerMascheroniConstant * Mval P
  have hL : 0 < L := by positivity
  have ht := MT_tendsto P b hb hE1 hT9
  rw [limit_eq P hT8] at ht
  have h1 : ∀ᶠ y in atTop, L / 2 < MT P b y / VB b y := (tendsto_order.1 ht).1 (L / 2) (by linarith)
  obtain ⟨C, hC0, hC⟩ := VB_log b hb
  set κ := kappaB b
  have hκ : 0 < κ := kappaB_pos b
  have h2 : ∀ᶠ y : ℝ in atTop, κ / 2 ≤ VB b y * Real.log y := by
    have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop ((Palprimes.bigB b : ℝ) + 4),
      hlog.eventually (eventually_ge_atTop (2 * C / κ + 1))] with y hy hly
    have := hC y hy
    have hlpos : 0 < Real.log y := by have : 0 ≤ 2 * C / κ := by positivity
                                      linarith
    have hCl : C / Real.log y ≤ κ / 2 := by
      rw [div_le_iff₀ hlpos]
      have := (div_le_iff₀ hκ).1 (show 2 * C / κ ≤ Real.log y by linarith)
      linarith
    have := (abs_le.1 this).1
    linarith
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (h1.and (h2.and (eventually_gt_atTop 1)))
  refine ⟨L / 2 * (κ / 2), by positivity, max Y 2, by linarith [le_max_right Y 2], fun y hy => ?_⟩
  obtain ⟨hy1, hy2, hy3⟩ := hY y (le_trans (le_max_left _ _) hy)
  have hV := VB_pos b y
  have hlpos : 0 < Real.log y := Real.log_pos hy3
  have hMT : L / 2 * VB b y ≤ MT P b y := by
    have := (lt_div_iff₀ hV).1 hy1; linarith
  rw [div_le_iff₀ hlpos]
  calc L / 2 * (κ / 2) ≤ L / 2 * (VB b y * Real.log y) := mul_le_mul_of_nonneg_left hy2 (by positivity)
    _ = L / 2 * VB b y * Real.log y := by ring
    _ ≤ MT P b y * Real.log y := mul_le_mul_of_nonneg_right hMT hlpos.le

/-- **HM from E1.** -/
theorem HM_of_E1 (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hT8 : 1 / 8 ≤ P.T0) (hM : 0 < Mval P)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₃ : ℕ, ∀ N ≥ N₃,
      c / Real.log ((b : ℝ) ^ (2 * N + 1)) ≤ MT P b (((b : ℝ) ^ (2 * N + 1)) ^ θ) := by
  obtain ⟨c, hc, Y, hY1, hY⟩ := MT_lower P b hb hE1 hT8 hM
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hx : Tendsto (fun N : ℕ => (b : ℝ) ^ (2 * N + 1)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro N
    have h1 : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ N ≤ (b : ℝ) ^ N := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hb) N
    have h3 : (b : ℝ) ^ N ≤ (b : ℝ) ^ (2 * N + 1) := pow_le_pow_right₀ hb1.le (by omega)
    linarith
  have hy := (tendsto_rpow_atTop hθ).comp hx
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hy.eventually (eventually_ge_atTop Y))
  refine ⟨c / θ, by positivity, N₃, fun N hN => ?_⟩
  have hyN := hN₃ N hN
  simp only [Function.comp] at hyN
  have hlx : 0 < Real.log ((b : ℝ) ^ (2 * N + 1)) := Real.log_pos (one_lt_pow₀ hb1 (by omega))
  have hle := hY _ hyN
  rw [Real.log_rpow (by positivity)] at hle
  calc c / θ / Real.log ((b : ℝ) ^ (2 * N + 1)) = c / (θ * Real.log ((b : ℝ) ^ (2 * N + 1))) := by
        rw [div_div]
    _ ≤ _ := hle

end Palprimes.MT
