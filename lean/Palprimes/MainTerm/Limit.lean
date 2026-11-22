import Palprimes.MainTerm.FchReg

/-! # The limit of `MT / V(y)`

`Ich P n = ∫_{(log T₀, 0]^{n+1}} fch`, `Ibig P = ∫_{(log T₀, 0]} fbig`.
`MT_tendsto`: under E1, `MT(y)/V(y) → Ibig + Σ_{n<8} Ich n`. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Palprimes.MT

open Palprimes.Greaves

theorem T0_pos (P : WPar) : 0 < P.T0 := by have := P.hT0; have := P.hU1; linarith [show 0 < (1 - P.U) / 3 by linarith]
theorem T0_lt_one (P : WPar) : P.T0 < 1 := by have := P.hT1; linarith

theorem box_exp_bounds {r : ℕ} (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (σ : Fin r → ℝ)
    (h : σ ∈ Box.Icc (boxA r a ha0 ha1)) (i : Fin r) : a ≤ Real.exp (σ i) ∧ Real.exp (σ i) ≤ 1 := by
  rw [Box.Icc_def, Set.mem_Icc] at h
  have h1 : Real.log a ≤ σ i := h.1 i
  have h2 : σ i ≤ 0 := h.2 i
  constructor
  · calc a = Real.exp (Real.log a) := (Real.exp_log ha0).symm
      _ ≤ _ := Real.exp_le_exp.2 h1
  · calc Real.exp (σ i) ≤ Real.exp 0 := Real.exp_le_exp.2 h2
      _ = 1 := Real.exp_zero

theorem fch_bound (P : WPar) (hT9 : 1 / 9 ≤ P.T0) (n : ℕ) (σ : Fin (n + 1) → ℝ)
    (h : σ ∈ Box.Icc (boxA (n + 1) P.T0 (T0_pos P) (T0_lt_one P))) :
    ‖fch P n σ‖ ≤ (P.U - P.V) * CG / P.T0 := by
  classical
  have hT := T0_pos P
  have hw1 := P.UV_pos
  have hM : 0 ≤ (P.U - P.V) * CG / P.T0 := by have := CG_pos; positivity
  rw [fch_eq, Real.norm_eq_abs]
  split_ifs
  · unfold gch
    set x := Real.exp (σ (Fin.last n))
    have hx := box_exp_bounds P.T0 hT (T0_lt_one P) σ h (Fin.last n)
    have hx0 : 0 < x := lt_of_lt_of_le hT hx.1
    have hS : 0 ≤ ∑ i, Real.exp (σ i) := Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
    have hs9 : (1 - ∑ i, Real.exp (σ i)) / x ≤ 9 := by
      rw [div_le_iff₀ hx0]
      have : 1 ≤ 9 * P.T0 := by linarith
      nlinarith [hx.1]
    obtain ⟨hG0, hG1⟩ := Gs_bounds (stF false (n + 1)) _ hs9
    have hW0 := P.W_nonneg x
    have hW1 := P.W_le x
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hW0,
      abs_of_nonneg hG0, abs_of_pos hx0]
    calc P.W x * Gs (stF false (n + 1)) ((1 - ∑ i, Real.exp (σ i)) / x) / x ≤ (P.U - P.V) * CG / x :=
          div_le_div_of_nonneg_right (mul_le_mul hW1 hG1 hG0 hw1.le) hx0.le
      _ ≤ (P.U - P.V) * CG / P.T0 := div_le_div_of_nonneg_left (by have := CG_pos; positivity) hT hx.1
  · simpa using hM

/-! ## `fbig` -/

noncomputable def gbig (P : WPar) (σ : Fin 1 → ℝ) : ℝ :=
  (P.W (Real.exp (σ 0)) - (P.U - P.V)) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - Real.exp (σ 0))

theorem fbig_eq (P : WPar) (σ : Fin 1 → ℝ) :
    fbig P σ = open Classical in if 1 / 2 ≤ Real.exp (σ 0) then gbig P σ else 0 := by
  classical
  unfold fbig gbig
  by_cases h : 1 / 2 ≤ Real.exp (σ 0)
  · rw [if_pos h]
  · rw [if_neg h]

noncomputable def Bbig (P : WPar) : Finset ((Fin 1 → ℝ) × ℝ) :=
  ({1 / 2, P.T0, 1 / 4, P.U, 1} : Finset ℝ).image (fun c => (fun _ => (1 : ℝ), c))

theorem fbig_continuousAt (P : WPar) (σ0 : Fin 1 → ℝ)
    (hg : ∀ p ∈ Bbig P, ∑ i, p.1 i * Real.exp (σ0 i) ≠ p.2) : ContinuousAt (fbig P) σ0 := by
  classical
  have hv : ∀ c ∈ ({1 / 2, P.T0, 1 / 4, P.U, 1} : Finset ℝ), Real.exp (σ0 0) ≠ c := by
    intro c hc
    have := hg _ (Finset.mem_image.2 ⟨c, hc, rfl⟩)
    simpa using this
  have cE : Continuous (fun σ : Fin 1 → ℝ => Real.exp (σ 0)) := Real.continuous_exp.comp (continuous_apply 0)
  apply continuousAt_ite_of_eventually (fbig P) (gbig P) (fun σ => 1 / 2 ≤ Real.exp (σ 0)) σ0 (fbig_eq P)
  · have := eventually_le_iff (fun σ : Fin 1 → ℝ => 1 / 2 - Real.exp (σ 0)) σ0
      (continuous_const.sub cE).continuousAt 0 (by intro h; exact hv (1 / 2) (by simp) (by linarith))
    filter_upwards [this] with σ hσ
    constructor
    · intro h1; have := hσ.1 (by linarith); linarith
    · intro h1; have := hσ.2 (by linarith); linarith
  · intro _
    unfold gbig
    have hW : ContinuousAt (fun σ : Fin 1 → ℝ => P.W (Real.exp (σ 0))) σ0 :=
      ContinuousAt.comp (g := P.W) (W_continuousAt P _ (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)))
        cE.continuousAt
    have h1 : 1 - Real.exp (σ0 0) ≠ 0 := by
      intro h; exact hv 1 (by simp) (by linarith)
    exact ((hW.sub continuousAt_const).mul continuousAt_const).div (continuous_const.sub cE).continuousAt h1

theorem fbig_ae_continuous (P : WPar) : ∀ᵐ σ ∂(volume : Measure (Fin 1 → ℝ)), ContinuousAt (fbig P) σ := by
  apply ae_continuousAt_of_bad (fbig P) (Bbig P) _ (fbig_continuousAt P)
  intro p hp
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hp
  intro h; have := congr_fun h 0; simp at this

theorem fbig_measurable (P : WPar) : Measurable (fbig P) := by
  classical
  have cE : Continuous (fun σ : Fin 1 → ℝ => Real.exp (σ 0)) := Real.continuous_exp.comp (continuous_apply 0)
  have : fbig P = fun σ => if 1 / 2 ≤ Real.exp (σ 0) then gbig P σ else 0 := funext (fbig_eq P)
  rw [this]
  refine Measurable.ite (measurableSet_le measurable_const cE.measurable) ?_ measurable_const
  unfold gbig
  exact ((((W_measurable P).comp cE.measurable).sub measurable_const).mul measurable_const).div
    (measurable_const.sub cE.measurable)

theorem fbig_bound (P : WPar) (σ : Fin 1 → ℝ)
    (h : σ ∈ Box.Icc (boxA 1 P.T0 (T0_pos P) (T0_lt_one P))) :
    ‖fbig P σ‖ ≤ (P.U - P.V) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - P.U) := by
  classical
  have hw1 := P.UV_pos
  have hU1 : 0 < 1 - P.U := by have := P.hU1; linarith
  have hM : 0 ≤ (P.U - P.V) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - P.U) := by positivity
  rw [fbig_eq, Real.norm_eq_abs]
  split_ifs with h2
  · unfold gbig
    set t := Real.exp (σ 0)
    by_cases htU : P.U < t
    · rw [W_gt_U P t htU, sub_self, zero_mul, zero_div, abs_zero]; exact hM
    · push_neg at htU
      have h1t : 0 < 1 - t := by linarith
      have hW0 := P.W_nonneg t
      have hW1 := P.W_le t
      rw [abs_div, abs_mul, abs_of_pos h1t, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp Real.eulerMascheroniConstant)]
      have ha : |P.W t - (P.U - P.V)| ≤ P.U - P.V := by rw [abs_le]; constructor <;> linarith
      calc |P.W t - (P.U - P.V)| * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - t)
          ≤ (P.U - P.V) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - t) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity)) h1t.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hU1 (by linarith)
  · simpa using hM

/-! ## Integrability on the boxes -/

theorem integrableOn_box {r : ℕ} (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (f : (Fin r → ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x ∈ Box.Icc (boxA r a ha0 ha1), ‖f x‖ ≤ C) :
    IntegrableOn f (boxA r a ha0 ha1 : Set (Fin r → ℝ)) := by
  apply IntegrableOn.of_bound ((boxA r a ha0 ha1).measure_coe_lt_top volume) hf.aestronglyMeasurable C
  exact ae_restrict_of_forall_mem (boxA r a ha0 ha1).measurableSet_coe
    (fun x hx => hC x (Box.coe_subset_Icc hx))

noncomputable def Ich (P : WPar) (n : ℕ) : ℝ :=
  ∫ σ in (boxA (n + 1) P.T0 (T0_pos P) (T0_lt_one P) : Set (Fin (n + 1) → ℝ)), fch P n σ

noncomputable def Ibig (P : WPar) : ℝ :=
  ∫ σ in (boxA 1 P.T0 (T0_pos P) (T0_lt_one P) : Set (Fin 1 → ℝ)), fbig P σ

theorem MainY_tendsto (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hT9 : 1 / 9 ≤ P.T0) :
    Tendsto (fun y => MainY P b y / VB b y) atTop (𝓝 (Ibig P + ∑ n ∈ Finset.range 8, Ich P n)) := by
  have hbig := prime_sum_tendsto b hb P.T0 (T0_pos P) (T0_lt_one P) (fbig P)
    ⟨_, fbig_bound P⟩ (fbig_ae_continuous P)
    (integrableOn_box _ _ _ _ (fbig_measurable P) _ (fbig_bound P))
  have hch : ∀ n ∈ Finset.range 8, Tendsto (fun y => ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Pset y P.T0),
      (∏ i, gB b (q i)) * fch P n (sigv y q)) atTop (𝓝 (Ich P n)) := by
    intro n _
    exact prime_sum_tendsto b hb P.T0 (T0_pos P) (T0_lt_one P) (fch P n)
      ⟨_, fch_bound P hT9 n⟩ (fch_ae_continuous P n)
      (integrableOn_box _ _ _ _ (fch_measurable P n) _ (fch_bound P hT9 n))
  have hsum := hbig.add (tendsto_finsetSum _ hch)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 1] with y hy
  rw [MainY_eq P b y hy hT9, mul_div_cancel_left₀ _ (VB_pos b y).ne']

/-- **The main term, normalised, converges** (under E1). -/
theorem MT_tendsto (P : WPar) (b : ℕ) (hb : 2 ≤ b) (hE1 : RosserAsymp b) (hT9 : 1 / 9 ≤ P.T0) :
    Tendsto (fun y => MT P b y / VB b y) atTop (𝓝 (Ibig P + ∑ n ∈ Finset.range 8, Ich P n)) := by
  have hdiff : Tendsto (fun y => MT P b y / VB b y - MainY P b y / VB b y) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [MT_approx P b hb hE1 hT9 (ε / 2) (by positivity)] with y hy
    have hV := VB_pos b y
    rw [Real.dist_eq, sub_zero, ← sub_div, abs_div, abs_of_pos hV, div_lt_iff₀ hV]
    have : ε / 2 * VB b y < ε * VB b y := by nlinarith
    linarith
  have := hdiff.add (MainY_tendsto P b hb hT9)
  simp only [zero_add, sub_add_cancel] at this
  exact this

end Palprimes.MT
