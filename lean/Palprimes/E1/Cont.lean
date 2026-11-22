import Mathlib

set_option linter.style.longLine false

/-! # E1, phase E3: continuous boundary functions and the Iwaniec 1971 majorant

Blueprint `lean/e1/E1_BLUEPRINT.md` §3.1 (B.0, B.1), §4.1 (C.0, C.1, C.5).

* `betaP k`, `betaM k`: the normalised boundary functions `β⁺_k`, `β⁻_k` (B.0), defined for all real `s`
  by set integrals over `Ioi`:
  `β⁺_0 s = max (3/s - 1) 0`, `β⁻_0 = 0`, `β⁻_{k+1} s = s⁻¹ ∫_{Ioi (s-1)} β⁺_k`,
  `β⁺_{k+1} s = s⁻¹ ∫_{Ioi (max (s-1) 2)} β⁻_{k+1}`.
  Only `s ≥ 1` (for `β⁺`) and `s ≥ 2` (for `β⁻`, continuity already for `s > 1`) are meaningful.
* B.1: continuity (`continuousAt_betaP` on `s > 0`, `continuousAt_betaM` on `s > 1`), support
  (`betaP_eq_zero` for `s ≥ 2k+3`, `betaM_eq_zero` for `s ≥ 2k+2`), nonnegativity, integrability on `Ioi c`,
  `betaP_succ_of_le_three` (`β⁺_k(s) = (3/s) β⁺_k(3)` for `s ≤ 3`, `k ≥ 1`), interval-integral forms.
* C.0: majorants `mPlus s = if s ≤ 3 then 3 e^{-3}/s else e^{-s}`, `mMinus s = e^{-s}`.
* C.1: kernel inequalities `kernel_minus` (constant `theta1 = 4/5`) and `kernel_plus` (`theta2 = e/3`),
  rate `rateA = theta1 * theta2 = 4e/15 < 0.725`. The sup of `ψ` on `[2,4]` is bounded by a 36-cell mesh
  (`psiK_le`), one pair of `norm_num` goals per cell.
* C.5: `betaP_le` (`β⁺_k ≤ c₀ A^k m⁺` on `s ≥ 1`), `betaM_succ_le` (`β⁻_{k+1} ≤ c₀ θ₁ A^k m⁻` on `s ≥ 2`),
  `c₀ = 2e³/3`; uniform forms `≤ 2 A^k`; summability and geometric tails of `∑ β±_k`.
* Inputs for C.2: `mPlus_sub_one_le` (`m⁺(s-1) ≤ e m⁻(s)`, `s ≥ 2`), monotonicity, and the layer-cake form
  `muPlus` (`μ⁺ = -(m⁺)'`): `integral_muPlus_Ioi` (`m⁺(t) = ∫_{u>t} μ⁺`), `integral_muPlus_mul_sub`
  (`∫_{u>a} μ⁺(u)(u-a) = ∫_{u>a} m⁺`).
* Bridge: `log_div_log_rpow_cont` (`log z / log (z^(1/s)) = s`).
-/


open MeasureTheory Set Real Filter Topology

namespace Palprimes.E1

/-! ## Bridge lemma `log z / log (z ^ (1/s)) = s` -/

theorem log_div_log_rpow_cont {z s : ℝ} (hz : 1 < z) (hs : 0 < s) :
    Real.log z / Real.log (z ^ (1 / s)) = s := by
  have hl : 0 < Real.log z := Real.log_pos hz
  rw [Real.log_rpow (by linarith) (1 / s)]
  field_simp

/-! ## Generic facts on tail integrals of continuous, eventually vanishing functions -/

section Generic

variable {f : ℝ → ℝ} {c M : ℝ}

lemma integrableOn_Ioi_of_cont (hf : ∀ x, c < x → ContinuousAt f x) (hM : ∀ x, M ≤ x → f x = 0)
    {a : ℝ} (ha : c < a) : IntegrableOn f (Ioi a) := by
  have hcont : ContinuousOn f (Icc a (max a M)) :=
    fun x hx => (hf x (ha.trans_le hx.1)).continuousWithinAt
  have h1 : IntegrableOn f (Ioc a (max a M)) := hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn f (Ioi (max a M)) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi (max a M))).congr_fun
      (fun x hx => (hM x ((le_max_right a M).trans (le_of_lt hx))).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (le_max_left a M)]
  exact h1.union h2

lemma setIntegral_Ioi_eq_intervalIntegral (hf : ∀ x, c < x → ContinuousAt f x)
    (hM : ∀ x, M ≤ x → f x = 0) {a N : ℝ} (ha : c < a) (hN : M ≤ N) :
    ∫ x in Ioi a, f x = ∫ x in a..N, f x := by
  rcases le_or_gt a N with haN | hNa
  · have hi := integrableOn_Ioi_of_cont hf hM ha
    rw [intervalIntegral.integral_of_le haN, ← Ioc_union_Ioi_eq_Ioi haN,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi haN)),
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioi N) (fun x hx => hM x (hN.trans (le_of_lt hx))), add_zero]
  · rw [setIntegral_eq_zero_of_forall_eq_zero (t := Ioi a) (fun x hx => hM x (by linarith [mem_Ioi.mp hx])),
      intervalIntegral.integral_symm, intervalIntegral.integral_of_le hNa.le,
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioc N a) (fun x hx => hM x (hN.trans hx.1.le)), neg_zero]

lemma continuousAt_setIntegral_Ioi (hf : ∀ x, c < x → ContinuousAt f x)
    (hM : ∀ x, M ≤ x → f x = 0) {x : ℝ} (hx : c < x) :
    ContinuousAt (fun a => ∫ t in Ioi a, f t) x := by
  set a₀ := (c + x) / 2 with ha₀
  set N := max M (x + 1) with hN
  have hc0 : c < a₀ := by rw [ha₀]; linarith
  have hx0 : a₀ < x := by rw [ha₀]; linarith
  have hxN : x < N := by rw [hN]; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have ha₀N : a₀ ≤ N := by linarith
  have hint : IntegrableOn f (uIcc a₀ N) := by
    rw [uIcc_of_le ha₀N]
    exact ContinuousOn.integrableOn_Icc fun y hy => (hf y (hc0.trans_le hy.1)).continuousWithinAt
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hint
  rw [uIcc_of_le ha₀N] at hcont
  have heq : EqOn (fun a => ∫ t in Ioi a, f t) (fun a => ∫ t in a..N, f t) (Icc a₀ N) :=
    fun a ha => setIntegral_Ioi_eq_intervalIntegral hf hM (hc0.trans_le ha.1) (le_max_left _ _)
  exact (hcont.congr heq).continuousAt (Icc_mem_nhds hx0 hxN)

end Generic

/-! ## Definitions (B.0, C.0, C.1 constants) -/

/-- `β⁺_k` (blueprint B.0): `β⁺_0 s = max (3/s - 1) 0`,
`β⁺_{k+1} s = s⁻¹ ∫_{u > max (s-1) 2} β⁻_{k+1}(u)` (with `β⁻_{k+1}` unfolded). -/
noncomputable def betaP : ℕ → ℝ → ℝ
  | 0 => fun s => max (3 / s - 1) 0
  | k + 1 => fun s => s⁻¹ * ∫ u in Ioi (max (s - 1) 2), (u⁻¹ * ∫ v in Ioi (u - 1), betaP k v)

/-- `β⁻_k` (blueprint B.0): `β⁻_0 = 0`, `β⁻_{k+1} s = s⁻¹ ∫_{u > s-1} β⁺_k(u)`. -/
noncomputable def betaM : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun s => s⁻¹ * ∫ u in Ioi (s - 1), betaP k u

lemma betaP_zero (s : ℝ) : betaP 0 s = max (3 / s - 1) 0 := rfl

lemma betaM_zero (s : ℝ) : betaM 0 s = 0 := rfl

lemma betaM_succ (k : ℕ) (s : ℝ) : betaM (k + 1) s = s⁻¹ * ∫ u in Ioi (s - 1), betaP k u := rfl

lemma betaP_succ (k : ℕ) (s : ℝ) :
    betaP (k + 1) s = s⁻¹ * ∫ u in Ioi (max (s - 1) 2), betaM (k + 1) u := rfl

/-- `β⁺_0(s) = 3/s - 1` for `0 < s ≤ 3`. -/
lemma betaP_zero_of_le_three {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 3) : betaP 0 s = 3 / s - 1 := by
  rw [betaP_zero, max_eq_left]
  rw [sub_nonneg, le_div_iff₀ hs0]; linarith

/-- `s β⁺_0(s) = (3 - s)₊` for `s > 0`. -/
lemma mul_betaP_zero {s : ℝ} (hs : 0 < s) : s * betaP 0 s = max (3 - s) 0 := by
  rw [betaP_zero, mul_max_of_nonneg _ _ hs.le, mul_zero, mul_sub, mul_div_cancel₀ _ hs.ne', mul_one]

/-- Majorant `m⁺` (C.0): `3 e^{-3}/s` on `s ≤ 3`, `e^{-s}` on `s > 3`. -/
noncomputable def mPlus (s : ℝ) : ℝ := if s ≤ 3 then 3 * exp (-3) / s else exp (-s)

/-- Majorant `m⁻` (C.0): `e^{-s}`. -/
noncomputable def mMinus (s : ℝ) : ℝ := exp (-s)

/-- `θ₁ = 4/5` (C.1; any value `≥ max (e/4) (sup_{[2,4]} ψ)` works, `sup ψ = ψ(2) ≈ 0.790`). -/
noncomputable def theta1 : ℝ := 4 / 5

/-- `θ₂ = e/3` (C.1). -/
noncomputable def theta2 : ℝ := exp 1 / 3

/-- The rate per depth `A = θ₁ θ₂ = 4e/15 < 0.725`. -/
noncomputable def rateA : ℝ := theta1 * theta2

/-- `c₀ = 2 e³/3` (C.5). -/
noncomputable def c0 : ℝ := 2 * exp 3 / 3

/-! ## Constants -/

lemma theta1_eq : theta1 = 4 / 5 := rfl

lemma theta1_pos : 0 < theta1 := by rw [theta1]; norm_num

lemma theta2_pos : 0 < theta2 := by rw [theta2]; positivity

lemma rateA_eq : rateA = 4 * exp 1 / 15 := by rw [rateA, theta1, theta2]; ring

lemma rateA_pos : 0 < rateA := mul_pos theta1_pos theta2_pos

lemma rateA_nonneg : 0 ≤ rateA := rateA_pos.le

lemma rateA_lt : rateA < 0.725 := by
  rw [rateA_eq]; have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith

lemma rateA_lt_one : rateA < 1 := rateA_lt.trans (by norm_num)

lemma c0_pos : 0 < c0 := by rw [c0]; positivity

lemma c0_mul_mPlus_one : c0 * (3 * exp (-3)) = 2 := by
  have h : exp 3 * exp (-3) = 1 := by rw [← exp_add]; simp
  rw [c0, show 2 * exp 3 / 3 * (3 * exp (-3)) = 2 * (exp 3 * exp (-3)) by ring, h, mul_one]

lemma c0_theta1_exp : c0 * theta1 * exp (-2) = 2 * rateA := by
  have h : exp 3 * exp (-2) = exp 1 := by rw [← exp_add]; norm_num
  rw [c0, rateA, theta2, show 2 * exp 3 / 3 * theta1 * exp (-2) = 2 * theta1 * (exp 3 * exp (-2)) / 3 by ring, h]
  ring

/-! ## The majorants -/

lemma mPlus_of_le {s : ℝ} (hs : s ≤ 3) : mPlus s = 3 * exp (-3) / s := by
  unfold mPlus; simp [hs]

lemma mPlus_of_ge {s : ℝ} (hs : 3 ≤ s) : mPlus s = exp (-s) := by
  rcases hs.lt_or_eq with h | h
  · unfold mPlus; simp [not_le.mpr h]
  · subst h; rw [mPlus_of_le le_rfl]; ring

lemma mPlus_eq (s : ℝ) : mPlus s = 3 * exp (-3) / min s 3 * exp (3 - max s 3) := by
  rcases le_total s 3 with h | h
  · rw [mPlus_of_le h, min_eq_left h, max_eq_right h]; simp
  · rw [mPlus_of_ge h, min_eq_right h, max_eq_left h,
      show exp (-s) = exp (-3) * exp (3 - s) by rw [← exp_add]; ring_nf]
    ring

lemma mPlus_pos {s : ℝ} (hs : 0 < s) : 0 < mPlus s := by
  rw [mPlus_eq]; have : 0 < min s 3 := lt_min hs (by norm_num); positivity

lemma mMinus_pos (s : ℝ) : 0 < mMinus s := exp_pos _

lemma mPlus_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : mPlus t ≤ mPlus s := by
  rw [mPlus_eq, mPlus_eq]
  have h0 : 0 < min s 3 := lt_min hs (by norm_num)
  refine mul_le_mul (div_le_div_of_nonneg_left (by positivity) h0 (min_le_min_right 3 hst))
    (exp_le_exp.mpr (by linarith [max_le_max_right 3 hst])) (by positivity) ?_
  have : 0 < min t 3 := lt_min (hs.trans_le hst) (by norm_num)
  positivity

lemma mMinus_anti {s t : ℝ} (hst : s ≤ t) : mMinus t ≤ mMinus s :=
  exp_le_exp.mpr (by linarith)

lemma mPlus_le_of_one_le {s : ℝ} (hs : 1 ≤ s) : mPlus s ≤ 3 * exp (-3) := by
  have := mPlus_anti one_pos hs
  rwa [mPlus_of_le (by norm_num : (1 : ℝ) ≤ 3), div_one] at this

lemma mMinus_le_of_two_le {s : ℝ} (hs : 2 ≤ s) : mMinus s ≤ 3 * exp (-3) := by
  have h1 : exp (-s) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
  have h2 : exp (-2) = exp 1 * exp (-3) := by rw [← exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h3 : exp 1 * exp (-3) ≤ 3 * exp (-3) :=
    mul_le_mul_of_nonneg_right (by norm_num at he ⊢; linarith) (exp_pos _).le
  unfold mMinus; linarith

lemma mPlus_three_exp_lt_one : 3 * exp (-3 : ℝ) < 1 := by
  have h := Real.add_one_le_exp (3 : ℝ)
  rw [exp_neg]
  rw [mul_inv_lt_iff₀ (exp_pos 3)]
  linarith

/-- `m⁺(s-1) ≤ e m⁻(s)` for `s ≥ 2` (used in C.2). -/
lemma mPlus_sub_one_le {s : ℝ} (hs : 2 ≤ s) : mPlus (s - 1) ≤ exp 1 * mMinus s := by
  have he : exp 1 * mMinus s = exp (-(s - 1)) := by rw [mMinus, ← exp_add]; congr 1; ring
  rw [he]
  rcases le_total (s - 1) 3 with h | h
  · rw [mPlus_of_le h, div_le_iff₀ (by linarith)]
    set t := 4 - s with ht
    have ht0 : 0 ≤ t := by linarith
    have ht2 : t ≤ 2 := by linarith
    have hexp : exp (-t) * (1 + t) ≤ 1 := by
      rw [exp_neg, inv_mul_le_iff₀ (exp_pos t)]; linarith [Real.add_one_le_exp t]
    have h3 : 3 * exp (-t) ≤ 3 - t := by
      by_contra hcon
      have := mul_lt_mul_of_pos_right (not_le.mp hcon) (show 0 < 1 + t by linarith)
      nlinarith
    have he2 : exp (-3) = exp (-t) * exp (-(s - 1)) := by rw [← exp_add]; congr 1; rw [ht]; ring
    rw [he2]
    have hpos : 0 < exp (-(s - 1)) := exp_pos _
    nlinarith [mul_le_mul_of_nonneg_right h3 hpos.le]
  · rw [mPlus_of_ge h]

lemma continuousAt_mPlus {x : ℝ} (hx : 0 < x) : ContinuousAt mPlus x := by
  have hfun : mPlus = fun s => 3 * exp (-3) / min s 3 * exp (3 - max s 3) := funext mPlus_eq
  rw [hfun]
  have h0 : min x 3 ≠ 0 := (lt_min hx (by norm_num)).ne'
  exact (continuousAt_const.div (continuous_id.min continuous_const).continuousAt h0).mul
    (continuous_const.sub (continuous_id.max continuous_const)).rexp.continuousAt

lemma continuous_mMinus : Continuous mMinus := (continuous_neg).rexp

lemma integrableOn_mPlus {c : ℝ} (hc : 0 < c) : IntegrableOn mPlus (Ioi c) := by
  rw [← Ioc_union_Ioi_eq_Ioi (le_max_left c 3)]
  refine IntegrableOn.union ?_ ?_
  · exact (ContinuousOn.integrableOn_Icc fun y hy =>
      (continuousAt_mPlus (hc.trans_le hy.1)).continuousWithinAt).mono_set Ioc_subset_Icc_self
  · exact (integrableOn_exp_neg_Ioi (max c 3)).congr_fun
      (fun x hx => (mPlus_of_ge ((le_max_right c 3).trans (le_of_lt hx))).symm) measurableSet_Ioi

lemma integrableOn_mMinus (c : ℝ) : IntegrableOn mMinus (Ioi c) := integrableOn_exp_neg_Ioi c

lemma integral_mMinus_Ioi (a : ℝ) : ∫ u in Ioi a, mMinus u = exp (-a) := integral_exp_neg_Ioi a

lemma integral_mPlus_Ioi_of_ge {a : ℝ} (ha : 3 ≤ a) : ∫ u in Ioi a, mPlus u = exp (-a) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun u => exp (-u))
    (fun u hu => mPlus_of_ge (ha.trans (le_of_lt hu)))]
  exact integral_exp_neg_Ioi a

lemma integral_mPlus_Ioi_of_le {a : ℝ} (ha0 : 0 < a) (ha3 : a ≤ 3) :
    ∫ u in Ioi a, mPlus u = exp (-3) * (1 + 3 * log (3 / a)) := by
  have hi := integrableOn_mPlus ha0
  rw [← Ioc_union_Ioi_eq_Ioi ha3, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) (integrableOn_mPlus (by norm_num)),
    integral_mPlus_Ioi_of_ge le_rfl,
    setIntegral_congr_fun measurableSet_Ioc (g := fun u => 3 * exp (-3) * u⁻¹)
      (fun u hu => by rw [mPlus_of_le hu.2, div_eq_mul_inv]),
    integral_const_mul, ← intervalIntegral.integral_of_le ha3, integral_inv_of_pos ha0 (by norm_num)]
  ring

/-! ## `ψ` on `[2,4]` by a mesh (C.1)

`psiK s = s ψ(s) = e^{s-3} (1 + 3 log (3/(s-1)))`. On a cell `[a,b] ⊆ [2,4]`:
`psiK s ≤ E(b) (1 + 3 L(a))` with `E(b) ≥ e^{b-3}` from `Real.exp_bound` (8 terms) and
`L(a) ≥ log (3/(a-1))` certified by `3/(a-1) ≤ ∑_{i<10} L^i/i! ≤ e^L`. -/

/-- `psiK s = s ψ(s) = e^{s-3} (1 + 3 log (3/(s-1)))`. -/
noncomputable def psiK (s : ℝ) : ℝ := exp (s - 3) * (1 + 3 * log (3 / (s - 1)))

lemma psi_cell (a b L : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 4) (hL0 : 0 ≤ L)
    (hL : 3 / (a - 1) ≤ ∑ i ∈ Finset.range 10, L ^ i / (i.factorial : ℝ))
    (hmain : (∑ i ∈ Finset.range 8, (b - 3) ^ i / (i.factorial : ℝ) + 9 / 322560) * (1 + 3 * L)
      ≤ 4 / 5 * a)
    {s : ℝ} (hs1 : a ≤ s) (hs2 : s ≤ b) : psiK s ≤ 4 / 5 * s := by
  have hb3 : |b - 3| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hE := (abs_le.mp (Real.exp_bound hb3 (n := 8) (by norm_num))).2
  have hR : |b - 3| ^ 8 * (((Nat.succ 8 : ℕ) : ℝ) / (((Nat.factorial 8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ)))
      ≤ 9 / 322560 := by
    have h1 : |b - 3| ^ 8 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb3
    have h2 : (((Nat.succ 8 : ℕ) : ℝ) / (((Nat.factorial 8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ)))
        = 9 / 322560 := by norm_num [Nat.factorial]
    rw [h2]; nlinarith [pow_nonneg (abs_nonneg (b - 3)) 8]
  have hEb : exp (b - 3) ≤ ∑ i ∈ Finset.range 8, (b - 3) ^ i / (i.factorial : ℝ) + 9 / 322560 := by
    linarith
  have h1 : exp (s - 3) ≤ ∑ i ∈ Finset.range 8, (b - 3) ^ i / (i.factorial : ℝ) + 9 / 322560 :=
    (exp_le_exp.mpr (by linarith)).trans hEb
  have hLa : log (3 / (a - 1)) ≤ L :=
    (log_le_iff_le_exp (by apply div_pos <;> linarith)).mpr (hL.trans (sum_le_exp_of_nonneg hL0 10))
  have hlog : log (3 / (s - 1)) ≤ L :=
    (log_le_log (by apply div_pos <;> linarith)
      (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))).trans hLa
  have hlog0 : 0 ≤ log (3 / (s - 1)) :=
    log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  unfold psiK
  calc exp (s - 3) * (1 + 3 * log (3 / (s - 1)))
      ≤ (∑ i ∈ Finset.range 8, (b - 3) ^ i / (i.factorial : ℝ) + 9 / 322560) * (1 + 3 * L) :=
        mul_le_mul h1 (by linarith) (by linarith) ((exp_pos _).le.trans h1)
    _ ≤ 4 / 5 * a := hmain
    _ ≤ 4 / 5 * s := by linarith

private lemma psi_cell_0 {s : ℝ} (h1 : (2 : ℝ) ≤ s) (h2 : s ≤ (257 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (2 : ℝ) (257 / 128 : ℝ) (11 / 10 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_1 {s : ℝ} (h1 : (257 / 128 : ℝ) ≤ s) (h2 : s ≤ (129 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (257 / 128 : ℝ) (129 / 64 : ℝ) (273 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_2 {s : ℝ} (h1 : (129 / 64 : ℝ) ≤ s) (h2 : s ≤ (259 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (129 / 64 : ℝ) (259 / 128 : ℝ) (217 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_3 {s : ℝ} (h1 : (259 / 128 : ℝ) ≤ s) (h2 : s ≤ (261 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (259 / 128 : ℝ) (261 / 128 : ℝ) (1077 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_4 {s : ℝ} (h1 : (261 / 128 : ℝ) ≤ s) (h2 : s ≤ (263 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (261 / 128 : ℝ) (263 / 128 : ℝ) (531 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_5 {s : ℝ} (h1 : (263 / 128 : ℝ) ≤ s) (h2 : s ≤ (265 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (263 / 128 : ℝ) (265 / 128 : ℝ) (1047 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_6 {s : ℝ} (h1 : (265 / 128 : ℝ) ≤ s) (h2 : s ≤ (67 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (265 / 128 : ℝ) (67 / 32 : ℝ) (129 / 125 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_7 {s : ℝ} (h1 : (67 / 32 : ℝ) ≤ s) (h2 : s ≤ (271 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (67 / 32 : ℝ) (271 / 128 : ℝ) (1011 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_8 {s : ℝ} (h1 : (271 / 128 : ℝ) ≤ s) (h2 : s ≤ (275 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (271 / 128 : ℝ) (275 / 128 : ℝ) (989 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_9 {s : ℝ} (h1 : (275 / 128 : ℝ) ≤ s) (h2 : s ≤ (279 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (275 / 128 : ℝ) (279 / 128 : ℝ) (481 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_10 {s : ℝ} (h1 : (279 / 128 : ℝ) ≤ s) (h2 : s ≤ (71 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (279 / 128 : ℝ) (71 / 32 : ℝ) (187 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_11 {s : ℝ} (h1 : (71 / 32 : ℝ) ≤ s) (h2 : s ≤ (289 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (71 / 32 : ℝ) (289 / 128 : ℝ) (451 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_12 {s : ℝ} (h1 : (289 / 128 : ℝ) ≤ s) (h2 : s ≤ (295 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (289 / 128 : ℝ) (295 / 128 : ℝ) (871 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_13 {s : ℝ} (h1 : (295 / 128 : ℝ) ≤ s) (h2 : s ≤ (301 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (295 / 128 : ℝ) (301 / 128 : ℝ) (417 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_14 {s : ℝ} (h1 : (301 / 128 : ℝ) ≤ s) (h2 : s ≤ (77 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (301 / 128 : ℝ) (77 / 32 : ℝ) (799 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_15 {s : ℝ} (h1 : (77 / 32 : ℝ) ≤ s) (h2 : s ≤ (315 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (77 / 32 : ℝ) (315 / 128 : ℝ) (759 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_16 {s : ℝ} (h1 : (315 / 128 : ℝ) ≤ s) (h2 : s ≤ (323 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (315 / 128 : ℝ) (323 / 128 : ℝ) (721 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_17 {s : ℝ} (h1 : (323 / 128 : ℝ) ≤ s) (h2 : s ≤ (331 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (323 / 128 : ℝ) (331 / 128 : ℝ) (679 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_18 {s : ℝ} (h1 : (331 / 128 : ℝ) ≤ s) (h2 : s ≤ (85 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (331 / 128 : ℝ) (85 / 32 : ℝ) (639 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_19 {s : ℝ} (h1 : (85 / 32 : ℝ) ≤ s) (h2 : s ≤ (349 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (85 / 32 : ℝ) (349 / 128 : ℝ) (149 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_20 {s : ℝ} (h1 : (349 / 128 : ℝ) ≤ s) (h2 : s ≤ (179 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (349 / 128 : ℝ) (179 / 64 : ℝ) (277 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_21 {s : ℝ} (h1 : (179 / 64 : ℝ) ≤ s) (h2 : s ≤ (367 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (179 / 64 : ℝ) (367 / 128 : ℝ) (257 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_22 {s : ℝ} (h1 : (367 / 128 : ℝ) ≤ s) (h2 : s ≤ (47 / 16 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (367 / 128 : ℝ) (47 / 16 : ℝ) (119 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_23 {s : ℝ} (h1 : (47 / 16 : ℝ) ≤ s) (h2 : s ≤ (385 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (47 / 16 : ℝ) (385 / 128 : ℝ) (439 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_24 {s : ℝ} (h1 : (385 / 128 : ℝ) ≤ s) (h2 : s ≤ (197 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (385 / 128 : ℝ) (197 / 64 : ℝ) (403 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_25 {s : ℝ} (h1 : (197 / 64 : ℝ) ≤ s) (h2 : s ≤ (403 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (197 / 64 : ℝ) (403 / 128 : ℝ) (369 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_26 {s : ℝ} (h1 : (403 / 128 : ℝ) ≤ s) (h2 : s ≤ (413 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (403 / 128 : ℝ) (413 / 128 : ℝ) (67 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_27 {s : ℝ} (h1 : (413 / 128 : ℝ) ≤ s) (h2 : s ≤ (423 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (413 / 128 : ℝ) (423 / 128 : ℝ) (3 / 10 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_28 {s : ℝ} (h1 : (423 / 128 : ℝ) ≤ s) (h2 : s ≤ (433 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (423 / 128 : ℝ) (433 / 128 : ℝ) (53 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_29 {s : ℝ} (h1 : (433 / 128 : ℝ) ≤ s) (h2 : s ≤ (443 / 128 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (433 / 128 : ℝ) (443 / 128 : ℝ) (29 / 125 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_30 {s : ℝ} (h1 : (443 / 128 : ℝ) ≤ s) (h2 : s ≤ (227 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (443 / 128 : ℝ) (227 / 64 : ℝ) (1 / 5 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_31 {s : ℝ} (h1 : (227 / 64 : ℝ) ≤ s) (h2 : s ≤ (233 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (227 / 64 : ℝ) (233 / 64 : ℝ) (33 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_32 {s : ℝ} (h1 : (233 / 64 : ℝ) ≤ s) (h2 : s ≤ (239 / 64 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (233 / 64 : ℝ) (239 / 64 : ℝ) (129 / 1000 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_33 {s : ℝ} (h1 : (239 / 64 : ℝ) ≤ s) (h2 : s ≤ (123 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (239 / 64 : ℝ) (123 / 32 : ℝ) (47 / 500 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_34 {s : ℝ} (h1 : (123 / 32 : ℝ) ≤ s) (h2 : s ≤ (127 / 32 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (123 / 32 : ℝ) (127 / 32 : ℝ) (11 / 200 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

private lemma psi_cell_35 {s : ℝ} (h1 : (127 / 32 : ℝ) ≤ s) (h2 : s ≤ (4 : ℝ)) : psiK s ≤ 4 / 5 * s :=
  psi_cell (127 / 32 : ℝ) (4 : ℝ) (3 / 250 : ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial]) h1 h2

/-- **Mesh bound for `ψ` on `[2,4]`** (I71 Lemma 3 replaced by 36 cells):
`e^{s-3} (1 + 3 log(3/(s-1))) ≤ (4/5) s`, i.e. `ψ(s) ≤ 4/5`. -/
theorem psiK_le {s : ℝ} (h2 : 2 ≤ s) (h4 : s ≤ 4) : psiK s ≤ 4 / 5 * s := by
  rcases le_total s (257 / 128 : ℝ) with h0 | g0
  · exact psi_cell_0 h2 h0
  rcases le_total s (129 / 64 : ℝ) with h1 | g1
  · exact psi_cell_1 g0 h1
  rcases le_total s (259 / 128 : ℝ) with h2 | g2
  · exact psi_cell_2 g1 h2
  rcases le_total s (261 / 128 : ℝ) with h3 | g3
  · exact psi_cell_3 g2 h3
  rcases le_total s (263 / 128 : ℝ) with h4 | g4
  · exact psi_cell_4 g3 h4
  rcases le_total s (265 / 128 : ℝ) with h5 | g5
  · exact psi_cell_5 g4 h5
  rcases le_total s (67 / 32 : ℝ) with h6 | g6
  · exact psi_cell_6 g5 h6
  rcases le_total s (271 / 128 : ℝ) with h7 | g7
  · exact psi_cell_7 g6 h7
  rcases le_total s (275 / 128 : ℝ) with h8 | g8
  · exact psi_cell_8 g7 h8
  rcases le_total s (279 / 128 : ℝ) with h9 | g9
  · exact psi_cell_9 g8 h9
  rcases le_total s (71 / 32 : ℝ) with h10 | g10
  · exact psi_cell_10 g9 h10
  rcases le_total s (289 / 128 : ℝ) with h11 | g11
  · exact psi_cell_11 g10 h11
  rcases le_total s (295 / 128 : ℝ) with h12 | g12
  · exact psi_cell_12 g11 h12
  rcases le_total s (301 / 128 : ℝ) with h13 | g13
  · exact psi_cell_13 g12 h13
  rcases le_total s (77 / 32 : ℝ) with h14 | g14
  · exact psi_cell_14 g13 h14
  rcases le_total s (315 / 128 : ℝ) with h15 | g15
  · exact psi_cell_15 g14 h15
  rcases le_total s (323 / 128 : ℝ) with h16 | g16
  · exact psi_cell_16 g15 h16
  rcases le_total s (331 / 128 : ℝ) with h17 | g17
  · exact psi_cell_17 g16 h17
  rcases le_total s (85 / 32 : ℝ) with h18 | g18
  · exact psi_cell_18 g17 h18
  rcases le_total s (349 / 128 : ℝ) with h19 | g19
  · exact psi_cell_19 g18 h19
  rcases le_total s (179 / 64 : ℝ) with h20 | g20
  · exact psi_cell_20 g19 h20
  rcases le_total s (367 / 128 : ℝ) with h21 | g21
  · exact psi_cell_21 g20 h21
  rcases le_total s (47 / 16 : ℝ) with h22 | g22
  · exact psi_cell_22 g21 h22
  rcases le_total s (385 / 128 : ℝ) with h23 | g23
  · exact psi_cell_23 g22 h23
  rcases le_total s (197 / 64 : ℝ) with h24 | g24
  · exact psi_cell_24 g23 h24
  rcases le_total s (403 / 128 : ℝ) with h25 | g25
  · exact psi_cell_25 g24 h25
  rcases le_total s (413 / 128 : ℝ) with h26 | g26
  · exact psi_cell_26 g25 h26
  rcases le_total s (423 / 128 : ℝ) with h27 | g27
  · exact psi_cell_27 g26 h27
  rcases le_total s (433 / 128 : ℝ) with h28 | g28
  · exact psi_cell_28 g27 h28
  rcases le_total s (443 / 128 : ℝ) with h29 | g29
  · exact psi_cell_29 g28 h29
  rcases le_total s (227 / 64 : ℝ) with h30 | g30
  · exact psi_cell_30 g29 h30
  rcases le_total s (233 / 64 : ℝ) with h31 | g31
  · exact psi_cell_31 g30 h31
  rcases le_total s (239 / 64 : ℝ) with h32 | g32
  · exact psi_cell_32 g31 h32
  rcases le_total s (123 / 32 : ℝ) with h33 | g33
  · exact psi_cell_33 g32 h33
  rcases le_total s (127 / 32 : ℝ) with h34 | g34
  · exact psi_cell_34 g33 h34
  exact psi_cell_35 g34 h4

/-! ## Kernel inequalities (C.1) -/

/-- **(K+)** For `s ≥ 1`: `s⁻¹ ∫_{u > max (s-1) 2} m⁻ ≤ θ₂ m⁺(s)` (equality on `[1,3]`). -/
theorem kernel_plus {s : ℝ} (hs : 1 ≤ s) :
    s⁻¹ * ∫ u in Ioi (max (s - 1) 2), mMinus u ≤ theta2 * mPlus s := by
  rw [integral_mMinus_Ioi, theta2]
  rcases le_total s 3 with h | h
  · rw [max_eq_right (by linarith), mPlus_of_le h]
    have he : exp 1 * exp (-3) = exp (-2) := by rw [← exp_add]; norm_num
    rw [← he]
    apply le_of_eq
    field_simp
  · rw [max_eq_left (by linarith), mPlus_of_ge h,
      show exp (-(s - 1)) = exp 1 * exp (-s) by rw [← exp_add]; congr 1; ring]
    have hinv : s⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) h
    calc s⁻¹ * (exp 1 * exp (-s)) ≤ 3⁻¹ * (exp 1 * exp (-s)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = exp 1 / 3 * exp (-s) := by ring

/-- **(K−)** For `s ≥ 2`: `s⁻¹ ∫_{u > s-1} m⁺ ≤ θ₁ m⁻(s)`, `θ₁ = 4/5`. -/
theorem kernel_minus {s : ℝ} (hs : 2 ≤ s) :
    s⁻¹ * ∫ u in Ioi (s - 1), mPlus u ≤ theta1 * mMinus s := by
  rw [theta1, mMinus]
  have hs0 : 0 < s := by linarith
  rcases le_total 4 s with h | h
  · rw [integral_mPlus_Ioi_of_ge (by linarith),
      show exp (-(s - 1)) = exp 1 * exp (-s) by rw [← exp_add]; congr 1; ring]
    have hinv : s⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) h
    have he := Real.exp_one_lt_d9
    calc s⁻¹ * (exp 1 * exp (-s)) ≤ 4⁻¹ * (exp 1 * exp (-s)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (exp 1 / 4) * exp (-s) := by ring
      _ ≤ 4 / 5 * exp (-s) :=
          mul_le_mul_of_nonneg_right (by norm_num at he ⊢; linarith) (exp_pos _).le
  · rw [integral_mPlus_Ioi_of_le (by linarith) (by linarith)]
    have hpsi := psiK_le hs h
    unfold psiK at hpsi
    have he3 : exp (-3) = exp (-s) * exp (s - 3) := by rw [← exp_add]; congr 1; ring
    calc s⁻¹ * (exp (-3) * (1 + 3 * log (3 / (s - 1))))
        = (s⁻¹ * exp (-s)) * (exp (s - 3) * (1 + 3 * log (3 / (s - 1)))) := by rw [he3]; ring
      _ ≤ (s⁻¹ * exp (-s)) * (4 / 5 * s) := mul_le_mul_of_nonneg_left hpsi (by positivity)
      _ = 4 / 5 * exp (-s) := by field_simp

/-- The rate is `< 1`: `θ₁ θ₂ = 4e/15 < 0.725`. -/
theorem theta1_mul_theta2_lt_one : theta1 * theta2 < 1 := rateA_lt_one

/-! ## Properties of `β±_k` (B.1) -/

section Props

private lemma betaM_succ_props (k : ℕ) (hc : ∀ x : ℝ, 0 < x → ContinuousAt (betaP k) x)
    (hz : ∀ x : ℝ, 2 * (k : ℝ) + 3 ≤ x → betaP k x = 0) :
    (∀ x : ℝ, 1 < x → ContinuousAt (betaM (k + 1)) x) ∧
      (∀ x : ℝ, 2 * ((k + 1 : ℕ) : ℝ) + 2 ≤ x → betaM (k + 1) x = 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hF := continuousAt_setIntegral_Ioi hc hz (show (0 : ℝ) < x - 1 by linarith)
    have hG : ContinuousAt (fun s : ℝ => ∫ u in Ioi (s - 1), betaP k u) x :=
      hF.comp (f := fun s : ℝ => s - 1) (continuousAt_id.sub continuousAt_const)
    exact (continuousAt_inv₀ (by linarith : x ≠ 0)).mul hG
  · rw [betaM_succ, setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
    intro u hu
    push_cast at hx
    exact hz u (by linarith [mem_Ioi.mp hu])

private lemma betaP_succ_props (k : ℕ) (hc : ∀ x : ℝ, 1 < x → ContinuousAt (betaM (k + 1)) x)
    (hz : ∀ x : ℝ, 2 * ((k + 1 : ℕ) : ℝ) + 2 ≤ x → betaM (k + 1) x = 0) :
    (∀ x : ℝ, 0 < x → ContinuousAt (betaP (k + 1)) x) ∧
      (∀ x : ℝ, 2 * ((k + 1 : ℕ) : ℝ) + 3 ≤ x → betaP (k + 1) x = 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hF := continuousAt_setIntegral_Ioi hc hz
      (show (1 : ℝ) < max (x - 1) 2 from lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    have hG : ContinuousAt (fun s : ℝ => ∫ u in Ioi (max (s - 1) 2), betaM (k + 1) u) x :=
      hF.comp (f := fun s : ℝ => max (s - 1) 2)
        ((continuous_id.sub continuous_const).max continuous_const).continuousAt
    exact (continuousAt_inv₀ hx.ne').mul hG
  · rw [betaP_succ, setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
    intro u hu
    have hu' : max (x - 1) 2 < u := hu
    exact hz u (by linarith [le_max_left (x - 1) 2])

private lemma betaP_props (k : ℕ) :
    (∀ x : ℝ, 0 < x → ContinuousAt (betaP k) x) ∧
      (∀ x : ℝ, 2 * (k : ℝ) + 3 ≤ x → betaP k x = 0) := by
  induction k with
  | zero =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact ((continuousAt_const.div continuousAt_id hx.ne').sub continuousAt_const).max
        continuousAt_const
    · rw [betaP_zero]
      have hx3 : (3 : ℝ) ≤ x := by simpa using hx
      have : 3 / x ≤ 1 := by rw [div_le_one (by linarith)]; exact hx3
      exact max_eq_right (by linarith)
  | succ k ih =>
    have hM := betaM_succ_props k ih.1 ih.2
    exact betaP_succ_props k hM.1 hM.2

end Props

/-- `β⁺_k` is continuous at every `x > 0`. -/
theorem continuousAt_betaP (k : ℕ) {x : ℝ} (hx : 0 < x) : ContinuousAt (betaP k) x :=
  (betaP_props k).1 x hx

/-- `β⁺_k = 0` on `[2k+3, ∞)`. -/
theorem betaP_eq_zero (k : ℕ) {x : ℝ} (hx : 2 * (k : ℝ) + 3 ≤ x) : betaP k x = 0 :=
  (betaP_props k).2 x hx

/-- `β⁻_k` is continuous at every `x > 1`. -/
theorem continuousAt_betaM (k : ℕ) {x : ℝ} (hx : 1 < x) : ContinuousAt (betaM k) x := by
  cases k with
  | zero => exact continuousAt_const
  | succ k => exact (betaM_succ_props k (betaP_props k).1 (betaP_props k).2).1 x hx

/-- `β⁻_k = 0` on `[2k+2, ∞)`. -/
theorem betaM_eq_zero (k : ℕ) {x : ℝ} (hx : 2 * (k : ℝ) + 2 ≤ x) : betaM k x = 0 := by
  cases k with
  | zero => rfl
  | succ k => exact (betaM_succ_props k (betaP_props k).1 (betaP_props k).2).2 x hx

theorem continuousOn_betaP (k : ℕ) : ContinuousOn (betaP k) (Ioi 0) :=
  fun _ hx => (continuousAt_betaP k hx).continuousWithinAt

theorem continuousOn_betaM (k : ℕ) : ContinuousOn (betaM k) (Ioi 1) :=
  fun _ hx => (continuousAt_betaM k hx).continuousWithinAt

theorem integrableOn_betaP (k : ℕ) {c : ℝ} (hc : 0 < c) : IntegrableOn (betaP k) (Ioi c) :=
  integrableOn_Ioi_of_cont (fun _ hx => continuousAt_betaP k hx) (fun _ hx => betaP_eq_zero k hx) hc

theorem integrableOn_betaM (k : ℕ) {c : ℝ} (hc : 1 < c) : IntegrableOn (betaM k) (Ioi c) :=
  integrableOn_Ioi_of_cont (fun _ hx => continuousAt_betaM k hx) (fun _ hx => betaM_eq_zero k hx) hc

/-- Measurability on the meaningful ranges. -/
theorem aestronglyMeasurable_betaP (k : ℕ) {c : ℝ} (hc : 0 < c) :
    AEStronglyMeasurable (betaP k) (volume.restrict (Ioi c)) :=
  (integrableOn_betaP k hc).aestronglyMeasurable

theorem aestronglyMeasurable_betaM (k : ℕ) {c : ℝ} (hc : 1 < c) :
    AEStronglyMeasurable (betaM k) (volume.restrict (Ioi c)) :=
  (integrableOn_betaM k hc).aestronglyMeasurable

/-- `β⁺_k ≥ 0` on `s ≥ 0`. -/
theorem betaP_nonneg (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ betaP k s := by
  induction k generalizing s with
  | zero => exact le_max_right _ _
  | succ k ih =>
    rw [betaP_succ]
    refine mul_nonneg (inv_nonneg.mpr hs) (setIntegral_nonneg measurableSet_Ioi fun u hu => ?_)
    have hu' : max (s - 1) 2 < u := hu
    have hu2 : 2 < u := lt_of_le_of_lt (le_max_right _ _) hu'
    rw [betaM_succ]
    exact mul_nonneg (inv_nonneg.mpr (by linarith))
      (setIntegral_nonneg measurableSet_Ioi fun v hv => ih (by linarith [mem_Ioi.mp hv]))

/-- `β⁻_k ≥ 0` on `s ≥ 1`. -/
theorem betaM_nonneg (k : ℕ) {s : ℝ} (hs : 1 ≤ s) : 0 ≤ betaM k s := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    rw [betaM_succ]
    exact mul_nonneg (inv_nonneg.mpr (by linarith))
      (setIntegral_nonneg measurableSet_Ioi fun v hv => betaP_nonneg k (by linarith [mem_Ioi.mp hv]))

/-- `β⁺_k(s) = (3/s) β⁺_k(3)` for `s ≤ 3`, `k ≥ 1`. -/
theorem betaP_succ_of_le_three (k : ℕ) {s : ℝ} (hs : s ≤ 3) :
    betaP (k + 1) s = 3 / s * betaP (k + 1) 3 := by
  rw [betaP_succ, betaP_succ, max_eq_right (by linarith : s - 1 ≤ 2),
    max_eq_right (by norm_num : (3 : ℝ) - 1 ≤ 2)]
  ring

/-- `s β⁺_k(s) = ∫_{u > 2} β⁻_k` for `0 < s ≤ 3`, `k ≥ 1`. -/
theorem mul_betaP_succ_of_le_three (k : ℕ) {s : ℝ} (hs0 : s ≠ 0) (hs : s ≤ 3) :
    s * betaP (k + 1) s = ∫ u in Ioi 2, betaM (k + 1) u := by
  rw [betaP_succ, max_eq_right (by linarith : s - 1 ≤ 2), ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]

/-- Interval-integral form of `β⁻_{k+1}` for `s > 1`, any cut `N ≥ 2k+3`. -/
theorem betaM_succ_eq_intervalIntegral (k : ℕ) {s N : ℝ} (hs : 1 < s) (hN : 2 * (k : ℝ) + 3 ≤ N) :
    betaM (k + 1) s = s⁻¹ * ∫ u in (s - 1)..N, betaP k u := by
  rw [betaM_succ, setIntegral_Ioi_eq_intervalIntegral (c := 0)
    (fun _ hx => continuousAt_betaP k hx) (fun _ hx => betaP_eq_zero k hx) (by linarith) hN]

/-- Interval-integral form of `β⁺_{k+1}` for all `s`, any cut `N ≥ 2k+4`. -/
theorem betaP_succ_eq_intervalIntegral (k : ℕ) (s : ℝ) {N : ℝ}
    (hN : 2 * ((k + 1 : ℕ) : ℝ) + 2 ≤ N) :
    betaP (k + 1) s = s⁻¹ * ∫ u in (max (s - 1) 2)..N, betaM (k + 1) u := by
  rw [betaP_succ, setIntegral_Ioi_eq_intervalIntegral (c := 1)
    (fun _ hx => continuousAt_betaM (k + 1) hx) (fun _ hx => betaM_eq_zero (k + 1) hx)
    (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hN]

/-! ## Continuous tail bounds (C.5) -/

/-- **C.5 (+)**: `β⁺_k(s) ≤ c₀ A^k m⁺(s)` for `s ≥ 1`. -/
theorem betaP_le (k : ℕ) {s : ℝ} (hs : 1 ≤ s) : betaP k s ≤ c0 * rateA ^ k * mPlus s := by
  induction k generalizing s with
  | zero =>
    rw [pow_zero, mul_one, betaP_zero]
    have hs0 : 0 < s := by linarith
    rcases le_total s 3 with h | h
    · rw [mPlus_of_le h, show c0 * (3 * exp (-3) / s) = c0 * (3 * exp (-3)) / s by ring,
        c0_mul_mPlus_one]
      refine max_le ?_ (by positivity)
      have : 1 / s ≤ 1 := by rw [div_le_one hs0]; exact hs
      have : 3 / s - 1 - 2 / s = 1 / s - 1 := by ring
      linarith
    · have : 3 / s ≤ 1 := by rw [div_le_one hs0]; exact h
      rw [max_eq_right (by linarith)]
      exact (mul_pos c0_pos (mPlus_pos hs0)).le
  | succ k ih =>
    -- first `β⁻_{k+1}(u) ≤ c₀ θ₁ A^k m⁻(u)` for `u ≥ 2`
    have hM : ∀ u : ℝ, 2 ≤ u → betaM (k + 1) u ≤ c0 * theta1 * rateA ^ k * mMinus u := by
      intro u hu
      rw [betaM_succ]
      have hc : 0 ≤ c0 * rateA ^ k := mul_nonneg c0_pos.le (pow_nonneg rateA_nonneg k)
      have hint : ∫ v in Ioi (u - 1), betaP k v ≤ ∫ v in Ioi (u - 1), c0 * rateA ^ k * mPlus v :=
        setIntegral_mono_on (integrableOn_betaP k (by linarith))
          ((integrableOn_mPlus (by linarith)).const_mul _) measurableSet_Ioi
          (fun v hv => ih (by linarith [mem_Ioi.mp hv]))
      rw [integral_const_mul] at hint
      calc u⁻¹ * ∫ v in Ioi (u - 1), betaP k v
          ≤ u⁻¹ * (c0 * rateA ^ k * ∫ v in Ioi (u - 1), mPlus v) :=
            mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (by linarith))
        _ = c0 * rateA ^ k * (u⁻¹ * ∫ v in Ioi (u - 1), mPlus v) := by ring
        _ ≤ c0 * rateA ^ k * (theta1 * mMinus u) := mul_le_mul_of_nonneg_left (kernel_minus hu) hc
        _ = c0 * theta1 * rateA ^ k * mMinus u := by ring
    rw [betaP_succ]
    have hc : 0 ≤ c0 * theta1 * rateA ^ k :=
      mul_nonneg (mul_nonneg c0_pos.le theta1_pos.le) (pow_nonneg rateA_nonneg k)
    have hint : ∫ u in Ioi (max (s - 1) 2), betaM (k + 1) u
        ≤ ∫ u in Ioi (max (s - 1) 2), c0 * theta1 * rateA ^ k * mMinus u :=
      setIntegral_mono_on (integrableOn_betaM (k + 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
        ((integrableOn_mMinus _).const_mul _) measurableSet_Ioi
        (fun u hu => hM u (le_trans (le_max_right _ _) (le_of_lt (mem_Ioi.mp hu))))
    rw [integral_const_mul] at hint
    calc s⁻¹ * ∫ u in Ioi (max (s - 1) 2), betaM (k + 1) u
        ≤ s⁻¹ * (c0 * theta1 * rateA ^ k * ∫ u in Ioi (max (s - 1) 2), mMinus u) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (by linarith))
      _ = c0 * theta1 * rateA ^ k * (s⁻¹ * ∫ u in Ioi (max (s - 1) 2), mMinus u) := by ring
      _ ≤ c0 * theta1 * rateA ^ k * (theta2 * mPlus s) := mul_le_mul_of_nonneg_left (kernel_plus hs) hc
      _ = c0 * rateA ^ (k + 1) * mPlus s := by rw [pow_succ, rateA]; ring

/-- **C.5 (−)**: `β⁻_{k+1}(s) ≤ c₀ θ₁ A^k m⁻(s)` for `s ≥ 2`. -/
theorem betaM_succ_le (k : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    betaM (k + 1) s ≤ c0 * theta1 * rateA ^ k * mMinus s := by
  rw [betaM_succ]
  have hc : 0 ≤ c0 * rateA ^ k := mul_nonneg c0_pos.le (pow_nonneg rateA_nonneg k)
  have hint : ∫ v in Ioi (s - 1), betaP k v ≤ ∫ v in Ioi (s - 1), c0 * rateA ^ k * mPlus v :=
    setIntegral_mono_on (integrableOn_betaP k (by linarith))
      ((integrableOn_mPlus (by linarith)).const_mul _) measurableSet_Ioi
      (fun v hv => betaP_le k (by linarith [mem_Ioi.mp hv]))
  rw [integral_const_mul] at hint
  calc s⁻¹ * ∫ v in Ioi (s - 1), betaP k v
      ≤ s⁻¹ * (c0 * rateA ^ k * ∫ v in Ioi (s - 1), mPlus v) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (by linarith))
    _ = c0 * rateA ^ k * (s⁻¹ * ∫ v in Ioi (s - 1), mPlus v) := by ring
    _ ≤ c0 * rateA ^ k * (theta1 * mMinus s) := mul_le_mul_of_nonneg_left (kernel_minus hs) hc
    _ = c0 * theta1 * rateA ^ k * mMinus s := by ring

/-- Uniform form: `0 ≤ β⁺_k(s) ≤ 2 A^k` for `s ≥ 1`. -/
theorem betaP_le_two (k : ℕ) {s : ℝ} (hs : 1 ≤ s) : betaP k s ≤ 2 * rateA ^ k := by
  have hc : 0 ≤ c0 * rateA ^ k := mul_nonneg c0_pos.le (pow_nonneg rateA_nonneg k)
  calc betaP k s ≤ c0 * rateA ^ k * mPlus s := betaP_le k hs
    _ ≤ c0 * rateA ^ k * (3 * exp (-3)) := mul_le_mul_of_nonneg_left (mPlus_le_of_one_le hs) hc
    _ = 2 * rateA ^ k := by rw [← c0_mul_mPlus_one]; ring

/-- Uniform form: `0 ≤ β⁻_k(s) ≤ 2 A^k` for `s ≥ 2` (all `k`, `β⁻_0 = 0`). -/
theorem betaM_le_two (k : ℕ) {s : ℝ} (hs : 2 ≤ s) : betaM k s ≤ 2 * rateA ^ k := by
  cases k with
  | zero => rw [betaM_zero]; norm_num
  | succ k =>
    have hc : 0 ≤ c0 * theta1 * rateA ^ k :=
      mul_nonneg (mul_nonneg c0_pos.le theta1_pos.le) (pow_nonneg rateA_nonneg k)
    calc betaM (k + 1) s ≤ c0 * theta1 * rateA ^ k * mMinus s := betaM_succ_le k hs
      _ ≤ c0 * theta1 * rateA ^ k * exp (-2) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hc
      _ = (c0 * theta1 * exp (-2)) * rateA ^ k := by ring
      _ = 2 * rateA ^ (k + 1) := by rw [c0_theta1_exp, pow_succ]; ring

theorem norm_betaP_le (k : ℕ) {s : ℝ} (hs : 1 ≤ s) : ‖betaP k s‖ ≤ 2 * rateA ^ k := by
  rw [Real.norm_of_nonneg (betaP_nonneg k (by linarith))]; exact betaP_le_two k hs

theorem norm_betaM_le (k : ℕ) {s : ℝ} (hs : 2 ≤ s) : ‖betaM k s‖ ≤ 2 * rateA ^ k := by
  rw [Real.norm_of_nonneg (betaM_nonneg k (by linarith))]; exact betaM_le_two k hs

theorem summable_two_mul_rateA_pow : Summable (fun k : ℕ => 2 * rateA ^ k) :=
  (summable_geometric_of_lt_one rateA_nonneg rateA_lt_one).mul_left 2

/-! ## Summability and geometric tails -/

/-- Generic geometric tail: if `0 ≤ f k ≤ C A^k` then `∑' k, f (k + K) ≤ C A^K / (1 - A)`. -/
theorem tsum_tail_le_of_le_geom {f : ℕ → ℝ} {C : ℝ} (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * rateA ^ k) (K : ℕ) :
    ∑' k, f (k + K) ≤ C * rateA ^ K / (1 - rateA) := by
  have hg : Summable (fun k : ℕ => C * rateA ^ K * rateA ^ k) :=
    (summable_geometric_of_lt_one rateA_nonneg rateA_lt_one).mul_left _
  have hle : ∀ k, f (k + K) ≤ C * rateA ^ K * rateA ^ k := fun k =>
    (hf (k + K)).trans_eq (by rw [pow_add]; ring)
  calc ∑' k, f (k + K) ≤ ∑' k, C * rateA ^ K * rateA ^ k :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun k => hf0 _) hle hg) hg
    _ = C * rateA ^ K * (1 - rateA)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one rateA_nonneg rateA_lt_one]
    _ = C * rateA ^ K / (1 - rateA) := by rw [div_eq_mul_inv]

theorem summable_of_le_geom {f : ℕ → ℝ} {C : ℝ} (hf0 : ∀ k, 0 ≤ f k)
    (hf : ∀ k, f k ≤ C * rateA ^ k) : Summable f :=
  Summable.of_nonneg_of_le hf0 hf ((summable_geometric_of_lt_one rateA_nonneg rateA_lt_one).mul_left _)

theorem summable_betaP {s : ℝ} (hs : 1 ≤ s) : Summable (fun k => betaP k s) :=
  summable_of_le_geom (fun k => betaP_nonneg k (by linarith)) (fun k => betaP_le_two k hs)

theorem summable_betaM {s : ℝ} (hs : 2 ≤ s) : Summable (fun k => betaM k s) :=
  summable_of_le_geom (fun k => betaM_nonneg k (by linarith)) (fun k => betaM_le_two k hs)

/-- Tail of `G⁺`: `∑_{k ≥ K} β⁺_k(s) ≤ c₀ A^K m⁺(s)/(1-A)` for `s ≥ 1`. -/
theorem tsum_betaP_tail_le (K : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑' k, betaP (k + K) s ≤ c0 * mPlus s * rateA ^ K / (1 - rateA) :=
  tsum_tail_le_of_le_geom (f := fun k => betaP k s) (fun k => betaP_nonneg k (by linarith))
    (fun k => (betaP_le k hs).trans_eq (by ring)) K

/-- Tail of `G⁻`: `∑_{k ≥ K} β⁻_{k+1}(s) ≤ c₀ θ₁ A^K m⁻(s)/(1-A)` for `s ≥ 2`. -/
theorem tsum_betaM_tail_le (K : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    ∑' k, betaM (k + K + 1) s ≤ c0 * theta1 * mMinus s * rateA ^ K / (1 - rateA) :=
  tsum_tail_le_of_le_geom (f := fun k => betaM (k + 1) s) (fun k => betaM_nonneg _ (by linarith))
    (fun k => (betaM_succ_le k hs).trans_eq (by ring)) K

/-- Uniform tails: `∑_{k ≥ K} β⁺_k(s) ≤ 2 A^K/(1-A)` (`s ≥ 1`). -/
theorem tsum_betaP_tail_le_two (K : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ∑' k, betaP (k + K) s ≤ 2 * rateA ^ K / (1 - rateA) :=
  tsum_tail_le_of_le_geom (f := fun k => betaP k s) (fun k => betaP_nonneg k (by linarith))
    (fun k => betaP_le_two k hs) K

/-- Uniform tails: `∑_{k ≥ K} β⁻_k(s) ≤ 2 A^K/(1-A)` (`s ≥ 2`). -/
theorem tsum_betaM_tail_le_two (K : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    ∑' k, betaM (k + K) s ≤ 2 * rateA ^ K / (1 - rateA) :=
  tsum_tail_le_of_le_geom (f := fun k => betaM k s) (fun k => betaM_nonneg k (by linarith))
    (fun k => betaM_le_two k hs) K

/-- `G⁺(s) = ∑' β⁺_k(s) ≤ c₀ m⁺(s)/(1-A)` for `s ≥ 1`. -/
theorem tsum_betaP_le {s : ℝ} (hs : 1 ≤ s) :
    ∑' k, betaP k s ≤ c0 * mPlus s / (1 - rateA) := by
  simpa using tsum_betaP_tail_le 0 hs

/-- `G⁻(s) = ∑' β⁻_k(s) ≤ c₀ θ₁ m⁻(s)/(1-A)` for `s ≥ 2`. -/
theorem tsum_betaM_le {s : ℝ} (hs : 2 ≤ s) :
    ∑' k, betaM k s ≤ c0 * theta1 * mMinus s / (1 - rateA) := by
  rw [(summable_betaM hs).tsum_eq_zero_add, betaM_zero, zero_add]
  simpa using tsum_betaM_tail_le 0 hs

/-! ## Layer-cake form of `m⁺` (input for C.2)

`m⁺(t) = ∫_{u>t} μ⁺(u) du` and `∫_{u>a} μ⁺(u) (u - a) du = ∫_{u>a} m⁺(u) du`, with `μ⁺ = -(m⁺)' ≥ 0`
(jump at `u = 3`, harmless). For `m⁻ = e^{-u}` the density is `m⁻` itself (`integral_mMinus_Ioi`). -/

/-- `μ⁺ = -(m⁺)'`: `3 e^{-3}/u²` on `u ≤ 3`, `e^{-u}` on `u > 3`. -/
noncomputable def muPlus (u : ℝ) : ℝ := if u ≤ 3 then 3 * exp (-3) / u ^ 2 else exp (-u)

lemma muPlus_of_le {u : ℝ} (hu : u ≤ 3) : muPlus u = 3 * exp (-3) / u ^ 2 := by
  unfold muPlus; simp [hu]

lemma muPlus_of_gt {u : ℝ} (hu : 3 < u) : muPlus u = exp (-u) := by
  unfold muPlus; simp [not_le.mpr hu]

lemma muPlus_nonneg (u : ℝ) : 0 ≤ muPlus u := by
  unfold muPlus; split_ifs <;> positivity

/-- `∫_{u>b} e^{-u} (u - a) du = (b - a + 1) e^{-b}` (with integrability) for `a ≤ b`. -/
private lemma expmoment (a b : ℝ) (hab : a ≤ b) :
    IntegrableOn (fun u => exp (-u) * (u - a)) (Ioi b) ∧
      ∫ u in Ioi b, exp (-u) * (u - a) = (b - a + 1) * exp (-b) := by
  set G : ℝ → ℝ := fun u => -((u - a + 1) * exp (-u)) with hG
  have hderiv : ∀ x ∈ Ici b, HasDerivAt G (exp (-x) * (x - a)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => u - a + 1) 1 x := ((hasDerivAt_id x).sub_const a).add_const 1
    have h2 : HasDerivAt (fun u : ℝ => exp (-u)) (-exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    have := (h1.mul h2).neg
    convert this using 1; ring
  have hpos : ∀ x ∈ Ioi b, 0 ≤ exp (-x) * (x - a) := fun x hx =>
    mul_nonneg (exp_pos _).le (by linarith [mem_Ioi.mp hx])
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
    have := (h1.add (h2.const_mul (1 - a))).neg
    simp only [pow_one, mul_zero, add_zero, neg_zero] at this
    refine this.congr (fun u => ?_)
    simp only [hG]; ring
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp only [hG]; ring

private lemma muPlus_Ioi_three : EqOn muPlus (fun u => exp (-u)) (Ioi 3) :=
  fun _ hu => muPlus_of_gt hu

private lemma muPlus_Ioc_three {t : ℝ} : EqOn muPlus (fun u => 3 * exp (-3) / u ^ 2) (Ioc t 3) :=
  fun _ hu => muPlus_of_le hu.2

private lemma contOn_inv_sq {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ) (hg : Continuous g) :
    ContinuousOn (fun u => 3 * exp (-3) / u ^ 2 * g u) (Icc t 3) :=
  (continuousOn_const.div (continuousOn_pow 2)
    (fun x (hx : x ∈ Icc t 3) => pow_ne_zero 2 (ht.trans_le hx.1).ne')).mul hg.continuousOn

theorem integrableOn_muPlus {t : ℝ} (ht : 0 < t) : IntegrableOn muPlus (Ioi t) := by
  rcases le_or_gt 3 t with h | h
  · exact ((integrableOn_exp_neg_Ioi 3).congr_fun muPlus_Ioi_three.symm measurableSet_Ioi).mono_set
      (Ioi_subset_Ioi h)
  · rw [← Ioc_union_Ioi_eq_Ioi h.le]
    refine IntegrableOn.union ?_
      ((integrableOn_exp_neg_Ioi 3).congr_fun muPlus_Ioi_three.symm measurableSet_Ioi)
    have := ((contOn_inv_sq ht (fun _ => 1) continuous_const).integrableOn_Icc (μ := volume)).mono_set
      (Ioc_subset_Icc_self (a := t) (b := 3))
    refine this.congr_fun (fun u hu => ?_) measurableSet_Ioc
    simp only [mul_one]; exact (muPlus_of_le hu.2).symm

theorem integrableOn_muPlus_mul_sub {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => muPlus u * (u - a)) (Ioi a) := by
  rcases le_or_gt 3 a with h | h
  · refine (expmoment a a le_rfl).1.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [muPlus_of_gt (h.trans_lt hu)]
  · rw [← Ioc_union_Ioi_eq_Ioi h.le]
    refine IntegrableOn.union ?_
      ((expmoment a 3 h.le).1.congr_fun (fun u hu => by simp only [muPlus_of_gt hu]) measurableSet_Ioi)
    have := ((contOn_inv_sq ha (fun u => u - a) (continuous_id.sub continuous_const)).integrableOn_Icc (μ := volume)).mono_set
      (Ioc_subset_Icc_self (a := a) (b := 3))
    exact this.congr_fun (fun u hu => by simp only [muPlus_of_le hu.2]) measurableSet_Ioc

/-- Layer-cake: `m⁺(t) = ∫_{u>t} μ⁺(u) du` for `t > 0`. -/
theorem integral_muPlus_Ioi {t : ℝ} (ht : 0 < t) : ∫ u in Ioi t, muPlus u = mPlus t := by
  rcases le_or_gt 3 t with h | h
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun u (hu : u ∈ Ioi t) => muPlus_of_gt (h.trans_lt hu)),
      integral_exp_neg_Ioi, mPlus_of_ge h]
  · have hi := integrableOn_muPlus ht
    rw [← Ioc_union_Ioi_eq_Ioi h.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi h.le)),
      setIntegral_congr_fun measurableSet_Ioi muPlus_Ioi_three, integral_exp_neg_Ioi,
      setIntegral_congr_fun measurableSet_Ioc muPlus_Ioc_three, ← intervalIntegral.integral_of_le h.le]
    have hd : ∀ x ∈ uIcc t 3, HasDerivAt (fun u => -(3 * exp (-3)) * u⁻¹) (3 * exp (-3) / x ^ 2) x := by
      intro x hx
      rw [uIcc_of_le h.le] at hx
      have hx0 : x ≠ 0 := (ht.trans_le hx.1).ne'
      convert (hasDerivAt_inv hx0).const_mul (-(3 * exp (-3))) using 1
      field_simp
    have hint : IntervalIntegrable (fun u => 3 * exp (-3) / u ^ 2) volume t 3 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h.le]
      simpa using contOn_inv_sq ht (fun _ => 1) continuous_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, mPlus_of_le h.le]
    field_simp
    ring

/-- Moment identity: `∫_{u>a} μ⁺(u) (u - a) du = ∫_{u>a} m⁺(u) du` for `a > 0`. -/
theorem integral_muPlus_mul_sub {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi a, muPlus u * (u - a) = ∫ u in Ioi a, mPlus u := by
  rcases le_or_gt 3 a with h | h
  · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun u => exp (-u) * (u - a))
      (fun u (hu : u ∈ Ioi a) => by simp only [muPlus_of_gt (h.trans_lt hu)]),
      (expmoment a a le_rfl).2, integral_mPlus_Ioi_of_ge h]
    ring
  · have hi := integrableOn_muPlus_mul_sub ha
    rw [← Ioc_union_Ioi_eq_Ioi h.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi h.le)),
      setIntegral_congr_fun measurableSet_Ioi (g := fun u => exp (-u) * (u - a))
        (fun u (hu : u ∈ Ioi 3) => by simp only [muPlus_of_gt hu]),
      (expmoment a 3 h.le).2,
      setIntegral_congr_fun measurableSet_Ioc (g := fun u => 3 * exp (-3) / u ^ 2 * (u - a))
        (fun u (hu : u ∈ Ioc a 3) => by simp only [muPlus_of_le hu.2]),
      ← intervalIntegral.integral_of_le h.le, Ioc_union_Ioi_eq_Ioi h.le,
      integral_mPlus_Ioi_of_le ha h.le]
    have hd : ∀ x ∈ uIcc a 3, HasDerivAt (fun u => 3 * exp (-3) * (log u + a * u⁻¹))
        (3 * exp (-3) / x ^ 2 * (x - a)) x := by
      intro x hx
      rw [uIcc_of_le h.le] at hx
      have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
      convert ((Real.hasDerivAt_log hx0).add ((hasDerivAt_inv hx0).const_mul a)).const_mul
        (3 * exp (-3)) using 1
      field_simp
      ring
    have hint : IntervalIntegrable (fun u => 3 * exp (-3) / u ^ 2 * (u - a)) volume a 3 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le h.le]
      exact contOn_inv_sq ha (fun u => u - a) (continuous_id.sub continuous_const)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint,
      Real.log_div (by norm_num) ha.ne']
    field_simp
    ring

end Palprimes.E1
