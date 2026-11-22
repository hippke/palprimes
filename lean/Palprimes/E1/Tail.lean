import Palprimes.E1.Boundary
import Palprimes.E1.Mertens
import Palprimes.E1.Cont

set_option linter.style.longLine false

/-! # E1, phase E6: the uniform tail (blueprint C.2, C.3, C.4)

* `layer_cake_sum`, `prime_layer_bound`: the layer-cake form of the discrete kernel step (blueprint §4.2,
  "Lean formulation without indexing primes"): `m(s_p) = ∫_{u>s_p} μ`, swap the finite sum and the integral,
  bound `Σ_{s_p ≤ u} g(p)V(p) = V(D^{1/(1+u)}) − V(c)` (A.7) by one-sided Mertens.
* `tail_setup`: the Mertens threshold `x₀` (ratio constant `ρ ≤ 1 + min(η,1)/40`), `W₀ = x₀²`, `D₀`.
* **C.2** `kernel_step`: for `D ≥ D₀`, `W₀ ≤ w ≤ D`:
  (−) `w² ≤ D → Σ_{p<w} g(p)V(p) m⁺(s_p) ≤ (1+η)θ₁ V(w) m⁻(s)`,
  (+) `Σ_{p<w, p³≤D} g(p)V(p) m⁻(s_p) ≤ (1+η)θ₂ V(w) m⁺(s)` (one-prime correction at `p = D^{1/3}` included).
* **C.3** `tail_geom`: `B⁺_k ≤ C A_η^k V(w) m⁺(s)` and `B⁻_{k+1} ≤ C (1+η)θ₁ A_η^k V(w) m⁻(s)`,
  `A_η = (1+η)² rateA`, for all `k`, all levels `D` and `2 ≤ w ≤ D` (resp. `w² ≤ D`); small levels in `C`.
* **C.4** `tail_small`: `Σ_{K' ≤ k < N} B^±_k(D, w) ≤ ε V(w)` for all `K' ≥ K`, `N`, `D`, `2 ≤ w ≤ D`
  (resp. `w² ≤ D`); assembly forms `Splus_trunc`, `Sminus_trunc`, and range lemmas for `w = z^{1/s}`.

Conventions: `s = log D / log w`, `s_p = log (D/p) / log p`; lower-sum hypothesis `w² ≤ D` (`w ≤ D^{1/2}`). -/


open MeasureTheory Set Finset Real Filter

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

/-! ## Finite layer cake -/

/-- **Finite layer cake.** If `m(t) = ∫_{u>t} μ` (`μ ≥ 0`) at the points `t_p > a`, and
`μ(u) · Σ_{p : t_p < u} c_p ≤ F(u)` for `u > a`, then `Σ_p c_p m(t_p) ≤ ∫_{u>a} F`. -/
theorem layer_cake_sum {ι : Type*} (P : Finset ι) (c t : ι → ℝ) (m μ F : ℝ → ℝ) (a : ℝ)
    (ht : ∀ p ∈ P, a < t p) (hμi : IntegrableOn μ (Ioi a))
    (hm : ∀ p ∈ P, m (t p) = ∫ u in Ioi (t p), μ u) (hF : IntegrableOn F (Ioi a))
    (hle : ∀ u, a < u → μ u * ∑ p ∈ P.filter (fun p => t p < u), c p ≤ F u) :
    ∑ p ∈ P, c p * m (t p) ≤ ∫ u in Ioi a, F u := by
  have e1 : ∀ p ∈ P, c p * m (t p) = ∫ u in Ioi a, c p * (Ioi (t p)).indicator μ u := by
    intro p hp
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_right (ht p hp).le, hm p hp]
  rw [sum_congr rfl e1, ← integral_finsetSum]
  · refine setIntegral_mono_on ?_ hF measurableSet_Ioi (fun u hu => ?_)
    · exact integrable_finsetSum _ (fun p _ => (hμi.indicator measurableSet_Ioi).const_mul _)
    · refine le_trans (le_of_eq ?_) (hle u hu)
      rw [sum_filter, mul_sum]
      refine sum_congr rfl (fun p _ => ?_)
      simp only [indicator, Set.mem_Ioi]
      split_ifs <;> ring
  · exact fun p _ => (hμi.indicator measurableSet_Ioi).const_mul _


/-- **Layer cake over the primes below `c`, with one-sided Mertens.** Put `s_c = log D / log c`,
`a = s_c − 1`, `U* = log D / log x₀ − 1`. If `V(x) log x ≤ ρ V(y) log y` for `x, y ≥ x₀`, and
`m(t) = ∫_{u>t} μ` with the moment identity `∫_{u>a} μ(u)(u − a) = ∫_{u>a} m`, then
`Σ_{p<c} g(p)V(p) m(s_p) ≤ V(c) (ρ s_c⁻¹ ∫_{u>a} m + (ρ − 1) m(a)) + m(U*)`. -/
theorem prime_layer_bound (b : ℕ) (m μ : ℝ → ℝ) {x₀ ρ D c : ℝ} (hx₀ : 1 < x₀) (hρ : 1 ≤ ρ)
    (hmert : ∀ x y : ℝ, x₀ ≤ x → x₀ ≤ y → VB b x * Real.log x ≤ ρ * (VB b y * Real.log y))
    (hc : x₀ ≤ c) (hcD : c ≤ D) (hμ0 : ∀ u, 0 ≤ μ u)
    (hμi : IntegrableOn μ (Ioi (Real.log D / Real.log c - 1)))
    (hμi2 : IntegrableOn (fun u => μ u * (u - (Real.log D / Real.log c - 1))) (Ioi (Real.log D / Real.log c - 1)))
    (hm : ∀ t, Real.log D / Real.log c - 1 ≤ t → m t = ∫ u in Ioi t, μ u)
    (hmom : ∫ u in Ioi (Real.log D / Real.log c - 1), μ u * (u - (Real.log D / Real.log c - 1)) =
      ∫ u in Ioi (Real.log D / Real.log c - 1), m u) :
    ∑ p ∈ primesBelow c, gB b p * VB b p * m (Real.log D / Real.log p - 1) ≤
      VB b c * (ρ * (Real.log D / Real.log c)⁻¹ * (∫ u in Ioi (Real.log D / Real.log c - 1), m u) +
        (ρ - 1) * m (Real.log D / Real.log c - 1)) + m (Real.log D / Real.log x₀ - 1) := by
  set lD := Real.log D with hlD
  set lc := Real.log c with hlc
  set L := Real.log x₀ with hL
  set sc := lD / lc with hsc
  set a := sc - 1 with ha
  set U := lD / L - 1 with hU
  have hc1 : 1 < c := lt_of_lt_of_le hx₀ hc
  have hD1 : 1 < D := lt_of_lt_of_le hc1 hcD
  have hD0 : 0 < D := by linarith
  have hL0 : 0 < L := Real.log_pos hx₀
  have hLc : L ≤ lc := Real.log_le_log (by linarith) hc
  have hlc0 : 0 < lc := lt_of_lt_of_le hL0 hLc
  have hlcD : lc ≤ lD := Real.log_le_log (by linarith) hcD
  have hlD0 : 0 < lD := lt_of_lt_of_le hlc0 hlcD
  have hsc1 : 1 ≤ sc := by rw [hsc, le_div_iff₀ hlc0]; linarith
  have hsc0 : 0 < sc := by linarith
  have hUa : a ≤ U := by
    have : lD / lc ≤ lD / L := div_le_div_of_nonneg_left hlD0.le hL0 hLc
    simp only [ha, hU, hsc]; linarith
  have hVc := VB_pos' b c
  set F : ℝ → ℝ := fun u => VB b c * ρ * sc⁻¹ * (μ u * (u - a)) + VB b c * (ρ - 1) * μ u +
    (Ioi U).indicator μ u with hF
  have hFi : IntegrableOn F (Ioi a) :=
    ((hμi2.const_mul _).add (hμi.const_mul _)).add (hμi.indicator measurableSet_Ioi)
  have key := layer_cake_sum (primesBelow c) (fun p => gB b p * VB b p) (fun p : ℕ => lD / Real.log p - 1)
    m μ F a ?ht hμi ?hm hFi ?hle
  case ht =>
    intro p hp
    have hp' := (mem_primesBelow c p).1 hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
    exact (lt_iff_s_sub_one_lt_sp hD1 hp1 hc1).1 hp'.2
  case hm =>
    intro p hp
    have hp' := (mem_primesBelow c p).1 hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
    exact hm _ ((lt_iff_s_sub_one_lt_sp hD1 hp1 hc1).1 hp'.2).le
  case hle =>
    intro u hu
    have hu1 : 0 < 1 + u := by linarith
    set xu := D ^ (1 / (1 + u)) with hxu
    have hxu0 : 0 < xu := Real.rpow_pos_of_pos hD0 _
    have hlxu : Real.log xu = lD / (1 + u) := by rw [hxu, Real.log_rpow hD0]; ring
    have hlxu0 : 0 < Real.log xu := by rw [hlxu]; positivity
    have hsc_lt : sc < 1 + u := by linarith
    have hxuc : xu ≤ c := by
      have : Real.log xu ≤ lc := by
        rw [hlxu, div_le_iff₀ hu1]
        have : lc * sc = lD := by rw [hsc]; field_simp
        nlinarith
      exact (Real.log_le_log_iff hxu0 (by linarith)).1 this
    -- the partial sum is at most `V(x_u) − V(c)`
    have hS : ∑ p ∈ (primesBelow c).filter (fun p : ℕ => lD / Real.log p - 1 < u), gB b p * VB b p ≤
        VB b xu - VB b c := by
      rw [← telescope b hxuc]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter] at hp
        have hp' := (mem_primesBelow c p).1 hp.1
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
        rw [mem_primesIco]
        exact ⟨hp'.1, (rpow_le_iff_sp_le hD0 hp1 hu1).2 hp.2.le, hp'.2⟩
      · intro p _ _; exact mul_nonneg (gB_nonneg b p) (VB_pos' b p).le
    have hT : VB b xu - VB b c ≤ VB b c * (ρ * (1 + u) / sc - 1) + (if U < u then 1 else 0) := by
      by_cases hx : x₀ ≤ xu
      · have h1 := hmert xu c hx hc
        have h2 : VB b xu ≤ ρ * VB b c * ((1 + u) / sc) := by
          have e : lc / Real.log xu = (1 + u) / sc := by
            rw [hlxu, hsc]; field_simp
          have h1' : VB b xu * Real.log xu ≤ ρ * (VB b c * lc) := h1
          rw [← e, show ρ * VB b c * (lc / Real.log xu) = ρ * (VB b c * lc) / Real.log xu by ring,
            le_div_iff₀ hlxu0]
          linarith
        have h3 : (0 : ℝ) ≤ (if U < u then 1 else 0) := by split_ifs <;> norm_num
        have e2 : VB b c * (ρ * (1 + u) / sc - 1) = ρ * VB b c * ((1 + u) / sc) - VB b c := by ring
        linarith
      · have hUu : U < u := by
          rw [not_le, ← Real.log_lt_log_iff hxu0 (by linarith), hlxu, div_lt_iff₀ hu1] at hx
          rw [hU, sub_lt_iff_lt_add, div_lt_iff₀ hL0]
          linarith
        simp only [hUu, ite_true]
        have h1 := VB_le_one b xu
        have h2 : 0 ≤ VB b c * (ρ * (1 + u) / sc) := by positivity
        nlinarith
    calc μ u * ∑ p ∈ (primesBelow c).filter (fun p : ℕ => lD / Real.log p - 1 < u), gB b p * VB b p
        ≤ μ u * (VB b c * (ρ * (1 + u) / sc - 1) + (if U < u then 1 else 0)) :=
          mul_le_mul_of_nonneg_left (hS.trans hT) (hμ0 u)
      _ = F u := by
          simp only [hF, indicator, Set.mem_Ioi]
          have : sc - 1 = a := rfl
          split_ifs
          · field_simp; ring
          · field_simp; ring
  refine key.trans (le_of_eq ?_)
  have hI1 : IntegrableOn (fun u => VB b c * ρ * sc⁻¹ * (μ u * (u - a))) (Ioi a) := hμi2.const_mul _
  have hI2 : IntegrableOn (fun u => VB b c * (ρ - 1) * μ u) (Ioi a) := hμi.const_mul _
  have hI3 : IntegrableOn ((Ioi U).indicator μ) (Ioi a) := hμi.indicator measurableSet_Ioi
  have e1 : ∫ u in Ioi a, F u = (∫ u in Ioi a, (VB b c * ρ * sc⁻¹ * (μ u * (u - a)) + VB b c * (ρ - 1) * μ u)) +
      ∫ u in Ioi a, (Ioi U).indicator μ u := integral_add (hI1.add hI2) hI3
  have e2 : ∫ u in Ioi a, (VB b c * ρ * sc⁻¹ * (μ u * (u - a)) + VB b c * (ρ - 1) * μ u) =
      (∫ u in Ioi a, VB b c * ρ * sc⁻¹ * (μ u * (u - a))) + ∫ u in Ioi a, VB b c * (ρ - 1) * μ u :=
    integral_add hI1 hI2
  rw [e1, e2, integral_const_mul, integral_const_mul,
    setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hUa, hmom, ← hm a le_rfl,
    ← hm U hUa]
  ring

/-! ## Inputs for the two majorants -/

/-- `∫_{u>b} e^{-u} (u − a) du = (b − a + 1) e^{-b}` (copy of the private `expmoment` in `Cont.lean`). -/
theorem expmoment' (a b : ℝ) (hab : a ≤ b) :
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
    mul_nonneg (exp_pos _).le (by linarith [Set.mem_Ioi.mp hx])
  have hlim : Tendsto G atTop (nhds 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
    have := (h1.add (h2.const_mul (1 - a))).neg
    simp only [pow_one, mul_zero, add_zero, neg_zero] at this
    refine this.congr (fun u => ?_)
    simp only [hG]; ring
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp only [hG]; ring

/-- `e^{-3} e^{-s} ≤ m⁺(s)` for `s > 0`. -/
theorem exp_mul_le_mPlus {s : ℝ} (hs : 0 < s) : exp (-3) * exp (-s) ≤ mPlus s := by
  rcases le_total s 3 with h | h
  · rw [mPlus_of_le h]
    have h1 : exp (-s) ≤ 1 := by rw [exp_le_one_iff]; linarith
    have h2 : 1 ≤ 3 / s := by rw [le_div_iff₀ hs]; linarith
    have h3 : 0 < exp (-3 : ℝ) := exp_pos _
    calc exp (-3) * exp (-s) ≤ exp (-3) * 1 := mul_le_mul_of_nonneg_left h1 h3.le
      _ ≤ exp (-3) * (3 / s) := mul_le_mul_of_nonneg_left h2 h3.le
      _ = 3 * exp (-3) / s := by ring
  · rw [mPlus_of_ge h]
    have : exp (-3 : ℝ) ≤ 1 := by rw [exp_le_one_iff]; norm_num
    nlinarith [exp_pos (-s)]

/-- `log (D/p) / log p = log D / log p − 1` (the inner level `s_p`). -/
theorem log_div_div_log {D p : ℝ} (hD : 0 < D) (hp : 1 < p) :
    Real.log (D / p) / Real.log p = Real.log D / Real.log p - 1 := by
  have := Real.log_pos hp
  rw [Real.log_div hD.ne' (by linarith)]
  field_simp

/-! ## Choice of the Mertens threshold (C.2) -/

/-- **Thresholds for C.2.** For `η > 0` there are `x₀ ≥ e³`, `1 ≤ ρ ≤ 1 + min(η,1)/40` with
`V(x) log x ≤ ρ V(y) log y` (`x, y ≥ x₀`), and `D₀ ≥ x₀⁴` such that the small-prime remainder is negligible:
`4 e^{−log D/log x₀} ≤ (η/4) e^{−3} V(w) e^{−s}` for `D ≥ D₀`, `x₀² ≤ w ≤ D`. -/
theorem tail_setup (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ ρ D₀ : ℝ, exp 3 ≤ x₀ ∧ 1 ≤ ρ ∧ ρ ≤ 1 + min η 1 / 40 ∧
      (∀ x y : ℝ, x₀ ≤ x → x₀ ≤ y → VB b x * Real.log x ≤ ρ * (VB b y * Real.log y)) ∧
      x₀ ^ 4 ≤ D₀ ∧
      ∀ D : ℝ, D₀ ≤ D → ∀ w : ℝ, x₀ ^ 2 ≤ w → w ≤ D →
        4 * exp (-(Real.log D / Real.log x₀)) ≤
          η / 4 * exp (-3) * VB b w * exp (-(Real.log D / Real.log w)) := by
  set δ := min η 1 / 40 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (lt_min hη one_pos) (by norm_num)
  have hδ1 : δ ≤ 1 / 40 := by rw [hδ]; have := min_le_right η 1; linarith
  set η' := δ / 3 with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'1 : η' < 1 := by rw [hη']; linarith
  obtain ⟨xa, hxa, hrat⟩ := VB_log_ratio b hb hη'0 hη'1
  obtain ⟨xb, hxb, hhalf⟩ := VB_log_ge_half b hb
  set κ := kappaB b with hκ
  have hκ0 : 0 < κ := kappaB_pos b
  set x₀ := max xa (exp 3) with hx₀
  have hx₀e : exp 3 ≤ x₀ := le_max_right _ _
  have hx₀1 : 1 < x₀ := lt_of_lt_of_le (by have := add_one_le_exp (3 : ℝ); linarith) hx₀e
  set L := Real.log x₀ with hL
  have hL3 : 3 ≤ L := by rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (exp_pos 3) hx₀e
  have hL0 : 0 < L := by linarith
  set E3 := exp (-3 : ℝ) with hE3
  have hE30 : 0 < E3 := exp_pos _
  set T := 256 * L ^ 2 / (η * κ * E3) with hT
  set D₀ := max (max (x₀ ^ 4) xb) (exp T) with hD₀
  refine ⟨x₀, (1 + η') / (1 - η'), D₀, hx₀e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · intro x y hx hy
    exact hrat x y ((le_max_left _ _).trans hx) ((le_max_left _ _).trans hy)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · intro D hD w hw hwD
    have hD4 : x₀ ^ 4 ≤ D := ((le_max_left _ _).trans (le_max_left _ _)).trans hD
    have hDb : xb ≤ D := ((le_max_right _ _).trans (le_max_left _ _)).trans hD
    have hDT : exp T ≤ D := (le_max_right _ _).trans hD
    have hD1 : 1 < D := lt_of_lt_of_le (one_lt_pow₀ hx₀1 (by norm_num)) hD4
    set lD := Real.log D with hlD
    have hlD0 : 0 < lD := Real.log_pos hD1
    have hlDT : T ≤ lD := by rw [hlD, ← Real.log_exp T]; exact Real.log_le_log (exp_pos T) hDT
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
    have hlw : 2 * L ≤ Real.log w := by
      have := Real.log_le_log (by positivity) hw
      rw [Real.log_pow, ← hL] at this
      push_cast at this
      exact this
    have hlw0 : 0 < Real.log w := by linarith
    -- `V(w) log D ≥ κ/2`
    have hV : κ / 2 ≤ VB b w * lD := by
      have h1 := hhalf D hDb
      have h2 := VB_anti b hwD
      nlinarith
    -- `e^{−s} ≥ X := e^{−log D/(2L)}`
    set x := lD / (2 * L) with hx
    have hx0 : 0 ≤ x := by positivity
    set X := exp (-x) with hX
    have hX0 : 0 < X := exp_pos _
    have hs : exp (-x) ≤ exp (-(lD / Real.log w)) := by
      rw [exp_le_exp, neg_le_neg_iff, hx]
      exact div_le_div_of_nonneg_left hlD0.le (by positivity) hlw
    have hXX : exp (-(lD / L)) = X * X := by
      rw [hX, ← exp_add]; congr 1; rw [hx]; field_simp; ring
    -- `X lD² ≤ 8 L²`
    have hXq : X * lD ^ 2 ≤ 8 * L ^ 2 := by
      have hq := Real.quadratic_le_exp_of_nonneg hx0
      have hexp : exp x * X = 1 := by rw [hX, ← exp_add]; simp
      have h1 : x ^ 2 / 2 ≤ exp x := by nlinarith
      have e : x ^ 2 / 2 = lD ^ 2 / (8 * L ^ 2) := by rw [hx]; field_simp; ring
      rw [e, div_le_iff₀ (by positivity)] at h1
      nlinarith
    -- `32 X lD ≤ η κ E3`
    have hkey : 32 * X * lD ≤ η * κ * E3 := by
      have h1 : 256 * L ^ 2 ≤ lD * (η * κ * E3) := by
        rw [hT, div_le_iff₀ (by positivity)] at hlDT; linarith
      have h2 : 32 * X * lD * lD ≤ 256 * L ^ 2 := by nlinarith
      have h3 : 32 * X * lD * lD ≤ lD * (η * κ * E3) := h2.trans h1
      nlinarith
    rw [hXX]
    have h1 : η * E3 * (κ / 2) ≤ η * E3 * (VB b w * lD) := mul_le_mul_of_nonneg_left hV (by positivity)
    have h2 : 16 * X * lD ≤ η * E3 * VB b w * lD := by linarith
    have h3 : 16 * X ≤ η * E3 * VB b w := le_of_mul_le_mul_right h2 hlD0
    calc 4 * (X * X) ≤ η / 4 * E3 * VB b w * X := by
          have := mul_le_mul_of_nonneg_right h3 hX0.le
          linarith
      _ ≤ η / 4 * E3 * VB b w * exp (-(lD / Real.log w)) :=
          mul_le_mul_of_nonneg_left hs (by have := VB_pos' b w; positivity)

/-! ## C.2: the discrete kernel step -/

/-- **C.2 (−)** from the thresholds of `tail_setup`. -/
theorem kernel_minus_of_setup (b : ℕ) {η x₀ ρ D₀ : ℝ} (hη : 0 < η) (hx₀e : exp 3 ≤ x₀) (hρ1 : 1 ≤ ρ)
    (hρδ : ρ ≤ 1 + min η 1 / 40)
    (hmert : ∀ x y : ℝ, x₀ ≤ x → x₀ ≤ y → VB b x * Real.log x ≤ ρ * (VB b y * Real.log y))
    (hD4 : x₀ ^ 4 ≤ D₀)
    (hsmall : ∀ D : ℝ, D₀ ≤ D → ∀ w : ℝ, x₀ ^ 2 ≤ w → w ≤ D →
      4 * exp (-(Real.log D / Real.log x₀)) ≤ η / 4 * exp (-3) * VB b w * exp (-(Real.log D / Real.log w)))
    (D : ℝ) (hD : D₀ ≤ D) (w : ℝ) (hw : x₀ ^ 2 ≤ w) (hw2 : w ^ 2 ≤ D) :
    ∑ p ∈ primesBelow w, gB b p * VB b p * mPlus (Real.log (D / p) / Real.log p) ≤
      (1 + η) * theta1 * VB b w * mMinus (Real.log D / Real.log w) := by
  have hx₀1 : 1 < x₀ := lt_of_lt_of_le (by have := add_one_le_exp (3 : ℝ); linarith) hx₀e
  have hx₀w : x₀ ≤ w := le_trans (by nlinarith) hw
  have hw1 : 1 < w := lt_of_lt_of_le hx₀1 hx₀w
  have hwD : w ≤ D := le_trans (by nlinarith) hw2
  have hD1 : 1 < D := lt_of_lt_of_le hw1 hwD
  have hD0 : 0 < D := by linarith
  set lD := Real.log D with hlD
  set lw := Real.log w with hlw
  set L := Real.log x₀ with hL
  have hlw0 : 0 < lw := Real.log_pos hw1
  have hL0 : 0 < L := Real.log_pos hx₀1
  have hL4 : 4 * L ≤ lD := by
    have := Real.log_le_log (by positivity) (le_trans hD4 hD)
    rw [Real.log_pow, ← hL] at this; push_cast at this; exact this
  set s := lD / lw with hs
  have hs2 : 2 ≤ s := by
    have := Real.log_le_log (by positivity) hw2
    rw [Real.log_pow, ← hlw] at this; push_cast at this
    rw [hs, le_div_iff₀ hlw0]; linarith
  have ha : 0 < s - 1 := by linarith
  have hsum : ∑ p ∈ primesBelow w, gB b p * VB b p * mPlus (Real.log (D / p) / Real.log p) =
      ∑ p ∈ primesBelow w, gB b p * VB b p * mPlus (lD / Real.log p - 1) := by
    refine sum_congr rfl (fun p hp => ?_)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast ((mem_primesBelow w p).1 hp).1.one_lt
    rw [log_div_div_log hD0 hp1]
  have hlay := prime_layer_bound b mPlus muPlus hx₀1 hρ1 hmert hx₀w hwD muPlus_nonneg
    (integrableOn_muPlus ha) (integrableOn_muPlus_mul_sub ha)
    (fun t ht => (integral_muPlus_Ioi (by linarith)).symm) (integral_muPlus_mul_sub ha)
  rw [hsum]
  refine hlay.trans ?_
  -- the three pieces
  have hV0 : 0 < VB b w := VB_pos' b w
  have hm0 : 0 < mMinus s := mMinus_pos s
  have A1 : ρ * s⁻¹ * (∫ u in Ioi (s - 1), mPlus u) ≤ ρ * (theta1 * mMinus s) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (kernel_minus hs2) (by linarith)
  have A2 : (ρ - 1) * mPlus (s - 1) ≤ (ρ - 1) * (exp 1 * mMinus s) :=
    mul_le_mul_of_nonneg_left (mPlus_sub_one_le hs2) (by linarith)
  have hU3 : 3 ≤ lD / L - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hL0]; linarith
  have A3 : mPlus (lD / L - 1) ≤ η / 4 * (VB b w * mMinus s) := by
    rw [mPlus_of_ge hU3]
    have h1 := hsmall D hD w hw hwD
    have he : exp (-(lD / L - 1)) = exp 1 * exp (-(lD / L)) := by rw [← exp_add]; ring_nf
    have he1 : exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
    have he3 : exp (-3 : ℝ) ≤ 1 := by rw [exp_le_one_iff]; norm_num
    have h2 : exp 1 * exp (-(lD / L)) ≤ 4 * exp (-(lD / L)) :=
      mul_le_mul_of_nonneg_right he1 (exp_pos _).le
    have h3 : η / 4 * exp (-3) * VB b w * exp (-(lD / lw)) ≤ η / 4 * (VB b w * mMinus s) := by
      have : 0 ≤ η / 4 * VB b w * exp (-(lD / lw)) := by positivity
      rw [mMinus, hs]; nlinarith
    rw [he]; linarith
  have he : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hδ : min η 1 / 40 ≤ η / 40 := by have := min_le_left η 1; linarith
  have hcoef : ρ * theta1 + (ρ - 1) * exp 1 + η / 4 ≤ (1 + η) * theta1 := by
    rw [theta1_eq]
    have : (ρ - 1) * exp 1 ≤ (ρ - 1) * 3 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hY : 0 ≤ VB b w * mMinus s := by positivity
  calc VB b w * (ρ * s⁻¹ * (∫ u in Ioi (s - 1), mPlus u) + (ρ - 1) * mPlus (s - 1)) + mPlus (lD / L - 1)
      ≤ VB b w * (ρ * (theta1 * mMinus s) + (ρ - 1) * (exp 1 * mMinus s)) + η / 4 * (VB b w * mMinus s) := by
        have := mul_le_mul_of_nonneg_left (add_le_add A1 A2) hV0.le
        linarith
    _ = (ρ * theta1 + (ρ - 1) * exp 1 + η / 4) * (VB b w * mMinus s) := by ring
    _ ≤ (1 + η) * theta1 * (VB b w * mMinus s) := mul_le_mul_of_nonneg_right hcoef hY
    _ = (1 + η) * theta1 * VB b w * mMinus s := by ring

/-- **C.2 (+)** from the thresholds of `tail_setup`. -/
theorem kernel_plus_of_setup (b : ℕ) {η x₀ ρ D₀ : ℝ} (hη : 0 < η) (hx₀e : exp 3 ≤ x₀) (hρ1 : 1 ≤ ρ)
    (hρδ : ρ ≤ 1 + min η 1 / 40)
    (hmert : ∀ x y : ℝ, x₀ ≤ x → x₀ ≤ y → VB b x * Real.log x ≤ ρ * (VB b y * Real.log y))
    (hD4 : x₀ ^ 4 ≤ D₀)
    (hsmall : ∀ D : ℝ, D₀ ≤ D → ∀ w : ℝ, x₀ ^ 2 ≤ w → w ≤ D →
      4 * exp (-(Real.log D / Real.log x₀)) ≤ η / 4 * exp (-3) * VB b w * exp (-(Real.log D / Real.log w)))
    (D : ℝ) (hD : D₀ ≤ D) (w : ℝ) (hw : x₀ ^ 2 ≤ w) (hwD : w ≤ D) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
        gB b p * VB b p * mMinus (Real.log (D / p) / Real.log p) ≤
      (1 + η) * theta2 * VB b w * mPlus (Real.log D / Real.log w) := by
  have hx₀1 : 1 < x₀ := lt_of_lt_of_le (by have := add_one_le_exp (3 : ℝ); linarith) hx₀e
  have hx₀w : x₀ ≤ w := le_trans (by nlinarith) hw
  have hw1 : 1 < w := lt_of_lt_of_le hx₀1 hx₀w
  have hD1 : 1 < D := lt_of_lt_of_le hw1 hwD
  have hD0 : 0 < D := by linarith
  set lD := Real.log D with hlD
  set lw := Real.log w with hlw
  set L := Real.log x₀ with hL
  have hlw0 : 0 < lw := Real.log_pos hw1
  have hlD0 : 0 < lD := Real.log_pos hD1
  have hL0 : 0 < L := Real.log_pos hx₀1
  have hL3 : 3 ≤ L := by rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (exp_pos 3) hx₀e
  have hL4 : 4 * L ≤ lD := by
    have := Real.log_le_log (by positivity) (le_trans hD4 hD)
    rw [Real.log_pow, ← hL] at this; push_cast at this; exact this
  set s := lD / lw with hs
  have hs0 : 0 < s := by positivity
  set c3 := D ^ (1 / 3 : ℝ) with hc3
  have hc3e : c3 = exp (lD / 3) := by rw [hc3, Real.rpow_def_of_pos hD0, hlD]; congr 1; ring
  have hlc3 : Real.log c3 = lD / 3 := by rw [hc3e, Real.log_exp]
  have hx₀c3 : x₀ ≤ c3 := by
    refine (cube_le_iff hD0.le (by linarith)).1 (le_trans ?_ (le_trans hD4 hD))
    nlinarith [pow_pos (by linarith : (0 : ℝ) < x₀) 3]
  have hc31 : 1 < c3 := lt_of_lt_of_le hx₀1 hx₀c3
  set f : ℕ → ℝ := fun p => gB b p * VB b p * mMinus (Real.log (D / p) / Real.log p) with hf
  rw [sum_filter_cube_le_eq f w hD0.le]
  -- the point `p = D^{1/3}`
  have hpt : ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c3), f p ≤ exp (-(lD / L)) := by
    have hb1 : 1 / c3 ≤ exp (-(lD / L)) := by
      rw [hc3e, one_div, ← exp_neg, exp_le_exp, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left hlD0.le (by norm_num) hL3
    refine le_trans (pointSum_bounds f w c3 (1 / c3) (by positivity) (fun p hp hpc => ?_)).2 hb1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have harg : 0 ≤ Real.log (D / p) / Real.log p := by
      rw [hpc, log_div_div_log hD0 hc31, hlc3]
      rw [le_sub_iff_add_le, zero_add, le_div_iff₀ (by positivity)]; linarith
    have hm1 : mMinus (Real.log (D / p) / Real.log p) ≤ 1 := by
      rw [mMinus, exp_le_one_iff]; linarith
    have hm0 := mMinus_pos (Real.log (D / p) / Real.log p)
    have hg0 := gB_nonneg b p
    have hV0 := VB_pos' b p
    have hV1 := VB_le_one b p
    refine ⟨by simp only [hf]; positivity, ?_⟩
    simp only [hf]
    rw [← hpc]
    calc gB b p * VB b p * mMinus (Real.log (D / p) / Real.log p) ≤ gB b p * 1 * 1 := by
          gcongr
      _ ≤ 1 / (p : ℝ) := by simpa using gB_le_inv b p
  -- the main part over the primes below `c = min(w, D^{1/3})`
  set c := min w c3 with hc
  have hx₀c : x₀ ≤ c := le_min hx₀w hx₀c3
  have hcD : c ≤ D := (min_le_left _ _).trans hwD
  set a := lD / Real.log c - 1 with ha
  have hmom : ∫ u in Ioi a, mMinus u * (u - a) = ∫ u in Ioi a, mMinus u := by
    rw [integral_mMinus_Ioi]
    have := (expmoment' a a le_rfl).2
    simp only [sub_self, zero_add, one_mul] at this
    exact this
  have hlay := prime_layer_bound b mMinus mMinus hx₀1 hρ1 hmert hx₀c hcD (fun u => (mMinus_pos u).le)
    (integrableOn_mMinus _) (expmoment' a a le_rfl).1 (fun t _ => (integral_mMinus_Ioi t).symm) hmom
  have hsum : ∑ p ∈ primesBelow c, f p = ∑ p ∈ primesBelow c, gB b p * VB b p * mMinus (lD / Real.log p - 1) := by
    refine sum_congr rfl (fun p hp => ?_)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast ((mem_primesBelow c p).1 hp).1.one_lt
    simp only [hf]; rw [log_div_div_log hD0 hp1]
  rw [hsum]
  have hU : mMinus (lD / L - 1) ≤ 3 * exp (-(lD / L)) := by
    rw [mMinus, show -(lD / L - 1) = 1 + -(lD / L) by ring, exp_add]
    have := Real.exp_one_lt_d9
    exact mul_le_mul_of_nonneg_right (by norm_num at this; linarith) (exp_pos _).le
  rw [integral_mMinus_Ioi] at hlay
  -- `θ₂ m⁺(s)` and the main comparison
  have hV0 := VB_pos' b w
  have hθ : theta2 = exp 1 / 3 := rfl
  have hmain : VB b c * (ρ * (lD / Real.log c)⁻¹ * exp (-a) + (ρ - 1) * mMinus a) ≤
      ρ * (4 * ρ - 3) * (theta2 * VB b w * mPlus s) := by
    rw [mMinus]
    rcases le_or_gt w c3 with hwc | hwc
    · -- `s ≥ 3`, `c = w`
      have hcw : c = w := min_eq_left hwc
      have hs3 : 3 ≤ s := by
        have := Real.log_le_log (by linarith) hwc
        rw [hlc3] at this
        rw [hs, le_div_iff₀ hlw0]; linarith
      rw [hcw, mPlus_of_ge hs3]
      have ha' : a = s - 1 := by rw [ha, hcw]
      rw [ha', show lD / Real.log w = s from rfl]
      have he : exp (-(s - 1)) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
      rw [he, hθ]
      have hinv : s⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
      have hE : 0 < exp 1 * exp (-s) := by positivity
      have h1 : ρ * s⁻¹ ≤ ρ * (1 / 3) := mul_le_mul_of_nonneg_left hinv (by linarith)
      have h2 : VB b w * (exp 1 * exp (-s)) * (ρ * s⁻¹ + (ρ - 1)) ≤
          VB b w * (exp 1 * exp (-s)) * (ρ * (1 / 3) + (ρ - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : (4 * ρ - 3) * (VB b w * (exp 1 * exp (-s))) ≤ ρ * (4 * ρ - 3) * (VB b w * (exp 1 * exp (-s))) := by
        have : 0 ≤ (4 * ρ - 3) * (VB b w * (exp 1 * exp (-s))) := by
          have : 0 ≤ 4 * ρ - 3 := by linarith
          positivity
        nlinarith
      calc VB b w * (ρ * s⁻¹ * (exp 1 * exp (-s)) + (ρ - 1) * (exp 1 * exp (-s)))
          = VB b w * (exp 1 * exp (-s)) * (ρ * s⁻¹ + (ρ - 1)) := by ring
        _ ≤ VB b w * (exp 1 * exp (-s)) * (ρ * (1 / 3) + (ρ - 1)) := h2
        _ = (4 * ρ - 3) * (VB b w * (exp 1 * exp (-s))) / 3 := by ring
        _ ≤ ρ * (4 * ρ - 3) * (VB b w * (exp 1 * exp (-s))) / 3 := by linarith
        _ = ρ * (4 * ρ - 3) * (exp 1 / 3 * VB b w * exp (-s)) := by ring
    · -- `s < 3`, `c = D^{1/3}`
      have hcw : c = c3 := min_eq_right hwc.le
      have hs3 : s < 3 := by
        have := Real.log_lt_log (by linarith) hwc
        rw [hlc3] at this
        rw [hs, div_lt_iff₀ hlw0]; linarith
      rw [hcw, mPlus_of_le hs3.le]
      have ha' : a = 2 := by rw [ha, hcw, hlc3]; field_simp; ring
      have hsc : lD / Real.log c3 = 3 := by rw [hlc3]; field_simp
      rw [ha', hsc]
      -- `V(c₃) lD/3 ≤ ρ V(w) lw`
      have hM := hmert c3 w hx₀c3 hx₀w
      rw [hlc3] at hM
      have he : exp 1 * (3 * exp (-3)) = 3 * exp (-2) := by
        rw [show exp 1 * (3 * exp (-3)) = 3 * (exp 1 * exp (-3)) by ring, ← exp_add]; norm_num
      have hE2 : 0 < exp (-2 : ℝ) := exp_pos _
      have hVc := VB_pos' b c3
      -- target: `V(c₃)(ρ/3 + ρ − 1) e^{-2} ≤ ρ(4ρ−3) (e/3) V(w) 3e^{-3}/s`
      have e2 : exp 1 * exp (-3) = exp (-2) := by rw [← exp_add]; norm_num
      have hlw' := hlw0.ne'
      have hlD' := hlD0.ne'
      have hR : ρ * (4 * ρ - 3) * (exp 1 / 3 * VB b w * (3 * exp (-3) / s)) =
          ρ * (4 * ρ - 3) * exp (-2) * VB b w * lw / lD := by
        rw [← e2, hs]; field_simp
      rw [hθ, hR, le_div_iff₀ hlD0]
      have h4' : 0 ≤ 4 * ρ - 3 := by linarith
      have h4 : 0 ≤ (4 * ρ - 3) * exp (-2) := by positivity
      have := mul_le_mul_of_nonneg_left hM h4
      calc VB b c3 * (ρ * 3⁻¹ * exp (-2) + (ρ - 1) * exp (-2)) * lD
          = (4 * ρ - 3) * exp (-2) * (VB b c3 * (lD / 3)) := by ring
        _ ≤ (4 * ρ - 3) * exp (-2) * (ρ * (VB b w * lw)) := this
        _ = ρ * (4 * ρ - 3) * exp (-2) * VB b w * lw := by ring
  -- the small terms
  have hsm := hsmall D hD w hw hwD
  have hmp : exp (-3) * exp (-s) ≤ mPlus s := exp_mul_le_mPlus hs0
  have hsm' : 4 * exp (-(lD / L)) ≤ η / 4 * (VB b w * mPlus s) := by
    have : η / 4 * exp (-3) * VB b w * exp (-(lD / lw)) ≤ η / 4 * (VB b w * mPlus s) := by
      have := mul_le_mul_of_nonneg_left hmp (by positivity : 0 ≤ η / 4 * VB b w)
      rw [hs]; linarith
    linarith
  -- the coefficient
  have hθ2 : 0.9 ≤ theta2 := by
    rw [hθ]; have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have hδ : min η 1 / 40 ≤ η / 40 := by have := min_le_left η 1; linarith
  have hδ1 : min η 1 / 40 ≤ 1 / 40 := by have := min_le_right η 1; linarith
  have hcoef : ρ * (4 * ρ - 3) * theta2 + η / 4 ≤ (1 + η) * theta2 := by
    have hρ2 : ρ ≤ 2 := by linarith
    have h1 : ρ * (4 * ρ - 3) ≤ 1 + 9 * (ρ - 1) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hρ2)]
    have h2 : ρ * (4 * ρ - 3) * theta2 ≤ (1 + 9 * (ρ - 1)) * theta2 :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : (ρ - 1) * theta2 ≤ η / 40 * theta2 := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h4 : η * 0.9 ≤ η * theta2 := mul_le_mul_of_nonneg_left hθ2 hη.le
    linarith
  have hY : 0 ≤ VB b w * mPlus s := by have := mPlus_pos hs0; positivity
  have hpt' := hpt
  calc _ ≤ ρ * (4 * ρ - 3) * (theta2 * VB b w * mPlus s) + 4 * exp (-(lD / L)) := by
        have := add_le_add hlay hpt
        linarith only [this, hmain, hU]
    _ ≤ (ρ * (4 * ρ - 3) * theta2 + η / 4) * (VB b w * mPlus s) := by
        have e : (ρ * (4 * ρ - 3) * theta2 + η / 4) * (VB b w * mPlus s) =
            ρ * (4 * ρ - 3) * (theta2 * VB b w * mPlus s) + η / 4 * (VB b w * mPlus s) := by ring
        rw [e]; linarith only [hsm']
    _ ≤ (1 + η) * theta2 * (VB b w * mPlus s) := mul_le_mul_of_nonneg_right hcoef hY
    _ = (1 + η) * theta2 * VB b w * mPlus s := by ring

/-- **Lemma C.2 (discrete kernel step).** For every `η > 0` there are `W₀ ≥ 2` and `D₀ ≥ W₀` such that for
`D ≥ D₀` and `W₀ ≤ w ≤ D`, with `s = log D / log w` and `s_p = log (D/p) / log p`:
(−) if `w² ≤ D`: `Σ_{p<w} g(p)V(p) m⁺(s_p) ≤ (1+η) θ₁ V(w) m⁻(s)`;
(+) `Σ_{p<w, p³≤D} g(p)V(p) m⁻(s_p) ≤ (1+η) θ₂ V(w) m⁺(s)`. -/
theorem kernel_step (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) :
    ∃ W₀ D₀ : ℝ, 2 ≤ W₀ ∧ W₀ ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ w : ℝ, W₀ ≤ w → w ≤ D →
      (w ^ 2 ≤ D → ∑ p ∈ primesBelow w, gB b p * VB b p * mPlus (Real.log (D / p) / Real.log p) ≤
        (1 + η) * theta1 * VB b w * mMinus (Real.log D / Real.log w)) ∧
      ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
          gB b p * VB b p * mMinus (Real.log (D / p) / Real.log p) ≤
        (1 + η) * theta2 * VB b w * mPlus (Real.log D / Real.log w) := by
  obtain ⟨x₀, ρ, D₀, hx₀e, hρ1, hρδ, hmert, hD4, hsmall⟩ := tail_setup b hb hη
  have hx₀1 : 1 < x₀ := lt_of_lt_of_le (by have := add_one_le_exp (3 : ℝ); linarith) hx₀e
  have hx₀2 : 2 ≤ x₀ := le_trans (by have := add_one_le_exp (3 : ℝ); linarith) hx₀e
  refine ⟨x₀ ^ 2, D₀, by nlinarith, le_trans ?_ hD4, fun D hD w hw hwD => ⟨fun hw2 =>
    kernel_minus_of_setup b hη hx₀e hρ1 hρδ hmert hD4 hsmall D hD w hw hw2,
    kernel_plus_of_setup b hη hx₀e hρ1 hρδ hmert hD4 hsmall D hD w hw hwD⟩⟩
  exact pow_le_pow_right₀ hx₀1.le (by norm_num)

/-! ## C.3: the uniform geometric bound -/

/-- `B⁺_k(D, w) ≤ Π_{p<W} (1 + g p)` for `w ≤ W` (crude bound, A.3). -/
theorem prod_primesBelow_mono (b : ℕ) {w W : ℝ} (h : w ≤ W) :
    ∏ p ∈ primesBelow w, (1 + gB b p) ≤ ∏ p ∈ primesBelow W, (1 + gB b p) := by
  have hsub : primesBelow w ⊆ primesBelow W := by
    intro p hp
    rw [mem_primesBelow] at hp ⊢
    exact ⟨hp.1, lt_of_lt_of_le hp.2 h⟩
  rw [← prod_sdiff hsub]
  have h1 : 1 ≤ ∏ p ∈ primesBelow W \ primesBelow w, (1 + gB b p) :=
    one_le_prod₀ (fun p _ => by linarith [gB_nonneg b p])
  have h2 : 0 ≤ ∏ p ∈ primesBelow w, (1 + gB b p) :=
    prod_nonneg (fun p _ => by linarith [gB_nonneg b p])
  nlinarith

/-- **Lemma C.3 (uniform geometric bound).** For `η > 0` put `A_η = (1+η)² A` (`A = rateA = θ₁θ₂`).
There is `C > 0` such that for **all** `k`, all levels `D` and all `2 ≤ w ≤ D` (`s = log D / log w`):
`B⁺_k(D, w) ≤ C A_η^k V(w) m⁺(s)`, and for `w² ≤ D`: `B⁻_{k+1}(D, w) ≤ C (1+η) θ₁ A_η^k V(w) m⁻(s)`.
Small levels are absorbed into `C`. -/
theorem tail_geom (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (∀ D w : ℝ, 2 ≤ w → w ≤ D →
        BP b k D w ≤ C * ((1 + η) ^ 2 * rateA) ^ k * VB b w * mPlus (Real.log D / Real.log w)) ∧
      (∀ D w : ℝ, 2 ≤ w → w ^ 2 ≤ D →
        BM b (k + 1) D w ≤ C * ((1 + η) * theta1) * ((1 + η) ^ 2 * rateA) ^ k * VB b w *
          mMinus (Real.log D / Real.log w)) := by
  obtain ⟨W₀, D₁, hW2, hWD, hker⟩ := kernel_step b hb hη
  obtain ⟨D₂, hD₂1, hcube⟩ := VB_cube_le b hb (η := 1 / 3) (by norm_num) (by norm_num)
  set D₀ := max (max D₁ D₂) (W₀ ^ (W₀ + 3)) with hD₀
  have hD₀1 : D₁ ≤ D₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hD₀2 : D₂ ≤ D₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hD₀3 : W₀ ^ (W₀ + 3) ≤ D₀ := le_max_right _ _
  have hD₀two : 2 ≤ D₀ := hW2.trans (hWD.trans hD₀1)
  set r := (1 + η) ^ 2 * rateA with hr
  have hr0 : 0 < r := mul_pos (by positivity) rateA_pos
  set q := (1 + η) * theta1 with hq
  have hq0 : 0 < q := mul_pos (by linarith) theta1_pos
  set rm := min r 1 with hrm
  have hrm0 : 0 < rm := lt_min hr0 one_pos
  set N₀ := ⌈D₀⌉₊ with hN₀
  set Pi0 := ∏ p ∈ primesBelow D₀, (1 + gB b p) with hPi0
  have hPi01 : 1 ≤ Pi0 := by
    rw [hPi0]; exact one_le_prod₀ (fun p _ => by linarith [gB_nonneg b p])
  set L₀ := Real.log D₀ / Real.log 2 with hL₀
  have hL₀0 : 0 < L₀ := div_pos (Real.log_pos (by linarith)) (Real.log_pos (by norm_num))
  set mmin := min (mPlus L₀) (mMinus L₀) with hmmin
  have hmmin0 : 0 < mmin := lt_min (mPlus_pos hL₀0) (mMinus_pos _)
  have hVD₀ := VB_pos' b D₀
  set Ms := Pi0 / (rm ^ N₀ * VB b D₀ * mmin) with hMs
  have hMs0 : 0 < Ms := by positivity
  set C := max (2 * exp 3) (max Ms (Ms / q)) with hC
  have hC1 : 2 * exp 3 ≤ C := le_max_left _ _
  have hC2 : Ms ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Ms ≤ C * q := by
    have : Ms / q ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    rwa [div_le_iff₀ hq0] at this
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC1
  -- facts on `s`
  have hs_pos : ∀ D w : ℝ, 2 ≤ w → w ≤ D → 1 ≤ Real.log D / Real.log w := by
    intro D w hw hwD
    have hlw : 0 < Real.log w := Real.log_pos (by linarith)
    rw [le_div_iff₀ hlw, one_mul]; exact Real.log_le_log (by linarith) hwD
  -- the small-level estimate
  have small : ∀ (k : ℕ) (X C' m : ℝ) (D w : ℝ), k ≤ N₀ → X ≤ Pi0 → Ms ≤ C' → mmin ≤ m →
      2 ≤ w → w ≤ D → D < D₀ → X ≤ C' * r ^ k * VB b w * m := by
    intro k X C' m D w hk hX hC' hm hw hwD hD
    have e : Pi0 = Ms * (rm ^ N₀ * VB b D₀ * mmin) := by rw [hMs]; field_simp
    have h1 : rm ^ N₀ ≤ r ^ k :=
      (pow_le_pow_of_le_one hrm0.le (min_le_right _ _) hk).trans
        (pow_le_pow_left₀ hrm0.le (min_le_left _ _) k)
    have h2 : VB b D₀ ≤ VB b w := VB_anti b (by linarith)
    calc X ≤ Ms * (rm ^ N₀ * VB b D₀ * mmin) := e ▸ hX
      _ ≤ C' * (r ^ k * VB b w * m) := by
          have hV := VB_pos' b w
          exact mul_le_mul hC' (mul_le_mul (mul_le_mul h1 h2 hVD₀.le (pow_nonneg hr0.le k)) hm hmmin0.le
            (by positivity)) (by positivity) (hMs0.le.trans hC')
      _ = C' * r ^ k * VB b w * m := by ring
  -- `m(s) ≥ mmin` at small levels
  have hsL : ∀ D w : ℝ, 2 ≤ w → w ≤ D → D < D₀ → Real.log D / Real.log w ≤ L₀ := by
    intro D w hw hwD hD
    have hlw : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    calc Real.log D / Real.log w ≤ Real.log D / Real.log 2 := div_le_div_of_nonneg_left hlD hl2 hlw
      _ ≤ L₀ := div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hD.le) hl2.le
  have hmP : ∀ D w : ℝ, 2 ≤ w → w ≤ D → D < D₀ → mmin ≤ mPlus (Real.log D / Real.log w) := fun D w hw hwD hD =>
    (min_le_left _ _).trans (mPlus_anti (by linarith [hs_pos D w hw hwD]) (hsL D w hw hwD hD))
  have hmM : ∀ D w : ℝ, 2 ≤ w → w ≤ D → D < D₀ → mmin ≤ mMinus (Real.log D / Real.log w) := fun D w hw hwD hD =>
    (min_le_right _ _).trans (mMinus_anti (hsL D w hw hwD hD))
  have hcard : ∀ D w : ℝ, 2 ≤ w → w ≤ D → D < D₀ → (primesBelow w).card < N₀ := by
    intro D w hw hwD hD
    have h1 := card_primesBelow_lt w hw
    have h2 : D₀ ≤ (N₀ : ℝ) := Nat.le_ceil D₀
    exact_mod_cast (show ((primesBelow w).card : ℝ) < N₀ by linarith)
  have hcrude : ∀ D w : ℝ, w ≤ D → D < D₀ → ∏ p ∈ primesBelow w, (1 + gB b p) ≤ Pi0 :=
    fun D w hwD hD => prod_primesBelow_mono b (by linarith)
  -- the two induction steps
  set P : ℕ → Prop := fun k => ∀ D w : ℝ, 2 ≤ w → w ≤ D →
    BP b k D w ≤ C * r ^ k * VB b w * mPlus (Real.log D / Real.log w) with hP
  set Q : ℕ → Prop := fun k => ∀ D w : ℝ, 2 ≤ w → w ^ 2 ≤ D →
    BM b (k + 1) D w ≤ C * q * r ^ k * VB b w * mMinus (Real.log D / Real.log w) with hQ
  have hPsmall : ∀ k D w, 2 ≤ w → w ≤ D → D < D₀ →
      BP b k D w ≤ C * r ^ k * VB b w * mPlus (Real.log D / Real.log w) := by
    intro k D w hw hwD hD
    by_cases hk : k ≤ N₀
    · exact small k _ C _ D w hk ((BP_le_prod b k D w).trans (hcrude D w hwD hD)) hC2 (hmP D w hw hwD hD) hw hwD hD
    · rw [BP_eq_zero_of_card b k D w (by have := hcard D w hw hwD hD; omega)]
      have := mPlus_pos (by linarith [hs_pos D w hw hwD] : 0 < Real.log D / Real.log w)
      have := VB_pos' b w
      positivity
  have hQsmall : ∀ k D w, 2 ≤ w → w ≤ D → D < D₀ →
      BM b (k + 1) D w ≤ C * q * r ^ k * VB b w * mMinus (Real.log D / Real.log w) := by
    intro k D w hw hwD hD
    by_cases hk : k ≤ N₀
    · exact small k _ (C * q) _ D w hk ((BM_le_prod b (k + 1) D w).trans (hcrude D w hwD hD)) hC3
        (hmM D w hw hwD hD) hw hwD hD
    · rw [BM_eq_zero_of_card b (k + 1) D w (by have := hcard D w hw hwD hD; omega)]
      have := mMinus_pos (Real.log D / Real.log w)
      have := VB_pos' b w
      positivity
  have hP0 : P 0 := by
    intro D w hw hwD
    rcases lt_or_ge D D₀ with hD | hD
    · exact hPsmall 0 D w hw hwD hD
    have hD0 : 0 < D := by linarith
    have hs1 := hs_pos D w hw hwD
    have hR : 0 ≤ C * r ^ 0 * VB b w * mPlus (Real.log D / Real.log w) := by
      have := mPlus_pos (by linarith : 0 < Real.log D / Real.log w)
      have := VB_pos' b w
      positivity
    by_cases h3 : w ^ 3 ≤ D
    · rw [BP_eq_zero_of_pow_le b 0 (by simpa using h3)]; exact hR
    have hcw : D ^ (1 / 3 : ℝ) < w := (lt_cube_iff hD0.le (by linarith)).1 (not_le.1 h3)
    have hlw : 0 < Real.log w := Real.log_pos (by linarith)
    have hs3 : Real.log D / Real.log w ≤ 3 := by
      rw [div_le_iff₀ hlw]
      have := Real.log_le_log hD0 (not_le.1 h3).le
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hE := (pointSum_gV_le b w (Real.rpow_nonneg hD0.le (1 / 3 : ℝ))).1
    rw [BP_zero_eq, sum_cube_gt_eq b w hD0.le, min_eq_right hcw.le]
    have hcub := hcube D (hD₀2.trans hD) w hcw.le
    have hV := VB_pos' b w
    rw [pow_zero, mul_one, mPlus_of_le hs3]
    have e : (1 + 1 / 3 : ℝ) / (1 - 1 / 3) * (3 / (Real.log D / Real.log w)) * VB b w =
        2 * exp 3 * VB b w * (3 * exp (-3) / (Real.log D / Real.log w)) := by
      have hsne : Real.log D / Real.log w ≠ 0 := by linarith
      rw [Real.exp_neg]
      field_simp
      ring
    have h2 : 2 * exp 3 * VB b w * (3 * exp (-3) / (Real.log D / Real.log w)) ≤
        C * VB b w * (3 * exp (-3) / (Real.log D / Real.log w)) := by
      have : 0 ≤ VB b w * (3 * exp (-3) / (Real.log D / Real.log w)) := by
        have : 0 < Real.log D / Real.log w := by linarith
        positivity
      nlinarith
    linarith
  have stepPQ : ∀ k, P k → Q k := by
    intro k hPk D w hw hw2
    have hwD : w ≤ D := le_trans (by nlinarith) hw2
    rcases lt_or_ge D D₀ with hD | hD
    · exact hQsmall k D w hw hwD hD
    rcases lt_or_ge w W₀ with hwW | hwW
    · rw [(no_chains_below b hw hwW (hD₀3.trans hD) (k + 1)).2]
      have := mMinus_pos (Real.log D / Real.log w)
      have := VB_pos' b w
      positivity
    have hD0 : 0 < D := by linarith
    have hk := (hker D (hD₀1.trans hD) w hwW hwD).1 hw2
    rw [BM_succ_eq]
    calc ∑ p ∈ primesBelow w, gB b p * BP b k (D / p) p
        ≤ ∑ p ∈ primesBelow w, gB b p * (C * r ^ k * VB b p * mPlus (Real.log (D / p) / Real.log p)) := by
          refine sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left ?_ (gB_nonneg b p))
          have hp' := (mem_primesBelow w p).1 hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
          have hp0 : (0 : ℝ) < p := by linarith
          refine hPk (D / p) p hp2 ?_
          rw [le_div_iff₀ hp0]
          nlinarith [hp'.2]
      _ = C * r ^ k * ∑ p ∈ primesBelow w, gB b p * VB b p * mPlus (Real.log (D / p) / Real.log p) := by
          rw [mul_sum]; exact sum_congr rfl (fun p _ => by ring)
      _ ≤ C * r ^ k * ((1 + η) * theta1 * VB b w * mMinus (Real.log D / Real.log w)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = C * q * r ^ k * VB b w * mMinus (Real.log D / Real.log w) := by rw [hq]; ring
  have stepQP : ∀ k, Q k → P (k + 1) := by
    intro k hQk D w hw hwD
    rcases lt_or_ge D D₀ with hD | hD
    · exact hPsmall (k + 1) D w hw hwD hD
    rcases lt_or_ge w W₀ with hwW | hwW
    · rw [(no_chains_below b hw hwW (hD₀3.trans hD) (k + 1)).1]
      have := mPlus_pos (by linarith [hs_pos D w hw hwD] : 0 < Real.log D / Real.log w)
      have := VB_pos' b w
      positivity
    have hk := (hker D (hD₀1.trans hD) w hwW hwD).2
    rw [BP_succ_eq]
    calc ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), gB b p * BM b (k + 1) (D / p) p
        ≤ ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
            gB b p * (C * q * r ^ k * VB b p * mMinus (Real.log (D / p) / Real.log p)) := by
          refine sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left ?_ (gB_nonneg b p))
          rw [Finset.mem_filter] at hp
          have hp' := (mem_primesBelow w p).1 hp.1
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
          have hp0 : (0 : ℝ) < p := by linarith
          refine hQk (D / p) p hp2 ?_
          rw [le_div_iff₀ hp0]
          nlinarith [hp.2]
      _ = C * q * r ^ k * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
            gB b p * VB b p * mMinus (Real.log (D / p) / Real.log p) := by
          rw [mul_sum]; exact sum_congr rfl (fun p _ => by ring)
      _ ≤ C * q * r ^ k * ((1 + η) * theta2 * VB b w * mPlus (Real.log D / Real.log w)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = C * r ^ (k + 1) * VB b w * mPlus (Real.log D / Real.log w) := by
          rw [hq, hr, rateA, pow_succ]; ring
  have hPQ : ∀ k, P k ∧ Q k := by
    intro k
    induction k with
    | zero => exact ⟨hP0, stepPQ 0 hP0⟩
    | succ k ih =>
      have h := stepQP k ih.2
      exact ⟨h, stepPQ (k + 1) h⟩
  exact ⟨C, hC0, fun k => ⟨(hPQ k).1, (hPQ k).2⟩⟩

/-! ## C.4: the uniform tail -/

/-- `(1 + 1/10)² A < 1`. -/
theorem rate_tenth_lt_one : (1 + 1 / 10 : ℝ) ^ 2 * rateA < 1 := by
  have := rateA_lt; have := rateA_pos; nlinarith

/-- Uniform geometric bounds with one constant: `B⁺_k, B⁻_k ≤ C' r^k V(w)` with `r = (11/10)² A < 1`. -/
theorem B_le_geom (b : ℕ) (hb : 2 ≤ b) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ, ∀ D w : ℝ, 2 ≤ w → w ≤ D →
      BP b k D w ≤ C' * ((1 + 1 / 10) ^ 2 * rateA) ^ k * VB b w ∧
      (w ^ 2 ≤ D → BM b k D w ≤ C' * ((1 + 1 / 10) ^ 2 * rateA) ^ k * VB b w) := by
  obtain ⟨C, hC0, hC⟩ := tail_geom b hb (η := 1 / 10) (by norm_num)
  set r := (1 + 1 / 10 : ℝ) ^ 2 * rateA with hr
  have hr0 : 0 < r := mul_pos (by norm_num) rateA_pos
  set q := (1 + 1 / 10 : ℝ) * theta1 with hq
  have hq0 : 0 < q := mul_pos (by norm_num) theta1_pos
  refine ⟨max C (C * q / r), lt_max_of_lt_left hC0, fun k D w hw hwD => ⟨?_, fun hw2 => ?_⟩⟩
  · have hs1 : 1 ≤ Real.log D / Real.log w := by
      have hlw : 0 < Real.log w := Real.log_pos (by linarith)
      rw [le_div_iff₀ hlw, one_mul]; exact Real.log_le_log (by linarith) hwD
    have hm1 : mPlus (Real.log D / Real.log w) ≤ 1 :=
      (mPlus_le_of_one_le hs1).trans mPlus_three_exp_lt_one.le
    have hV := VB_pos' b w
    calc BP b k D w ≤ C * r ^ k * VB b w * mPlus (Real.log D / Real.log w) := (hC k).1 D w hw hwD
      _ ≤ C * r ^ k * VB b w * 1 := mul_le_mul_of_nonneg_left hm1 (by positivity)
      _ ≤ max C (C * q / r) * r ^ k * VB b w := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hV.le
  · have hV := VB_pos' b w
    have hlw : 0 < Real.log w := Real.log_pos (by linarith)
    have hs0 : 0 ≤ Real.log D / Real.log w := div_nonneg (Real.log_nonneg (by linarith)) hlw.le
    cases k with
    | zero => rw [BM_zero]; have : 0 < max C (C * q / r) := lt_max_of_lt_left hC0
              positivity
    | succ k =>
      have hm1 : mMinus (Real.log D / Real.log w) ≤ 1 := by rw [mMinus, exp_le_one_iff]; linarith
      calc BM b (k + 1) D w ≤ C * q * r ^ k * VB b w * mMinus (Real.log D / Real.log w) := (hC k).2 D w hw hw2
        _ ≤ C * q * r ^ k * VB b w * 1 := mul_le_mul_of_nonneg_left hm1 (by positivity)
        _ = C * q / r * r ^ (k + 1) * VB b w := by rw [pow_succ]; field_simp
        _ ≤ max C (C * q / r) * r ^ (k + 1) * VB b w :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hV.le

/-- **Corollary C.4 (uniform tail).** For every `ε > 0` there is `K` such that for every `K' ≥ K`, every
level `D`, every `2 ≤ w ≤ D` and every `N`: `Σ_{K' ≤ k < N} B⁺_k(D, w) ≤ ε V(w)`, and, if `w² ≤ D`,
`Σ_{K' ≤ k < N} B⁻_k(D, w) ≤ ε V(w)`. -/
theorem tail_small (b : ℕ) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∀ D w : ℝ, 2 ≤ w → w ≤ D → ∀ N : ℕ,
      ∑ k ∈ Ico K' N, BP b k D w ≤ ε * VB b w ∧
      (w ^ 2 ≤ D → ∑ k ∈ Ico K' N, BM b k D w ≤ ε * VB b w) := by
  obtain ⟨C', hC'0, hC'⟩ := B_le_geom b hb
  set r := (1 + 1 / 10 : ℝ) ^ 2 * rateA with hr
  have hr0 : 0 < r := mul_pos (by norm_num) rateA_pos
  have hr1 : r < 1 := rate_tenth_lt_one
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε * (1 - r) / C' by
    have : 0 < 1 - r := by linarith
    positivity) hr1
  refine ⟨K, fun K' hKK' D w hw hwD N => ?_⟩
  have hV := VB_pos' b w
  have hgeom : ∑ k ∈ Ico K' N, C' * r ^ k * VB b w ≤ ε * VB b w := by
    have h1 : ∑ k ∈ Ico K' N, C' * r ^ k * VB b w = C' * VB b w * ∑ k ∈ Ico K' N, r ^ k := by
      rw [mul_sum]; exact sum_congr rfl (fun k _ => by ring)
    have h2 : ∑ k ∈ Ico K' N, r ^ k ≤ r ^ K' / (1 - r) := geom_sum_Ico_le_of_lt_one hr0.le hr1
    have h3 : r ^ K' ≤ r ^ K := pow_le_pow_of_le_one hr0.le hr1.le hKK'
    have h4 : r ^ K' / (1 - r) ≤ ε / C' := by
      rw [div_le_div_iff₀ (by linarith) hC'0]
      have := (lt_div_iff₀ hC'0).1 (show r ^ K < ε * (1 - r) / C' from hK)
      nlinarith
    rw [h1]
    calc C' * VB b w * ∑ k ∈ Ico K' N, r ^ k ≤ C' * VB b w * (ε / C') :=
          mul_le_mul_of_nonneg_left (h2.trans h4) (by positivity)
      _ = ε * VB b w := by field_simp
  exact ⟨(sum_le_sum (fun k _ => (hC' k D w hw hwD).1)).trans hgeom,
    fun hw2 => (sum_le_sum (fun k _ => (hC' k D w hw hwD).2 hw2)).trans hgeom⟩

/-! ## Forms for the assembly (§6, phase E12) -/

/-- For `π(w) < N`, `Σ_{k<N} B⁺_k = Σ_{k<K} B⁺_k + Σ_{K≤k<N} B⁺_k` for every `K` (also `K > N`). -/
theorem sum_range_split_BP (b : ℕ) (D w : ℝ) {N : ℕ} (hN : (primesBelow w).card < N) (K : ℕ) :
    ∑ k ∈ range N, BP b k D w = ∑ k ∈ range K, BP b k D w + ∑ k ∈ Ico K N, BP b k D w := by
  rcases le_total K N with h | h
  · exact (sum_range_add_sum_Ico _ h).symm
  · rw [Finset.Ico_eq_empty_of_le h, sum_empty, add_zero, ← sum_range_add_sum_Ico _ h, left_eq_add]
    exact sum_eq_zero (fun k hk => BP_eq_zero_of_card b k D w (by rw [Finset.mem_Ico] at hk; omega))

/-- For `π(w) < N`, `Σ_{k<N} B⁻_k = Σ_{k<K} B⁻_k + Σ_{K≤k<N} B⁻_k` for every `K`. -/
theorem sum_range_split_BM (b : ℕ) (D w : ℝ) {N : ℕ} (hN : (primesBelow w).card < N) (K : ℕ) :
    ∑ k ∈ range N, BM b k D w = ∑ k ∈ range K, BM b k D w + ∑ k ∈ Ico K N, BM b k D w := by
  rcases le_total K N with h | h
  · exact (sum_range_add_sum_Ico _ h).symm
  · rw [Finset.Ico_eq_empty_of_le h, sum_empty, add_zero, ← sum_range_add_sum_Ico _ h, left_eq_add]
    exact sum_eq_zero (fun k hk => BM_eq_zero_of_card b k D w (by rw [Finset.mem_Ico] at hk; omega))

/-- **C.4 for `S⁺`** (assembly form): for `ε > 0` there is `K` with, for all `K' ≥ K`, all `z`, `s` with
`2 ≤ w := z^{1/s} ≤ z`: `|S⁺(z, s) − (V(w) + Σ_{k<K'} B⁺_k(z, w))| ≤ ε V(w)`. -/
theorem Splus_trunc (b : ℕ) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∀ z s : ℝ, 2 ≤ z ^ (1 / s) → z ^ (1 / s) ≤ z →
      |Splus b z s - (VB b (z ^ (1 / s)) + ∑ k ∈ range K', BP b k z (z ^ (1 / s)))| ≤
        ε * VB b (z ^ (1 / s)) := by
  obtain ⟨K, hK⟩ := tail_small b hb hε
  refine ⟨K, fun K' hKK' z s hw hwz => ?_⟩
  rw [Splus_eq, sum_range_split_BP b z _ (Nat.lt_succ_self _) K']
  have h := (hK K' hKK' z _ hw hwz ((primesBelow (z ^ (1 / s))).card + 1)).1
  have h0 : 0 ≤ ∑ k ∈ Ico K' ((primesBelow (z ^ (1 / s))).card + 1), BP b k z (z ^ (1 / s)) :=
    sum_nonneg (fun k _ => BP_nonneg b k _ _)
  rw [abs_le]; constructor <;> linarith

/-- **C.4 for `S⁻`** (assembly form): for `ε > 0` there is `K` with, for all `K' ≥ K`, all `z`, `s` with
`2 ≤ w := z^{1/s}`, `w² ≤ z`: `|S⁻(z, s) − (V(w) − Σ_{k<K'} B⁻_k(z, w))| ≤ ε V(w)`. -/
theorem Sminus_trunc (b : ℕ) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∀ z s : ℝ, 2 ≤ z ^ (1 / s) → (z ^ (1 / s)) ^ 2 ≤ z →
      |Sminus b z s - (VB b (z ^ (1 / s)) - ∑ k ∈ range K', BM b k z (z ^ (1 / s)))| ≤
        ε * VB b (z ^ (1 / s)) := by
  obtain ⟨K, hK⟩ := tail_small b hb hε
  refine ⟨K, fun K' hKK' z s hw hw2 => ?_⟩
  have hwz : z ^ (1 / s) ≤ z := le_trans (by nlinarith) hw2
  rw [Sminus_eq, sum_range_split_BM b z _ (Nat.lt_succ_self _) K']
  have h := (hK K' hKK' z _ hw hwz ((primesBelow (z ^ (1 / s))).card + 1)).2 hw2
  have h0 : 0 ≤ ∑ k ∈ Ico K' ((primesBelow (z ^ (1 / s))).card + 1), BM b k z (z ^ (1 / s)) :=
    sum_nonneg (fun k _ => BM_nonneg b k _ _)
  rw [abs_le]; constructor <;> linarith

/-- Range facts for `w = z^{1/s}`: `2 ≤ w` if `2^9 ≤ z`, `0 < s ≤ 9`. -/
theorem two_le_rpow_one_div {z s : ℝ} (hz : 2 ^ (9 : ℕ) ≤ z) (hs0 : 0 < s) (hs9 : s ≤ 9) :
    2 ≤ z ^ (1 / s) := by
  have h1 : (2 : ℝ) ^ (9 / s) ≤ z ^ (1 / s) := by
    rw [show (9 / s : ℝ) = (9 : ℝ) * (1 / s) by ring, Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hz) (by positivity)
  have h2 : (2 : ℝ) ≤ 2 ^ (9 / s) := by
    conv_lhs => rw [← Real.rpow_one 2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [le_div_iff₀ hs0]; linarith)
  linarith

/-- `w = z^{1/s} ≤ z` for `1 ≤ z`, `1 ≤ s`. -/
theorem rpow_one_div_le_self {z s : ℝ} (hz : 1 ≤ z) (hs : 1 ≤ s) : z ^ (1 / s) ≤ z := by
  conv_rhs => rw [← Real.rpow_one z]
  exact Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one (by linarith)]; exact hs)

/-- `(z^{1/s})² ≤ z` for `1 ≤ z`, `2 ≤ s`. -/
theorem rpow_one_div_sq_le {z s : ℝ} (hz : 1 ≤ z) (hs : 2 ≤ s) : (z ^ (1 / s)) ^ 2 ≤ z := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  conv_rhs => rw [← Real.rpow_one z]
  exact Real.rpow_le_rpow_of_exponent_le hz (by push_cast; rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hs)

end Palprimes.E1
