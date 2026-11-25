import Omega3.Statements
import Omega3.Items.M11_A
import Omega3.Items.M11_B

/-!
# M11. Greaves' Lemma 12: `|E11(y) − 2e^γ V(y)𝓜(W)| ≤ εV(y)` for `y ≥ y₀`

Proof (`M11_PLAN.md`): `E11 = W(1)T⁻(y, y^{1/2}) − S2 + S3a − S3b` (`M11_Pieces`). `T⁻ = o(V)` (`M11_Tminus`).
Each `S/V` is a prime-tuple sum with weights `σ⁺(y/Π q)/V(y)`, replaced by `2e^γ/u` (`sigma_approx`, error
`≤ ε W(1) Mass^{2k+1}`), whose limits are box integrals (Palprimes `prime_sum_tendsto`), identified in `M11_Int`:
`2e^γ(−I2 + I3 − I4) = 2e^γ 𝓜(W)`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset Real Filter Topology
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT
open Classical

theorem mm_pos : 0 < mm := by unfold mm; norm_num

theorem expv_sigv {r : ℕ} {y : ℝ} (hy : 1 < y) (q : Fin r → ℕ) (hq : ∀ i, (q i).Prime) :
    expv (sigv y q) = xq y q := by
  funext i
  unfold expv sigv sig xq
  apply Real.exp_log
  exact div_pos (Real.log_pos (by exact_mod_cast (hq i).one_lt)) (Real.log_pos hy)

noncomputable def Mass (b : ℕ) (y : ℝ) : ℝ := ∑ p ∈ Pset y aa, gB b p

theorem mass_nonneg (b : ℕ) (y : ℝ) : 0 ≤ Mass b y := Finset.sum_nonneg (fun p _ => gB_nonneg b p)

theorem mass_bound (b : ℕ) (hb : 2 ≤ b) : ∀ᶠ y : ℝ in atTop, Mass b y ≤ -Real.log aa + 1 := by
  have ht := mu1_tendsto b hb aa (Real.log aa) 0 aa_pos le_rfl (Real.log_nonpos aa_pos.le aa_lt_one.le) le_rfl
  have hev := (tendsto_order.1 ht).2 (-Real.log aa + 1) (by linarith)
  filter_upwards [hev, eventually_gt_atTop 1] with y hy hy1
  have e : mu1 b y aa (Real.log aa) 0 = Mass b y := by
    unfold mu1 Mass
    congr 1
    apply Finset.filter_true_of_mem
    intro p hp
    have hpp := (mem_Pset.1 hp).1
    rw [sig_mem_Ioc y hy1 _ _ p hpp.one_lt, Real.exp_log aa_pos, Real.exp_zero, Real.rpow_one]
    constructor
    · have := (mem_Pset.1 hp).2.1
      have h2 : y ^ aa < (⌊y ^ aa⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h3 : (⌊y ^ aa⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast this
      linarith
    · exact le_trans (by exact_mod_cast (mem_Pset.1 hp).2.2) (Nat.floor_le (by linarith))
  rw [← e]; linarith

theorem prod_sum_mass {r : ℕ} (b : ℕ) (y : ℝ) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin r => Pset y aa), ∏ i, gB b (q i) = Mass b y ^ r := by
  unfold Mass
  rw [← Finset.prod_univ_sum (fun _ : Fin r => Pset y aa) (fun _ p => gB b p), Finset.prod_const, card_univ, Fintype.card_fin]

/-! ## The replacement steps -/

theorem rep_S3a (b : ℕ) (hb : 2 ≤ b) (h7 : Lemma7Stmt b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |(∑ p ∈ Pset y aa, gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p))) / VB b y -
      ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y aa), (∏ i, gB b (q i)) * f3 (sigv y q)| ≤ ε * W1 * Mass b y := by
  filter_upwards [sigma_approx b hb h7 mm mm_pos (by unfold mm; norm_num) ε hε, eventually_gt_atTop 1] with y hs hy
  have hl := Real.log_pos hy
  have hV := VB_pos b y
  rw [sum_piFinset_one, Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold Mass
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
  have hpp := (mem_Pset.1 hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  simp only [Fin.prod_univ_one]
  rw [expv_sigv hy _ (fun _ => hpp) |> fun h => show f3 (sigv y (fun _ => p)) = _ from by unfold f3 fR; rw [h]]
  have hx : xq y (fun _ : Fin 1 => p) = fun _ => tp y p := rfl
  rw [hx]
  have hg := gB_nonneg b p
  by_cases ht : tp y p < 1 / 2
  · rw [if_pos ht, if_pos ((cnd3_iff _).2 ht)]
    unfold G3
    have hlY : Real.log (y / p) = (1 - tp y p) * Real.log y := by
      rw [Real.log_div (by linarith) hp0.ne']; unfold tp; field_simp
    have hY1 : y ^ mm ≤ y / p := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < y / p), Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2; rw [hlY]; have : mm = 1 / 85 := rfl; nlinarith
    have hY2 : y / p ≤ y := div_le_self (by linarith) (by exact_mod_cast hpp.one_lt.le)
    have h := hs (y / p) hY1 hY2
    have hq : Real.log y / Real.log (y / p) = 1 / (1 - tp y p) := by rw [hlY]; field_simp
    rw [hq] at h
    have hW0 := Wf_nonneg (tp y p)
    have hWl := Wf_le (tp y p)
    have e : gB b p * (Wf (tp y p) * sigmaP b (y / p)) / VB b y - gB b p * (Wf (tp y p) * EG / (1 - tp y p)) =
        gB b p * Wf (tp y p) * (sigmaP b (y / p) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * (1 / (1 - tp y p))) := by
      unfold EG; field_simp
    rw [e, abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hW0]
    calc gB b p * Wf (tp y p) * |sigmaP b (y / p) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * (1 / (1 - tp y p))|
        ≤ gB b p * W1 * ε := mul_le_mul (mul_le_mul_of_nonneg_left hWl hg) h (abs_nonneg _) (mul_nonneg hg (by unfold W1; norm_num))
      _ = ε * W1 * gB b p := by ring
  · rw [if_neg ht, if_neg (fun h => ht ((cnd3_iff _).1 h))]
    simp only [mul_zero, zero_mul, zero_div, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hε.le (by unfold W1; norm_num)) hg

theorem rep_S2 (b : ℕ) (hb : 2 ≤ b) (h7 : Lemma7Stmt b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |(∑ p ∈ Pset y aa, gB b p * ((if 1 / 2 ≤ tp y p then W1 - Wf (tp y p) else 0) * sigmaP b (y / p))) / VB b y -
      ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y aa), (∏ i, gB b (q i)) * f2 (sigv y q)| ≤ ε * W1 * Mass b y := by
  filter_upwards [sigma_approx b hb h7 mm mm_pos (by unfold mm; norm_num) ε hε, eventually_gt_atTop 1] with y hs hy
  have hl := Real.log_pos hy
  have hV := VB_pos b y
  rw [sum_piFinset_one, Finset.sum_div, ← Finset.sum_sub_distrib]
  unfold Mass
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp => ?_))
  have hpp := (mem_Pset.1 hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  simp only [Fin.prod_univ_one]
  rw [expv_sigv hy _ (fun _ => hpp) |> fun h => show f2 (sigv y (fun _ => p)) = _ from by unfold f2 fR; rw [h]]
  have hx : xq y (fun _ : Fin 1 => p) = fun _ => tp y p := rfl
  rw [hx]
  have hg := gB_nonneg b p
  by_cases ht : 1 / 2 ≤ tp y p
  · rw [if_pos ht, if_pos ((cnd2_iff _).2 ht)]
    unfold G2
    by_cases hU : UU ≤ tp y p
    · rw [Wf_W1_of_ge hU]
      simp only [sub_self, zero_mul, mul_zero, zero_div, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hε.le (by unfold W1; norm_num)) hg
    push Not at hU
    have hlY : Real.log (y / p) = (1 - tp y p) * Real.log y := by
      rw [Real.log_div (by linarith) hp0.ne']; unfold tp; field_simp
    have hY1 : y ^ mm ≤ y / p := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < y / p), Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2; rw [hlY]; have : mm = 1 / 85 := rfl; have : UU = 83 / 85 := rfl; nlinarith
    have hY2 : y / p ≤ y := div_le_self (by linarith) (by exact_mod_cast hpp.one_lt.le)
    have h := hs (y / p) hY1 hY2
    have h1t : 0 < 1 - tp y p := by have : UU = 83 / 85 := rfl; linarith
    have hq : Real.log y / Real.log (y / p) = 1 / (1 - tp y p) := by rw [hlY]; field_simp
    rw [hq] at h
    have hW0 : 0 ≤ W1 - Wf (tp y p) := by linarith [Wf_le (tp y p)]
    have hWl : W1 - Wf (tp y p) ≤ W1 := by linarith [Wf_nonneg (tp y p)]
    have e : gB b p * ((W1 - Wf (tp y p)) * sigmaP b (y / p)) / VB b y - gB b p * ((W1 - Wf (tp y p)) * EG / (1 - tp y p)) =
        gB b p * (W1 - Wf (tp y p)) * (sigmaP b (y / p) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * (1 / (1 - tp y p))) := by
      unfold EG; field_simp
    rw [e, abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hW0]
    calc gB b p * (W1 - Wf (tp y p)) * |sigmaP b (y / p) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * (1 / (1 - tp y p))|
        ≤ gB b p * W1 * ε := mul_le_mul (mul_le_mul_of_nonneg_left hWl hg) h (abs_nonneg _) (mul_nonneg hg (by unfold W1; norm_num))
      _ = ε * W1 * gB b p := by ring
  · rw [if_neg ht, if_neg (fun h => ht ((cnd2_iff _).1 h))]
    simp only [mul_zero, zero_mul, zero_div, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hε.le (by unfold W1; norm_num)) hg

theorem rep_S3b_k (b : ℕ) (hb : 2 ≤ b) (h7 : Lemma7Stmt b) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ y : ℝ in atTop, |(∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q) / VB b y -
      ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)| ≤
        ε * W1 * Mass b y ^ (2 * k + 1) := by
  filter_upwards [sigma_approx b hb h7 mm mm_pos (by unfold mm; norm_num) ε hε, eventually_gt_atTop 1] with y hs hy
  have hl := Real.log_pos hy
  have hV := VB_pos b y
  have hn : 1 ≤ 2 * k := by omega
  rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← prod_sum_mass, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q hq => ?_))
  rw [Fintype.mem_piFinset] at hq
  have hqp : ∀ i, (q i).Prime := fun i => (mem_Pset.1 (hq i)).1
  have hg : 0 ≤ ∏ i, gB b (q i) := Finset.prod_nonneg (fun i _ => gB_nonneg b _)
  unfold Phi3 fA fR
  rw [expv_sigv hy q hqp]
  by_cases hE : ExplA (2 * k) (xq y q)
  · rw [if_pos hE, if_pos ((cndA_iff hn _).2 hE)]
    unfold GA
    set t := xq y q (Fin.last (2 * k))
    by_cases hm : t ≤ mm
    · rw [Wf_zero_of_le hm]
      simp only [zero_mul, mul_zero, zero_div, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg hε.le (by unfold W1; norm_num)) hg
    push Not at hm
    have hu := explA_u hn hE
    set u := 1 - t - ∑ j, Fin.init (xq y q) j with hudef
    have hPq : (0 : ℝ) < ((∏ i, q i : ℕ) : ℝ) := by exact_mod_cast Finset.prod_pos (fun i _ => (hqp i).pos)
    have hsum : ∑ i, xq y q i = t + ∑ j, Fin.init (xq y q) j := by
      rw [Fin.sum_univ_castSucc]; unfold Fin.init; ring
    have hlogP : Real.log ((∏ i, q i : ℕ) : ℝ) = (∑ i, xq y q i) * Real.log y := by
      rw [Nat.cast_prod, Real.log_prod (fun i _ => by exact_mod_cast (hqp i).ne_zero), Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; unfold xq; field_simp
    have hlY : Real.log (y / ((∏ i, q i : ℕ) : ℝ)) = u * Real.log y := by
      rw [Real.log_div (by linarith) hPq.ne', hlogP, hsum, hudef]; ring
    have hY1 : y ^ mm ≤ y / ((∏ i, q i : ℕ) : ℝ) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < y / ((∏ i, q i : ℕ) : ℝ)), Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2; rw [hlY]; nlinarith
    have hY2 : y / ((∏ i, q i : ℕ) : ℝ) ≤ y := div_le_self (by linarith) (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_pos (fun i _ => (hqp i).pos)).ne')
    have h := hs _ hY1 hY2
    have hu0 : 0 < u := by
      have ht : t = xq y q (Fin.last (2 * k)) := rfl
      have := mm_pos; linarith
    have hq' : Real.log y / Real.log (y / ((∏ i, q i : ℕ) : ℝ)) = 1 / u := by rw [hlY]; field_simp
    rw [hq'] at h
    have hW0 := Wf_nonneg t
    have hWl := Wf_le t
    have e : (∏ i, gB b (q i)) * (Wf t * sigmaP b (y / ((∏ i, q i : ℕ) : ℝ))) / VB b y -
        (∏ i, gB b (q i)) * (Wf t * (2 * Real.exp Real.eulerMascheroniConstant) / u) =
        (∏ i, gB b (q i)) * Wf t * (sigmaP b (y / ((∏ i, q i : ℕ) : ℝ)) / VB b y -
          2 * Real.exp Real.eulerMascheroniConstant * (1 / u)) := by
      field_simp
    rw [e, abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hW0]
    calc (∏ i, gB b (q i)) * Wf t * |sigmaP b (y / ((∏ i, q i : ℕ) : ℝ)) / VB b y -
          2 * Real.exp Real.eulerMascheroniConstant * (1 / u)|
        ≤ (∏ i, gB b (q i)) * W1 * ε := mul_le_mul (mul_le_mul_of_nonneg_left hWl hg) h (abs_nonneg _) (mul_nonneg hg (by unfold W1; norm_num))
      _ = ε * W1 * ∏ i, gB b (q i) := by ring
  · rw [if_neg hE, if_neg (fun h => hE ((cndA_iff hn _).1 h))]
    simp only [mul_zero, zero_mul, zero_div, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hε.le (by unfold W1; norm_num)) hg

end Omega3.M11

namespace Omega3

open Palprimes Palprimes.Greaves Palprimes.MT Omega3.M11
open Classical

theorem itemM11 : ItemM11 := by
  intro b hb h7 ε hε
  -- constants
  set Mm : ℝ := max (-Real.log aa + 1) 1 with hMm
  have hMm1 : 1 ≤ Mm := le_max_right _ _
  set K : ℝ := W1 * (2 * Mm + 42 * Mm ^ 85) + W1 with hK
  have hW1 : (0 : ℝ) < W1 := by unfold W1; norm_num
  have hK0 : 0 < K := by rw [hK]; positivity
  set δ : ℝ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  set ε' : ℝ := δ / K with hε'
  have hε'0 : 0 < ε' := by positivity
  -- the limits
  have hl2 := prime_sum_tendsto b hb aa aa_pos aa_lt_one f2 ⟨_, fun σ _ => f2_bound σ⟩ f2_ae
    (integrableOn_box _ _ _ _ f2_measurable _ (fun σ _ => f2_bound σ))
  have hl3 := prime_sum_tendsto b hb aa aa_pos aa_lt_one f3 ⟨_, fun σ _ => f3_bound σ⟩ f3_ae
    (integrableOn_box _ _ _ _ f3_measurable _ (fun σ _ => f3_bound σ))
  have hl4 : Tendsto (fun y => ∑ k ∈ Icc 1 42, ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa),
      (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)) atTop
      (𝓝 (∑ k ∈ Icc 1 42, ∫ σ in (BoxIntegral.Box.toSet (boxA (2 * k + 1) aa aa_pos aa_lt_one) : Set (Fin (2 * k + 1) → ℝ)), fA (2 * k) σ)) := by
    apply tendsto_finsetSum
    intro k hk
    rw [mem_Icc] at hk
    exact prime_sum_tendsto b hb aa aa_pos aa_lt_one (fA (2 * k)) ⟨_, fun σ _ => fA_bound (by omega) σ⟩
      (fA_ae (by omega)) (fA_integrableOn (by omega))
  rw [f2_box.1] at hl2
  rw [f3_box.1] at hl3
  rw [chain_box.1] at hl4
  have hev2 := (Metric.tendsto_nhds.1 hl2) δ hδ0
  have hev3 := (Metric.tendsto_nhds.1 hl3) δ hδ0
  have hev4 := (Metric.tendsto_nhds.1 hl4) δ hδ0
  obtain ⟨yT, hyT⟩ := Omega3.M11R.Tminus_small b hb (δ / W1) (by positivity)
  have hevk : ∀ᶠ y : ℝ in atTop, ∀ k ∈ Icc 1 42,
      |(∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q) / VB b y -
        ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)| ≤
          ε' * W1 * Mass b y ^ (2 * k + 1) := by
    rw [Filter.eventually_all_finset]
    intro k hk; rw [mem_Icc] at hk
    exact rep_S3b_k b hb h7 ε' hε'0 k hk.1
  have hall := (hev2.and hev3).and (hev4.and (hevk.and ((rep_S2 b hb h7 ε' hε'0).and ((rep_S3a b hb h7 ε' hε'0).and
    ((mass_bound b hb).and ((eventually_ge_atTop yT).and (eventually_gt_atTop (1 : ℝ))))))))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hall
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨⟨h2, h3⟩, h4, hk, hr2, hr3, hm, hyT', hy1⟩ := hy₀ y hy
  rw [Real.dist_eq] at h2 h3 h4
  have hV := VB_pos b y
  have hmass : Mass b y ≤ Mm := le_trans hm (le_max_left _ _)
  have hmass0 := mass_nonneg b y
  -- decomposition
  rw [E11_split' b y, S2_eq b hy1, S3a_eq b hy1, S3b_eq b hy1]
  set A0 := Tpm b false y (y ^ ((1 : ℝ) / 2))
  set A2 := ∑ p ∈ Pset y aa, gB b p * ((if 1 / 2 ≤ tp y p then W1 - Wf (tp y p) else 0) * sigmaP b (y / p))
  set A3 := ∑ p ∈ Pset y aa, gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p))
  set A4 := ∑ k ∈ Icc 1 42, ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q
  set B2 := ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y aa), (∏ i, gB b (q i)) * f2 (sigv y q)
  set B3 := ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y aa), (∏ i, gB b (q i)) * f3 (sigv y q)
  set B4 := ∑ k ∈ Icc 1 42, ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa),
      (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)
  have hT := hyT y hyT'
  -- the chain error
  have hk4 : |A4 / VB b y - B4| ≤ ε' * W1 * (42 * Mm ^ 85) := by
    have e : A4 / VB b y - B4 = ∑ k ∈ Icc 1 42,
        ((∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q) / VB b y -
          ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_div]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Icc 1 42, |(∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q) / VB b y -
          ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), (∏ i, gB b (q i)) * fA (2 * k) (sigv y q)|
        ≤ ∑ k ∈ Icc 1 42, ε' * W1 * Mm ^ 85 := by
          apply Finset.sum_le_sum; intro k hk'
          refine (hk k hk').trans ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [mem_Icc] at hk'
          calc Mass b y ^ (2 * k + 1) ≤ Mm ^ (2 * k + 1) := pow_le_pow_left₀ hmass0 hmass _
            _ ≤ Mm ^ 85 := pow_le_pow_right₀ hMm1 (by omega)
      _ = ε' * W1 * (42 * Mm ^ 85) := by rw [Finset.sum_const]; simp; ring
  have hr2' : |A2 / VB b y - B2| ≤ ε' * W1 * Mm := hr2.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hr3' : |A3 / VB b y - B3| ≤ ε' * W1 * Mm := hr3.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hsumε : ε' * W1 * (42 * Mm ^ 85) + ε' * W1 * Mm + ε' * W1 * Mm ≤ δ := by
    have : ε' * K = δ := by rw [hε']; field_simp
    have hKe : ε' * W1 * (42 * Mm ^ 85) + ε' * W1 * Mm + ε' * W1 * Mm ≤ ε' * K := by
      rw [hK]; nlinarith [hε'0, hW1]
    linarith
  have hT' : |W1 * A0 / VB b y| ≤ δ := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV, abs_mul, abs_of_pos hW1]
    have := mul_le_mul_of_nonneg_left hT hW1.le
    calc W1 * |A0| ≤ W1 * (δ / W1 * VB b y) := this
      _ = δ * VB b y := by field_simp
  have hmv := mvalW_eq
  -- combine
  have key : (W1 * A0 - A2 + A3 - A4) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * mvalW =
      W1 * A0 / VB b y - (A2 / VB b y - B2) - (B2 - EG * I2) + (A3 / VB b y - B3) + (B3 - EG * I3) -
        (A4 / VB b y - B4) - (B4 - EG * I4) := by
    rw [hmv]; unfold EG; field_simp; ring
  have hfin : |(W1 * A0 - A2 + A3 - A4) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * mvalW| ≤ 8 * δ := by
    rw [key]
    have a1 := abs_sub_le_iff.1 hr2'
    have a2 := abs_sub_lt_iff.1 h2
    have a3 := abs_sub_le_iff.1 hr3'
    have a4 := abs_sub_lt_iff.1 h3
    have a5 := abs_sub_le_iff.1 hk4
    have a6 := abs_sub_lt_iff.1 h4
    have a7 := abs_le.1 hT'
    rw [abs_le]; constructor <;> linarith
  have e2 : |W1 * A0 - A2 + A3 - A4 - 2 * Real.exp Real.eulerMascheroniConstant * VB b y * mvalW| =
      VB b y * |(W1 * A0 - A2 + A3 - A4) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * mvalW| := by
    rw [← abs_of_pos hV, ← abs_mul, abs_of_pos hV]
    congr 1; field_simp
  rw [e2]
  calc VB b y * |(W1 * A0 - A2 + A3 - A4) / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * mvalW|
      ≤ VB b y * (8 * δ) := mul_le_mul_of_nonneg_left hfin hV.le
    _ = ε * VB b y := by rw [hδ]; ring

end Omega3
