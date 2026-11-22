import Palprimes.MainTerm.Mval

/-! # `𝓜(P*) > 0` -/

set_option linter.style.longLine false

open MeasureTheory Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

/-! ## Measurability of `hk k` in `x` -/

lemma measurable_chainX₂ {α : Type*} [MeasurableSpace α] {L : ℕ} {g : α → ℝ} {f : α → Fin L → ℝ}
    (hg : Measurable g) (hf : ∀ i, Measurable fun a => f a i) (k : ℕ) :
    Measurable fun a => chainX (g a) (f a) k := by
  unfold chainX
  by_cases h : k < L
  · simp only [h, dite_true]; exact hf _
  · simp only [h, dite_false]; exact hg

lemma measurable_condX₂ {α : Type*} [MeasurableSpace α] {L : ℕ} {g : α → ℝ} {f : α → Fin L → ℝ}
    (hg : Measurable g) (hf : ∀ i, Measurable fun a => f a i) (j : ℕ) :
    Measurable fun a => (∑ i ∈ Finset.range (2 * j - 1), chainX (g a) (f a) i) + 3 * chainX (g a) (f a) (2 * j - 1) := by
  have h1 : Measurable fun a => ∑ i ∈ Finset.range (2 * j - 1), chainX (g a) (f a) i :=
    Finset.measurable_sum _ fun i _ => measurable_chainX₂ hg hf i
  exact h1.add ((measurable_chainX₂ hg hf _).const_mul 3)

lemma measurable_hRegion₂ {α : Type*} [MeasurableSpace α] {k : ℕ} {g : α → ℝ} {f : α → Fin (2 * k) → ℝ}
    (hg : Measurable g) (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => HRegion k (g a) (f a) := by
  unfold HRegion
  refine (measurable_strictAnti_comp hf).and ((Measurable.forall fun i => measurable_lt_fun hg (hf i)).and
    ((Measurable.forall fun i => measurable_lt_fun (hf i) measurable_const).and
    ((Measurable.forall fun j => measurable_const.imp (measurable_const.imp
      (measurable_le_fun (measurable_condX₂ hg hf j) measurable_const))).and
    ((measurable_lt_fun measurable_const (measurable_condX₂ hg hf k)).and ?_))))
  have h1 : Measurable fun a => ∑ i, f a i := Finset.measurable_sum _ fun i _ => hf i
  exact measurable_lt_fun (measurable_chainX₂ hg hf _) ((measurable_const.sub hg).sub h1)

theorem measurable_hk (k : ℕ) : Measurable (hk k) := by
  classical
  have hF : Measurable (Function.uncurry fun (x : ℝ) (v : Fin (2 * k) → ℝ) =>
      if HRegion k x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) := by
    refine Measurable.ite (measurableSet_setOfPred.mpr (measurable_hRegion₂ (k := k) (g := fun p : ℝ × (Fin (2 * k) → ℝ) => p.1)
      (f := fun p => p.2) measurable_fst fun i => (measurable_pi_apply i).comp measurable_snd)) ?_ measurable_const
    have hp : Measurable fun p : ℝ × (Fin (2 * k) → ℝ) => ∏ i, p.2 i :=
      Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).comp measurable_snd
    have hs : Measurable fun p : ℝ × (Fin (2 * k) → ℝ) => ∑ i, p.2 i :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_snd
    exact measurable_const.div (hp.mul ((measurable_const.sub measurable_fst).sub hs))
  have := (StronglyMeasurable.integral_prod_right (ν := (volume : Measure (Fin (2 * k) → ℝ))) hF.stronglyMeasurable).measurable
  convert this using 1
  funext x; unfold hk; rfl

/-! ## Nonnegativity and a crude bound -/

lemma hk_integrand_nonneg {k : ℕ} {x : ℝ} (hx : 0 < x) (v : Fin (2 * k) → ℝ) :
    0 ≤ (open Classical in if HRegion k x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) := by
  split_ifs with h
  · have hl := hRegion_zvec_gt h (Fin.last _)
    simp only [zvec_last] at hl
    have : 0 < ∏ i, v i := Finset.prod_pos fun i _ => lt_trans hx (h.2.1 i)
    have : 0 < 1 - x - ∑ i, v i := by linarith
    positivity
  · exact le_rfl

theorem hk_nonneg (k : ℕ) {x : ℝ} (hx : 0 < x) : 0 ≤ hk k x := by
  unfold hk
  exact integral_nonneg fun v => hk_integrand_nonneg hx v

theorem hk_le_pow (k : ℕ) {x : ℝ} (hx : 0 < x) : hk k x ≤ 1 / x ^ (2 * k + 1) := by
  classical
  set S : Set (Fin (2 * k) → ℝ) := Set.univ.pi fun _ => Set.Ioo 0 1 with hS
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hvol : volume S = 1 := by rw [hS, Real.volume_pi_Ioo]; simp
  have hbound : ∀ v : Fin (2 * k) → ℝ,
      (if HRegion k x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0) ≤ S.indicator (fun _ => 1 / x ^ (2 * k + 1)) v := by
    intro v
    split_ifs with h
    · have hl := hRegion_zvec_gt h (Fin.last _)
      simp only [zvec_last] at hl
      have hvS : v ∈ S := fun i _ => ⟨lt_trans hx (h.2.1 i), h.2.2.1 i⟩
      rw [Set.indicator_of_mem hvS]
      have hp : x ^ (2 * k) ≤ ∏ i, v i := by
        have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => x) (g := v)
          (h0 := fun i _ => hx.le) (h1 := fun i _ => (h.2.1 i).le)
        simpa using this
      have : x ^ (2 * k + 1) ≤ (∏ i, v i) * (1 - x - ∑ i, v i) := by
        rw [pow_succ]; exact mul_le_mul hp hl.le hx.le (le_trans (by positivity) hp)
      exact one_div_le_one_div_of_le (by positivity) this
    · exact Set.indicator_nonneg (fun _ _ => by positivity) v
  have hint : Integrable (S.indicator (fun _ : Fin (2 * k) → ℝ => 1 / x ^ (2 * k + 1))) := by
    rw [integrable_indicator_iff hSm]
    exact integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)
  unfold hk
  calc (∫ v : Fin (2 * k) → ℝ, if HRegion k x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0)
      ≤ ∫ v, S.indicator (fun _ => 1 / x ^ (2 * k + 1)) v :=
        integral_mono_of_nonneg (ae_of_all _ fun v => hk_integrand_nonneg hx v) hint (ae_of_all _ hbound)
    _ = 1 / x ^ (2 * k + 1) := by
        rw [integral_indicator_const _ hSm, Measure.real, hvol]; simp

/-! ## Upper Riemann sums on a uniform grid -/

theorem integral_le_cells {f : ℝ → ℝ} {lo hi : ℝ} {n : ℕ} (hn : 0 < n) (hlh : lo ≤ hi)
    (hf : IntervalIntegrable f volume lo hi) (M : ℕ → ℝ)
    (hM : ∀ k < n, ∀ t ∈ Set.Icc (lo + (hi - lo) * k / n) (lo + (hi - lo) * (k + 1) / n), f t ≤ M k) :
    ∫ t in lo..hi, f t ≤ ∑ k ∈ range n, (hi - lo) / n * M k := by
  set g : ℕ → ℝ := fun k => lo + (hi - lo) * k / n with hg
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : g 0 = lo := by simp [hg]
  have hgn : g n = hi := by simp only [hg]; field_simp; ring
  have hmono : ∀ k, g k ≤ g (k + 1) := by
    intro k; simp only [hg]; push_cast
    have : (hi - lo) * k / n ≤ (hi - lo) * (k + 1) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hnr.le
    linarith
  have hsub : ∀ k < n, Set.uIcc (g k) (g (k + 1)) ⊆ Set.uIcc lo hi := by
    intro k hk
    rw [Set.uIcc_of_le (hmono k), Set.uIcc_of_le hlh]
    apply Set.Icc_subset_Icc
    · simp only [hg]
      have : 0 ≤ (hi - lo) * k / n := div_nonneg (mul_nonneg (by linarith) (by positivity)) hnr.le
      linarith
    · simp only [hg]
      have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
      have : (hi - lo) * ((k + 1 : ℕ) : ℝ) / n ≤ hi - lo := by
        rw [div_le_iff₀ hnr]; push_cast; nlinarith
      linarith
  have hint : ∀ k < n, IntervalIntegrable f volume (g k) (g (k + 1)) := fun k hk => hf.mono_set (hsub k hk)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hg0, hgn] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  calc ∫ t in g k..g (k + 1), f t ≤ ∫ t in g k..g (k + 1), M k :=
        intervalIntegral.integral_mono_on (hmono k) (hint k hk') intervalIntegrable_const (fun t ht => by
          apply hM k hk' t
          simpa [hg] using ht)
    _ = (hi - lo) / n * M k := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        congr 1
        simp only [hg]; push_cast; field_simp; ring

/-- Bounded measurable functions are interval integrable. -/
theorem ii_of_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hf : Measurable f)
    (hC : ∀ t ∈ Set.Icc a b, |f t| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]; exact hC t (Set.Ioc_subset_Icc_self ht)))

/-! ## An upper bound for `h_2(x, 1)` on a cell `x₀ ≤ x ≤ x₁` -/

lemma H2_nonneg {x : ℝ} (hx : 0 < x) (a b : ℝ) : 0 ≤ H2 x a b := by
  unfold H2
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    have : 0 < a := by linarith
    have : 0 < b := by linarith
    have : 0 < 1 - x - (a + b) := by linarith
    positivity
  · exact le_rfl

/-- `K(x₁, a) = 9 / (a (1 − a) (2 − 3x₁ − 2a))`. -/
noncomputable def Kc (x1 a : ℝ) : ℝ := 9 / (a * (1 - a) * (2 - 3 * x1 - 2 * a))

lemma H2_le_ind {x0 x1 x : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x) (hx1 : x ≤ x1) (h21 : x1 < 2 * x0) (a b : ℝ) :
    H2 x a b ≤ (Set.Ioo ((1 - a) / 3) (min a ((1 - x0 - a) / 2))).indicator (fun _ => Kc x1 a) b := by
  unfold H2
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    have hb : b ∈ Set.Ioo ((1 - a) / 3) (min a ((1 - x0 - a) / 2)) := ⟨by linarith, lt_min h1 (by linarith)⟩
    rw [Set.indicator_of_mem hb]
    have ha : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hu : 0 < 1 - x - (a + b) := by linarith
    have hd : 0 < 2 - 3 * x1 - 2 * a := by linarith
    have h1a : 0 < 1 - a := by linarith
    unfold Kc
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : 0 ≤ (b - (1 - a) / 3) * ((1 - x - a) - b - (1 - a) / 3) :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ (1 - a) * (x1 - x) := mul_nonneg h1a.le (by linarith)
    nlinarith [mul_nonneg ha.le e1, mul_nonneg ha.le e2]
  · refine Set.indicator_nonneg (fun b hb => ?_) b
    obtain ⟨hb1, hb2⟩ := hb
    have hb3 := lt_of_lt_of_le hb2 (min_le_left _ _)
    have hb4 := lt_of_lt_of_le hb2 (min_le_right _ _)
    have ha : 0 < a := by linarith
    have h1a : 0 < 1 - a := by linarith
    have hd : 0 < 2 - 3 * x1 - 2 * a := by linarith
    unfold Kc; positivity

/-- The bound for the inner integral, uniform for `x₀ ≤ x ≤ x₁`. -/
noncomputable def Phi (x0 x1 a : ℝ) : ℝ := max (min a ((1 - x0 - a) / 2) - (1 - a) / 3) 0 * Kc x1 a

lemma inner_le_Phi {x0 x1 x : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x) (hx1 : x ≤ x1) (h21 : x1 < 2 * x0) (a : ℝ) :
    ∫ b, H2 x a b ≤ Phi x0 x1 a := by
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  have hint : Integrable ((Set.Ioo ((1 - a) / 3) (min a ((1 - x0 - a) / 2))).indicator (fun _ : ℝ => Kc x1 a)) := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const measure_Ioo_lt_top.ne
  calc ∫ b, H2 x a b ≤ ∫ b, (Set.Ioo ((1 - a) / 3) (min a ((1 - x0 - a) / 2))).indicator (fun _ => Kc x1 a) b :=
        integral_mono_of_nonneg (ae_of_all _ fun b => H2_nonneg hxpos a b) hint
          (ae_of_all _ fun b => H2_le_ind hx0 hx hx1 h21 a b)
    _ = Phi x0 x1 a := by
        rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo, smul_eq_mul]
        rfl

lemma Phi_eq_zero {x0 x1 a : ℝ} (h : a ∉ Set.Ioc (1 / 4) (1 - 3 * x0)) : Phi x0 x1 a = 0 := by
  unfold Phi
  have : min a ((1 - x0 - a) / 2) - (1 - a) / 3 ≤ 0 := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
    rcases h with h | h
    · have := min_le_left a ((1 - x0 - a) / 2); linarith
    · have := min_le_right a ((1 - x0 - a) / 2); linarith
  rw [max_eq_right this, zero_mul]

lemma continuousOn_Phi {x0 x1 : ℝ} (hx0 : 0 < x0) (h21 : x1 < 2 * x0) :
    ContinuousOn (Phi x0 x1) (Set.Icc (1 / 4) (1 - 3 * x0)) := by
  have hc1 : Continuous fun a : ℝ => max (min a ((1 - x0 - a) / 2) - (1 - a) / 3) 0 := by fun_prop
  have hc3 : Continuous fun a : ℝ => a * (1 - a) * (2 - 3 * x1 - 2 * a) := by fun_prop
  have hc2 : ContinuousOn (fun a : ℝ => 9 / (a * (1 - a) * (2 - 3 * x1 - 2 * a))) (Set.Icc (1 / 4) (1 - 3 * x0)) := by
    refine continuousOn_const.div hc3.continuousOn ?_
    intro a ⟨ha1, ha2⟩
    have p1 : 0 < a := by linarith
    have p2 : 0 < 1 - a := by linarith
    have p3 : 0 < 2 - 3 * x1 - 2 * a := by linarith
    exact (mul_pos (mul_pos p1 p2) p3).ne'
  exact hc1.continuousOn.mul hc2

lemma integral_Phi {x0 x1 : ℝ} (hx0 : 0 < x0) (hx4 : x0 ≤ 1 / 4) (h21 : x1 < 2 * x0) :
    Integrable (Phi x0 x1) ∧ ∫ a, Phi x0 x1 a = ∫ a in (1 / 4)..(1 - 3 * x0), Phi x0 x1 a := by
  have hle : (1 / 4 : ℝ) ≤ 1 - 3 * x0 := by linarith
  have hon : IntegrableOn (Phi x0 x1) (Set.Ioc (1 / 4) (1 - 3 * x0)) :=
    ((continuousOn_Phi hx0 h21).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hsupp : Function.support (Phi x0 x1) ⊆ Set.Ioc (1 / 4) (1 - 3 * x0) := by
    intro a ha
    by_contra hc
    exact ha (Phi_eq_zero hc)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsupp).mp hon, ?_⟩
  rw [intervalIntegral.integral_of_le hle, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro a ha; exact Phi_eq_zero ha

theorem hk1_le_intPhi {x0 x1 x : ℝ} (hx0 : 0 < x0) (hx4 : x0 ≤ 1 / 4) (hx : x0 ≤ x) (hx1 : x ≤ x1)
    (h21 : x1 < 2 * x0) : hk 1 x ≤ ∫ a in (1 / 4)..(1 - 3 * x0), Phi x0 x1 a := by
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  obtain ⟨hI, hE⟩ := integral_Phi (x1 := x1) hx0 hx4 h21
  rw [hk1_eq_iter hxpos, ← hE]
  exact integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun b => H2_nonneg hxpos a b) hI
    (ae_of_all _ fun a => inner_le_Phi hx0 hx hx1 h21 a)

/-- Cell bound for `Phi` on `a₀ ≤ a ≤ a₁`. -/
noncomputable def Mc (x0 x1 a0 a1 : ℝ) : ℝ :=
  max (min ((4 * a1 - 1) / 3) ((1 - 3 * x0 - a0) / 6)) 0 *
    (9 / (min (a0 * (1 - a0)) (a1 * (1 - a1)) * (2 - 3 * x1 - 2 * a1)))

lemma Phi_le_Mc {x0 x1 a0 a1 a : ℝ} (hx0 : 0 < x0) (h21 : x1 < 2 * x0) (ha0 : 1 / 4 ≤ a0) (h0 : a0 ≤ a)
    (h1 : a ≤ a1) (ha1 : a1 ≤ 1 - 3 * x0) : Phi x0 x1 a ≤ Mc x0 x1 a0 a1 := by
  unfold Phi Mc Kc
  have hm1 : max (min a ((1 - x0 - a) / 2) - (1 - a) / 3) 0 ≤ max (min ((4 * a1 - 1) / 3) ((1 - 3 * x0 - a0) / 6)) 0 := by
    apply max_le_max _ le_rfl
    apply le_min
    · have := min_le_left a ((1 - x0 - a) / 2); linarith
    · have := min_le_right a ((1 - x0 - a) / 2); linarith
  have hpos_a : 0 < a := by linarith
  have hpos_1a : 0 < 1 - a := by linarith
  have hd1 : 0 < 2 - 3 * x1 - 2 * a1 := by linarith
  have hmin_pos : 0 < min (a0 * (1 - a0)) (a1 * (1 - a1)) :=
    lt_min (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
  have hmin_le : min (a0 * (1 - a0)) (a1 * (1 - a1)) ≤ a * (1 - a) := by
    by_cases hc : a + a0 ≤ 1
    · have := min_le_left (a0 * (1 - a0)) (a1 * (1 - a1))
      nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr hc)]
    · have := min_le_right (a0 * (1 - a0)) (a1 * (1 - a1))
      push Not at hc
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show (0 : ℝ) ≤ a + a1 - 1 by linarith)]
  have hK : 9 / (a * (1 - a) * (2 - 3 * x1 - 2 * a)) ≤
      9 / (min (a0 * (1 - a0)) (a1 * (1 - a1)) * (2 - 3 * x1 - 2 * a1)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hmin_pos hd1)
    exact mul_le_mul hmin_le (by linarith) hd1.le (mul_pos hpos_a hpos_1a).le
  have hd : 0 < 2 - 3 * x1 - 2 * a := by linarith
  exact mul_le_mul hm1 hK (div_nonneg (by norm_num) (mul_pos (mul_pos hpos_a hpos_1a) hd).le) (le_max_right _ _)

/-- The bound `Hb` for `h_2` on a cell. -/
noncomputable def Hb (x0 x1 : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (1 - 3 * x0 - 1 / 4) / n *
    Mc x0 x1 (1 / 4 + (1 - 3 * x0 - 1 / 4) * k / n) (1 / 4 + (1 - 3 * x0 - 1 / 4) * (k + 1) / n)

theorem hk1_le_Hb {x0 x1 x : ℝ} {n : ℕ} (hn : 0 < n) (hx0 : 0 < x0) (hx4 : x0 ≤ 1 / 4) (hx : x0 ≤ x)
    (hx1 : x ≤ x1) (h21 : x1 < 2 * x0) : hk 1 x ≤ Hb x0 x1 n := by
  have hle : (1 / 4 : ℝ) ≤ 1 - 3 * x0 := by linarith
  refine le_trans (hk1_le_intPhi hx0 hx4 hx hx1 h21) ?_
  have hii : IntervalIntegrable (Phi x0 x1) volume (1 / 4) (1 - 3 * x0) :=
    ((continuousOn_Phi hx0 h21).mono (by rw [Set.uIcc_of_le hle])).intervalIntegrable
  refine integral_le_cells hn hle hii _ fun k hk t ht => ?_
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
  apply Phi_le_Mc hx0 h21 _ ht.1 ht.2
  · have : (1 - 3 * x0 - 1 / 4) * (k + 1) / n ≤ 1 - 3 * x0 - 1 / 4 := by
      rw [div_le_iff₀ hnr]; nlinarith
    linarith
  · have : 0 ≤ (1 - 3 * x0 - 1 / 4) * k / n := div_nonneg (mul_nonneg (by linarith) (by positivity)) hnr.le
    linarith

/-! ## The parameters `P*` -/

lemma PU : Pstar.U = 2499 / 2608 := rfl
lemma PV : Pstar.V = 1 / 652 := rfl
lemma PT0 : Pstar.T0 = 1 / 8 := rfl
lemma Pc : Pstar.c = 109 / 7824 := by unfold WPar.c; rw [PU]; norm_num

lemma W_lo {t : ℝ} (h1 : 1 / 8 < t) (h2 : t ≤ 1 / 4) : Pstar.W t = t - 109 / 7824 := by
  unfold WPar.W
  rw [if_neg (by rw [PU]; linarith), if_neg (by linarith), if_pos (by rw [PT0]; linarith), Pc]

lemma W_mid {t : ℝ} (h1 : 1 / 4 < t) (h2 : t ≤ 2499 / 2608) : Pstar.W t = t - 1 / 652 := by
  unfold WPar.W
  rw [if_neg (by rw [PU]; linarith), if_pos h1, PV]

lemma W_le_lin {t : ℝ} (h1 : 1 / 8 ≤ t) (h2 : t ≤ 1 / 4) : Pstar.W t ≤ t - 109 / 7824 := by
  rcases h1.lt_or_eq with h | h
  · exact (W_lo h h2).le
  · unfold WPar.W
    rw [if_neg (by rw [PU]; linarith), if_neg (by linarith), if_neg (by rw [PT0]; linarith)]
    linarith

lemma W_le_one (t : ℝ) : Pstar.W t ≤ 1 := by
  have := Pstar.W_le t; rw [PU, PV] at this; linarith

lemma measurable_W (P : WPar) : Measurable P.W := by
  unfold WPar.W
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) (measurable_id.sub measurable_const)
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) (measurable_id.sub measurable_const)
        measurable_const))

/-! ## The three pieces of the second integral -/

/-- `W(t) / ((1 − t) t)`. -/
noncomputable def g1 (t : ℝ) : ℝ := Pstar.W t / ((1 - t) * t)

/-- `W(t) h_{2k}(t) / t`. -/
noncomputable def g2 (k : ℕ) (t : ℝ) : ℝ := Pstar.W t * hk k t / t

lemma ii_g1 {a b : ℝ} (ha : 1 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) : IntervalIntegrable g1 volume a b := by
  refine ii_of_bound (C := 16) hab ((measurable_W _).div ((measurable_const.sub measurable_id).mul measurable_id)) ?_
  intro t ⟨h1, h2⟩
  have hW0 := Pstar.W_nonneg t
  have hW1 := W_le_one t
  have hd : 1 / 16 ≤ (1 - t) * t := by nlinarith
  unfold g1
  rw [abs_of_nonneg (div_nonneg hW0 (by linarith)), div_le_iff₀ (by linarith)]
  nlinarith

lemma g2_bound (k : ℕ) {t : ℝ} (h1 : 1 / 8 ≤ t) : |g2 k t| ≤ 8 ^ (2 * k + 2) := by
  have ht0 : 0 < t := by linarith
  have hW0 := Pstar.W_nonneg t
  have hW1 := W_le_one t
  have hh0 := hk_nonneg k ht0
  have hh1 := hk_le_pow k ht0
  have hinv : t⁻¹ ≤ 8 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hp : 1 / t ^ (2 * k + 1) ≤ 8 ^ (2 * k + 1) := by
    rw [one_div, ← inv_pow]; exact pow_le_pow_left₀ (by positivity) hinv _
  unfold g2
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hW0 hh0) ht0.le), div_eq_mul_inv]
  calc Pstar.W t * hk k t * t⁻¹ ≤ 1 * 8 ^ (2 * k + 1) * 8 := by
        apply mul_le_mul (mul_le_mul hW1 (hh1.trans hp) hh0 (by norm_num)) hinv (by positivity) (by positivity)
    _ = 8 ^ (2 * k + 2) := by ring

lemma ii_g2 (k : ℕ) {a b : ℝ} (ha : 1 / 8 ≤ a) (hab : a ≤ b) : IntervalIntegrable (g2 k) volume a b :=
  ii_of_bound hab (((measurable_W _).mul (measurable_hk k)).div measurable_id)
    fun _t ht => g2_bound k (le_trans ha ht.1)

theorem second_split :
    ∫ t in (1 / 8 : ℝ)..(1 / 2), Pstar.W t * (1 / (1 - t) - hk 1 t - hk 2 t) / t =
      (∫ t in (1 / 8 : ℝ)..(1 / 2), g1 t) - (∫ t in (1 / 8 : ℝ)..(1 / 2), g2 1 t) - ∫ t in (1 / 8 : ℝ)..(1 / 2), g2 2 t := by
  have h1 := ii_g1 (a := 1 / 8) (b := 1 / 2) le_rfl (by norm_num) le_rfl
  have h2 := ii_g2 1 (a := 1 / 8) (b := 1 / 2) le_rfl (by norm_num)
  have h3 := ii_g2 2 (a := 1 / 8) (b := 1 / 2) le_rfl (by norm_num)
  rw [← intervalIntegral.integral_sub h1 h2, ← intervalIntegral.integral_sub (h1.sub h2) h3]
  congr 1; funext t
  simp only [g1, g2, div_eq_mul_inv, mul_inv]
  ring

/-! ## Closed forms for the `W`-integrals -/

/-- Antiderivative of `(t − d)/((1 − t) t)`. -/
noncomputable def Fd (d t : ℝ) : ℝ := -d * Real.log t - (1 - d) * Real.log (1 - t)

theorem integral_lin (d : ℝ) {lo hi : ℝ} (h0 : 0 < lo) (hlh : lo ≤ hi) (h1 : hi < 1) :
    ∫ t in lo..hi, (t - d) / ((1 - t) * t) = Fd d hi - Fd d lo := by
  have hderiv : ∀ t ∈ Set.uIcc lo hi, HasDerivAt (Fd d) ((t - d) / ((1 - t) * t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hlh] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have ht0 : 0 < t := by linarith
    have ht1' : 0 < 1 - t := by linarith
    have hA := (Real.hasDerivAt_log ht0.ne').const_mul (-d)
    have hB := (((hasDerivAt_id t).const_sub 1).log ht1'.ne').const_mul (1 - d)
    have hF : Fd d = (fun y => -d * Real.log y) - fun y => (1 - d) * Real.log (1 - id y) := by
      funext y; simp only [Fd, Pi.sub_apply, id]
    rw [hF]
    refine (hA.sub hB).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hlh]
  have hc1 : Continuous fun t : ℝ => t - d := by fun_prop
  have hc2 : Continuous fun t : ℝ => (1 - t) * t := by fun_prop
  refine hc1.continuousOn.div hc2.continuousOn ?_
  intro t ⟨ht1, ht2⟩
  have p1 : 0 < t := by linarith
  have p2 : 0 < 1 - t := by linarith
  exact (mul_pos p2 p1).ne'

theorem G1_eq : ∫ t in (1 / 8 : ℝ)..(1 / 2), g1 t =
    (Fd (109 / 7824) (1 / 4) - Fd (109 / 7824) (1 / 8)) + (Fd (1 / 652) (1 / 2) - Fd (1 / 652) (1 / 4)) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 4) (ii_g1 le_rfl (by norm_num) (by norm_num))
    (ii_g1 (by norm_num) (by norm_num) le_rfl)]
  congr 1
  · rw [← integral_lin _ (by norm_num) (by norm_num) (by norm_num)]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at ht
    simp only [g1, W_lo ht.1 ht.2]
  · rw [← integral_lin _ (by norm_num) (by norm_num) (by norm_num)]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at ht
    simp only [g1, W_mid ht.1 (by linarith [ht.2])]

theorem A1_eq : ∫ t in (1 / 2 : ℝ)..Pstar.U, (Pstar.W t - (Pstar.U - Pstar.V)) / ((1 - t) * t) =
    Fd (2499 / 2608) (2499 / 2608) - Fd (2499 / 2608) (1 / 2) := by
  rw [PU, ← integral_lin _ (by norm_num) (by norm_num) (by norm_num)]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [Set.uIoc_of_le (by norm_num)] at ht
  simp only [W_mid (by linarith [ht.1]) ht.2, PV]
  ring_nf

/-! ## Logarithm bounds and the value of the `W`-integrals -/

lemma log_one_sub_bounds {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (n : ℕ) :
    -(∑ i ∈ range n, y ^ (i + 1) / (i + 1)) - y ^ (n + 1) / (1 - y) ≤ Real.log (1 - y) ∧
      Real.log (1 - y) ≤ -(∑ i ∈ range n, y ^ (i + 1) / (i + 1)) + y ^ (n + 1) / (1 - y) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |y| < 1 by rwa [abs_of_nonneg h0]) n
  rw [abs_of_nonneg h0] at h
  have := abs_le.mp h
  constructor <;> linarith [this.1, this.2]

theorem A12_ge : (2655 / 100000 : ℝ) ≤ (Fd (2499 / 2608) (2499 / 2608) - Fd (2499 / 2608) (1 / 2)) +
    ((Fd (109 / 7824) (1 / 4) - Fd (109 / 7824) (1 / 8)) + (Fd (1 / 652) (1 / 2) - Fd (1 / 652) (1 / 4))) := by
  have e1 : Real.log (2499 / 2608 : ℝ) = Real.log (1 - 109 / 2608) := by norm_num
  have e2 : Real.log (1 - 2499 / 2608 : ℝ) = -5 * Real.log 2 - Real.log (1 - 55 / 218) := by
    rw [show (1 : ℝ) - 2499 / 2608 = (2 ^ 5)⁻¹ * (1 - 55 / 218)⁻¹ by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast; ring
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have e3' : Real.log (1 - 1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  have e4 : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
  have e5 : Real.log (1 / 8 : ℝ) = -3 * Real.log 2 := by
    rw [show (1 / 8 : ℝ) = (2 ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
  simp only [Fd]
  rw [e1, e2, e3, e3', e4, e5]
  have b1 := (log_one_sub_bounds (y := 109 / 2608) (by norm_num) (by norm_num) 3).2
  have b2 := (log_one_sub_bounds (y := 55 / 218) (by norm_num) (by norm_num) 6).1
  have b3 := (log_one_sub_bounds (y := 1 / 4) (by norm_num) (by norm_num) 6).1
  have b4 := (log_one_sub_bounds (y := 1 / 8) (by norm_num) (by norm_num) 5).1
  norm_num [Finset.sum_range_succ] at b1 b2 b3 b4
  have l2 := Real.log_two_gt_d9
  norm_num at l2
  linarith

/-! ## The `h_2` and `h_4` integrals by cells -/

lemma cell_g2_1 {x0 x1 t : ℝ} {n : ℕ} (hn : 0 < n) (hx0 : 1 / 8 ≤ x0) (hx1 : x1 ≤ 1 / 4) (h21 : x1 < 2 * x0)
    (ht : t ∈ Set.Icc x0 x1) : g2 1 t ≤ (1 - 109 / 7824 / x1) * Hb x0 x1 n := by
  obtain ⟨ht1, ht2⟩ := ht
  have ht0 : 0 < t := by linarith
  have hW := W_le_lin (t := t) (by linarith) (by linarith)
  have hh0 := hk_nonneg 1 ht0
  have hh1 := hk1_le_Hb hn (by linarith) (by linarith) ht1 ht2 h21
  unfold g2
  calc Pstar.W t * hk 1 t / t ≤ (t - 109 / 7824) * Hb x0 x1 n / t :=
        div_le_div_of_nonneg_right (mul_le_mul hW hh1 hh0 (by linarith)) ht0.le
    _ = (1 - 109 / 7824 / t) * Hb x0 x1 n := by field_simp
    _ ≤ (1 - 109 / 7824 / x1) * Hb x0 x1 n := by
        apply mul_le_mul_of_nonneg_right _ (hh0.trans hh1)
        have : 109 / 7824 / x1 ≤ 109 / 7824 / t := div_le_div_of_nonneg_left (by norm_num) ht0 ht2
        linarith

lemma cell_g2_2 {x0 x1 t : ℝ} (hx0 : 1 / 8 ≤ x0) (hx1 : x1 ≤ 1 / 6) (ht : t ∈ Set.Icc x0 x1) :
    g2 2 t ≤ (1 - 109 / 7824 / x1) * ((1 - 6 * x0) ^ 4 / (576 * x0 ^ 5)) := by
  obtain ⟨ht1, ht2⟩ := ht
  have ht0 : 0 < t := by linarith
  have hx00 : 0 < x0 := by linarith
  have hW := W_le_lin (t := t) (by linarith) (by linarith)
  have hh0 := hk_nonneg 2 ht0
  have hB0 : 0 ≤ (1 - 6 * x0) ^ 4 / (576 * x0 ^ 5) := by positivity
  have hh1 : hk 2 t ≤ (1 - 6 * x0) ^ 4 / (576 * x0 ^ 5) := by
    rcases lt_or_ge t (1 / 6) with h6 | h6
    · refine (hk2_le ht0 h6).trans ?_
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 4) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx00.le ht1 5) (by norm_num)
    · rw [hk2_eq_zero h6]; exact hB0
  unfold g2
  calc Pstar.W t * hk 2 t / t ≤ (t - 109 / 7824) * ((1 - 6 * x0) ^ 4 / (576 * x0 ^ 5)) / t :=
        div_le_div_of_nonneg_right (mul_le_mul hW hh1 hh0 (by linarith)) ht0.le
    _ = (1 - 109 / 7824 / t) * ((1 - 6 * x0) ^ 4 / (576 * x0 ^ 5)) := by field_simp
    _ ≤ (1 - 109 / 7824 / x1) * ((1 - 6 * x0) ^ 4 / (576 * x0 ^ 5)) := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have : 109 / 7824 / x1 ≤ 109 / 7824 / t := div_le_div_of_nonneg_left (by norm_num) ht0 ht2
        linarith

/-- The upper sum for `∫ W h₂ / t` (32 × 64 cells). -/
noncomputable def A3R : ℝ :=
  ∑ j ∈ range 32, (1 / 4 - 1 / 8) / (32 : ℕ) * ((1 - 109 / 7824 / (1 / 8 + (1 / 4 - 1 / 8) * ((j : ℝ) + 1) / (32 : ℕ))) *
    Hb (1 / 8 + (1 / 4 - 1 / 8) * (j : ℝ) / (32 : ℕ)) (1 / 8 + (1 / 4 - 1 / 8) * ((j : ℝ) + 1) / (32 : ℕ)) 64)

/-- The upper sum for `∫ W h₄ / t` (64 cells). -/
noncomputable def A4R : ℝ :=
  ∑ j ∈ range 64, (1 / 6 - 1 / 8) / (64 : ℕ) * ((1 - 109 / 7824 / (1 / 8 + (1 / 6 - 1 / 8) * ((j : ℝ) + 1) / (64 : ℕ))) *
    ((1 - 6 * (1 / 8 + (1 / 6 - 1 / 8) * (j : ℝ) / (64 : ℕ))) ^ 4 / (576 * (1 / 8 + (1 / 6 - 1 / 8) * (j : ℝ) / (64 : ℕ)) ^ 5)))

theorem G2_le : ∫ t in (1 / 8 : ℝ)..(1 / 2), g2 1 t ≤ A3R := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 4) (ii_g2 1 le_rfl (by norm_num))
    (ii_g2 1 (by norm_num) (by norm_num))]
  have hz : ∫ t in (1 / 4 : ℝ)..(1 / 2), g2 1 t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by norm_num)] at ht
      simp [g2, hk1_eq_zero ht.1]
  rw [hz, add_zero]
  refine integral_le_cells (n := 32) (by norm_num) (by norm_num) (ii_g2 1 le_rfl (by norm_num)) _ fun j hj t ht => ?_
  have hj' : (j : ℝ) + 1 ≤ 32 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  push_cast at ht ⊢
  exact cell_g2_1 (by norm_num) (by linarith) (by linarith) (by linarith) ht

theorem G3_le : ∫ t in (1 / 8 : ℝ)..(1 / 2), g2 2 t ≤ A4R := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 6) (ii_g2 2 le_rfl (by norm_num))
    (ii_g2 2 (by norm_num) (by norm_num))]
  have hz : ∫ t in (1 / 6 : ℝ)..(1 / 2), g2 2 t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
    · simp
    · rw [Set.uIcc_of_le (by norm_num)] at ht
      simp [g2, hk2_eq_zero ht.1]
  rw [hz, add_zero]
  refine integral_le_cells (n := 64) (by norm_num) (by norm_num) (ii_g2 2 le_rfl (by norm_num)) _ fun j hj t ht => ?_
  have hj' : (j : ℝ) + 1 ≤ 64 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  push_cast at ht ⊢
  exact cell_g2_2 (by linarith) (by linarith) ht

/-! ## Rational certificates (checked by the kernel) -/

/-- `Mc` over `ℚ`. -/
def McQ (x0 x1 a0 a1 : ℚ) : ℚ :=
  max (min ((4 * a1 - 1) / 3) ((1 - 3 * x0 - a0) / 6)) 0 *
    (9 / (min (a0 * (1 - a0)) (a1 * (1 - a1)) * (2 - 3 * x1 - 2 * a1)))

/-- `Hb` over `ℚ`. -/
def HbQ (x0 x1 : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ range n, (1 - 3 * x0 - 1 / 4) / n *
    McQ x0 x1 (1 / 4 + (1 - 3 * x0 - 1 / 4) * k / n) (1 / 4 + (1 - 3 * x0 - 1 / 4) * (k + 1) / n)

/-- `A3R` over `ℚ`. -/
def A3Q : ℚ :=
  ∑ j ∈ range 32, (1 / 4 - 1 / 8) / (32 : ℕ) * ((1 - 109 / 7824 / (1 / 8 + (1 / 4 - 1 / 8) * ((j : ℚ) + 1) / (32 : ℕ))) *
    HbQ (1 / 8 + (1 / 4 - 1 / 8) * (j : ℚ) / (32 : ℕ)) (1 / 8 + (1 / 4 - 1 / 8) * ((j : ℚ) + 1) / (32 : ℕ)) 64)

/-- `A4R` over `ℚ`. -/
def A4Q : ℚ :=
  ∑ j ∈ range 64, (1 / 6 - 1 / 8) / (64 : ℕ) * ((1 - 109 / 7824 / (1 / 8 + (1 / 6 - 1 / 8) * ((j : ℚ) + 1) / (64 : ℕ))) *
    ((1 - 6 * (1 / 8 + (1 / 6 - 1 / 8) * (j : ℚ) / (64 : ℕ))) ^ 4 / (576 * (1 / 8 + (1 / 6 - 1 / 8) * (j : ℚ) / (64 : ℕ)) ^ 5)))

theorem A3Q_le : A3Q ≤ 2187 / 100000 := by decide +kernel

theorem A4Q_le : A4Q ≤ 137 / 100000 := by decide +kernel

theorem A3R_eq : A3R = (A3Q : ℝ) := by
  simp only [A3R, A3Q, Hb, HbQ, Mc, McQ]
  push_cast
  rfl

theorem A4R_eq : A4R = (A4Q : ℝ) := by
  simp only [A4R, A4Q]
  push_cast
  rfl

/-! ## The main result -/

theorem Mval_Pstar_ge : (3 / 1000 : ℝ) ≤ Mval Pstar := by
  unfold Mval
  rw [PT0, second_split, A1_eq, G1_eq]
  have h12 := A12_ge
  have h3 := G2_le
  have h4 := G3_le
  rw [A3R_eq] at h3
  rw [A4R_eq] at h4
  have q3 : (A3Q : ℝ) ≤ ((2187 / 100000 : ℚ) : ℝ) := Rat.cast_le.mpr A3Q_le
  have q4 : (A4Q : ℝ) ≤ ((137 / 100000 : ℚ) : ℝ) := Rat.cast_le.mpr A4Q_le
  push_cast at q3 q4
  linarith

theorem Mval_Pstar_pos : 0 < Mval Pstar := by
  have := Mval_Pstar_ge
  linarith

end Palprimes.MT
