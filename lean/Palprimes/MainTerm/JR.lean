import Palprimes.MainTerm.Defs

/-! # Greaves Lemma 5.1, consequences: closed forms of `I_t`, `F`, `f` on the first ranges

* `Iint_one`, `Iint_eq_zero`, `Iint_two`: `I_1(s) = 1/s`, `I_t(s) = 0` for `t ≥ s`,
  `I_2(s) = log(s − 1)/s`;
* `Fjr_eq`, `fjr_eq`, `fjr_le_two`: `F(s) = 2e^γ/s` on `(1, 3]`, `f(s) = 2e^γ log(s − 1)/s` on
  `[2, 4]`, `f = 0` on `(−∞, 2]`;
* regularity: `continuous_Iint` (`t ≥ 2`), `continuousOn_Fjr` (on `(1, ∞)`), `continuous_fjr`;
* bounds: `0 ≤ F, f ≤ 2e^γ 8^9` on `s ≤ 9`.
Also the measurability helpers used by the simplex files. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real Filter Topology

namespace Palprimes.MT

/-! ## Measurability helpers -/

lemma measurable_lt_fun {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a < g a :=
  measurableSet_setOfPred.mp (measurableSet_lt hf hg)

lemma measurable_le_fun {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a ≤ g a :=
  measurableSet_setOfPred.mp (measurableSet_le hf hg)

lemma measurable_strictAnti_comp {α : Type*} [MeasurableSpace α] {n : ℕ} {f : α → Fin n → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => StrictAnti (f a) := by
  unfold StrictAnti
  refine Measurable.forall fun i => Measurable.forall fun j => ?_
  exact measurable_const.imp (measurable_lt_fun (hf j) (hf i))

lemma measurable_strictAnti {n : ℕ} : Measurable fun w : Fin n → ℝ => StrictAnti w :=
  measurable_strictAnti_comp fun i => measurable_pi_apply i

lemma integral_fin_zero (f : (Fin 0 → ℝ) → ℝ) : ∫ w, f w = f Fin.elim0 := by
  rw [MeasureTheory.volume_pi, Measure.pi_of_empty, integral_dirac]
  congr 1

/-- Volume of a level set of a nonzero linear functional is zero. -/
lemma volume_linear_level_null {m : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (a : ℝ) :
    volume {w : Fin m → ℝ | L w = a} = 0 := by
  have hset : {w : Fin m → ℝ | L w = a} =
      ((AffineSubspace.mk' a (⊥ : Submodule ℝ ℝ)).comap L.toAffineMap : Set (Fin m → ℝ)) := by
    ext w
    simp [AffineSubspace.mem_mk', sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_affineSubspace
  intro htop
  apply hL
  have hall : ∀ w, L w = a := by
    intro w
    have : w ∈ ((AffineSubspace.mk' a (⊥ : Submodule ℝ ℝ)).comap L.toAffineMap : Set (Fin m → ℝ)) := by
      rw [htop]; trivial
    simpa [AffineSubspace.mem_mk', sub_eq_zero] using this
  have h0 : a = 0 := by simpa using (hall 0).symm
  ext w
  exact (hall _).trans h0

/-! ## `I_t` -/

lemma Iint_succ (n : ℕ) (s : ℝ) : Iint (n + 1) s =
    ∫ w : Fin n → ℝ, (open Classical in if IRegion n s w then 1 / ((∏ i, w i) * lastU s w) else 0) := by
  simp [Iint]

theorem Iint_one {s : ℝ} (hs : 1 < s) : Iint 1 s = 1 / s := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Iint_succ, integral_fin_zero]
  have : IRegion 0 s Fin.elim0 := by
    refine ⟨fun a => a.elim0, fun i => i.elim0, by simp [lastU, hs], fun i => i.elim0⟩
  simp [this, lastU]

lemma Iint_one_of_le {s : ℝ} (hs : s ≤ 1) : Iint 1 s = 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Iint_succ, integral_fin_zero]
  have : ¬ IRegion 0 s Fin.elim0 := by
    rintro ⟨-, -, h, -⟩; simp [lastU] at h; linarith
  simp [this]

/-- On the region, `s = Σ w + u_t > t`. -/
lemma IRegion_lt {n : ℕ} {s : ℝ} {w : Fin n → ℝ} (h : IRegion n s w) : (n : ℝ) + 1 < s := by
  obtain ⟨-, h1, h2, -⟩ := h
  have : (n : ℝ) ≤ ∑ i, w i := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h1 i).le)
    simpa using this
  unfold lastU at h2
  linarith

theorem Iint_eq_zero {t : ℕ} {s : ℝ} (ht : 1 ≤ t) (hts : (t : ℝ) ≥ s) : Iint t s = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [Iint_succ]
  have : ∀ w : Fin n → ℝ, ¬ IRegion n s w := by
    intro w hw
    have := IRegion_lt hw
    push_cast at hts
    linarith
  simp [this]

lemma Iint_nonneg (t : ℕ) (s : ℝ) : 0 ≤ Iint t s := by
  rcases t with _ | n
  · simp [Iint]
  rw [Iint_succ]
  refine integral_nonneg fun w => ?_
  split_ifs with h
  · obtain ⟨-, h1, h2, -⟩ := h
    have : 0 < ∏ i, w i := Finset.prod_pos fun i _ => by linarith [h1 i]
    positivity
  · exact le_rfl

/-- The integrand of `I_{n+1}` on its region is `≤ 1`. -/
lemma IRegion_integrand_le {n : ℕ} {s : ℝ} {w : Fin n → ℝ} (h : IRegion n s w) :
    1 / ((∏ i, w i) * lastU s w) ≤ 1 := by
  obtain ⟨-, h1, h2, -⟩ := h
  have hp : 1 ≤ ∏ i, w i := Finset.one_le_prod₀ fun i _ => (h1 i).le
  rw [div_le_one (by nlinarith)]
  nlinarith

theorem Iint_two {s : ℝ} (hs : 2 ≤ s) : Iint 2 s = Real.log (s - 1) / s := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Iint_succ]
  have hpos : 0 < s := by linarith
  -- reduce to a one-variable integral
  set g : ℝ → ℝ := fun u => if s / 2 < u ∧ u < s - 1 then 1 / (u * (s - u)) else 0 with hg
  have hfun : (fun w : Fin 1 → ℝ => (open Classical in
      if IRegion 1 s w then 1 / ((∏ i, w i) * lastU s w) else 0)) = fun w => g (w 0) := by
    funext w
    have hreg : IRegion 1 s w ↔ (s / 2 < w 0 ∧ w 0 < s - 1) := by
      simp only [IRegion, lastU, Fin.sum_univ_one, Fin.forall_fin_one]
      constructor
      · rintro ⟨-, h1, h2, h3⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩
        refine ⟨Subsingleton.strictAnti _, by linarith, by linarith, by linarith⟩
    simp only [hg, Fin.prod_univ_one, lastU, Fin.sum_univ_one]
    by_cases h : s / 2 < w 0 ∧ w 0 < s - 1
    · rw [if_pos (hreg.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hreg.mp h')), if_neg h]
  rw [hfun]
  have := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp' (g := g)
  simp only [MeasurableEquiv.funUnique_apply] at this
  rw [show (∫ w : Fin 1 → ℝ, g (w 0)) = ∫ y, g y from this]
  have hgI : g = Set.indicator (Set.Ioo (s / 2) (s - 1)) (fun u => 1 / (u * (s - u))) := by
    funext u; simp [hg, Set.indicator, Set.mem_Ioo]
  rw [hgI, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ u ∈ Set.uIcc (s / 2) (s - 1),
      HasDerivAt (fun u => (Real.log u - Real.log (s - u)) / s) (1 / (u * (s - u))) u := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : 0 < u := by linarith
    have hsu : 0 < s - u := by linarith
    have h1 := Real.hasDerivAt_log hu0.ne'
    have h2 := ((hasDerivAt_id u).const_sub s).log hsu.ne'
    have := (h1.sub h2).div_const s
    exact this.congr_deriv (by simp only [id]; field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · show (Real.log (s - 1) - Real.log (s - (s - 1))) / s - (Real.log (s / 2) - Real.log (s - s / 2)) / s = _
    rw [sub_sub_cancel, Real.log_one, sub_half]
    ring
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.div continuousOn_const
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id))) ?_
    intro u ⟨hu1, hu2⟩
    have h1 : 0 < u := by linarith
    have h2 : 0 < s - u := by linarith
    exact (mul_pos h1 h2).ne'

/-! ## `F` and `f` as finite sums with a fixed range -/

lemma sum_Iint_range_eq {P : ℕ → Prop} [DecidablePred P] {s : ℝ} {M : ℕ} (hM1 : 1 ≤ M) (hM : s < M) :
    ∑ t ∈ (Finset.range (⌊s⌋₊ + 1)).filter P, Iint t s = ∑ t ∈ (Finset.range M).filter P, Iint t s := by
  have hM0 : M ≠ 0 := by omega
  have hfl : ⌊s⌋₊ < M := (Nat.floor_lt' hM0).mpr hM
  apply Finset.sum_subset
  · intro t; simp only [Finset.mem_filter, Finset.mem_range]
    exact fun ⟨h1, h2⟩ => ⟨by omega, h2⟩
  · intro t ht hnot
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at ht hnot
    have ht' : ⌊s⌋₊ + 1 ≤ t := by by_contra h; exact hnot (by omega) ht.2
    apply Iint_eq_zero (by omega)
    have : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
    have : ((⌊s⌋₊ + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht'
    push_cast at this
    linarith

lemma Fjr_eq_sum {s : ℝ} {M : ℕ} (hM1 : 1 ≤ M) (hM : s < M) :
    Fjr s = 2 * Real.exp Real.eulerMascheroniConstant * ∑ t ∈ (Finset.range M).filter Odd, Iint t s := by
  rw [Fjr, sum_Iint_range_eq hM1 hM]

lemma fjr_eq_sum {s : ℝ} {M : ℕ} (hM1 : 1 ≤ M) (hM : s < M) :
    fjr s = 2 * Real.exp Real.eulerMascheroniConstant *
      ∑ t ∈ (Finset.range M).filter (fun t => Even t ∧ 2 ≤ t), Iint t s := by
  rw [fjr, sum_Iint_range_eq hM1 hM]

theorem Fjr_eq {s : ℝ} (h1 : 1 < s) (h3 : s ≤ 3) : Fjr s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
  rw [Fjr_eq_sum (M := 4) (by norm_num) (by norm_num; linarith)]
  have : (Finset.range 4).filter Odd = {1, 3} := by decide
  rw [this, Finset.sum_pair (by norm_num), Iint_one h1, Iint_eq_zero (by norm_num) (by norm_num; linarith)]
  ring

theorem fjr_eq {s : ℝ} (h2 : 2 ≤ s) (h4 : s ≤ 4) :
    fjr s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [fjr_eq_sum (M := 5) (by norm_num) (by norm_num; linarith)]
  have : (Finset.range 5).filter (fun t => Even t ∧ 2 ≤ t) = {2, 4} := by decide
  rw [this, Finset.sum_pair (by norm_num), Iint_two h2, Iint_eq_zero (by norm_num) (by norm_num; linarith)]
  ring

theorem fjr_le_two {s : ℝ} (h2 : s ≤ 2) : fjr s = 0 := by
  rw [fjr_eq_sum (M := 3) (by norm_num) (by norm_num; linarith)]
  have : (Finset.range 3).filter (fun t => Even t ∧ 2 ≤ t) = {2} := by decide
  rw [this, Finset.sum_singleton, Iint_eq_zero (by norm_num) (by norm_num; linarith)]
  ring

theorem Fjr_le_one {s : ℝ} (h1 : s ≤ 1) : Fjr s = 0 := by
  rw [Fjr_eq_sum (M := 2) (by norm_num) (by norm_num; linarith)]
  have : (Finset.range 2).filter Odd = {1} := by decide
  rw [this, Finset.sum_singleton, Iint_eq_zero (by norm_num) (by norm_num; linarith)]
  ring

theorem Fjr_nonneg (s : ℝ) : 0 ≤ Fjr s := by
  unfold Fjr
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => Iint_nonneg t s)

theorem fjr_nonneg (s : ℝ) : 0 ≤ fjr s := by
  unfold fjr
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => Iint_nonneg t s)

/-! ## Regularity -/

lemma measurable_IRegion (n : ℕ) (s : ℝ) : Measurable fun w : Fin n → ℝ => IRegion n s w := by
  unfold IRegion lastU
  refine measurable_strictAnti.and ((Measurable.forall fun i => ?_).and
    ((measurable_lt_fun measurable_const (by fun_prop)).and (Measurable.forall fun i => ?_)))
  · exact measurable_lt_fun measurable_const (measurable_pi_apply i)
  · exact measurable_lt_fun (by fun_prop) (measurable_pi_apply i)

/-- The integrand of `I_{n+1}`. -/
noncomputable def Ifun (n : ℕ) (s : ℝ) (w : Fin n → ℝ) : ℝ :=
  open Classical in if IRegion n s w then 1 / ((∏ i, w i) * lastU s w) else 0

lemma Iint_succ' (n : ℕ) (s : ℝ) : Iint (n + 1) s = ∫ w, Ifun n s w := by
  rw [Iint_succ]; rfl

lemma measurable_Ifun (n : ℕ) (s : ℝ) : Measurable (Ifun n s) := by
  unfold Ifun
  refine Measurable.ite (measurableSet_setOfPred.mpr (measurable_IRegion n s)) ?_ measurable_const
  unfold lastU; fun_prop

lemma Ifun_nonneg (n : ℕ) (s : ℝ) (w : Fin n → ℝ) : 0 ≤ Ifun n s w := by
  unfold Ifun
  split_ifs with h
  · obtain ⟨-, h1, h2, -⟩ := h
    have : 0 < ∏ i, w i := Finset.prod_pos fun i _ => by linarith [h1 i]
    positivity
  · exact le_rfl

/-- The box `[1, S]^n`. -/
def boxI (n : ℕ) (S : ℝ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 1 S

lemma measurableSet_boxI (n : ℕ) (S : ℝ) : MeasurableSet (boxI n S) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma integrable_boxI (n : ℕ) (S : ℝ) : Integrable ((boxI n S).indicator (1 : (Fin n → ℝ) → ℝ)) := by
  rw [integrable_indicator_iff (measurableSet_boxI n S)]
  refine integrableOn_const ?_
  exact (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne

lemma Ifun_le_box {n : ℕ} {s S : ℝ} (hs : s ≤ S) (w : Fin n → ℝ) :
    Ifun n s w ≤ (boxI n S).indicator 1 w := by
  unfold Ifun
  split_ifs with h
  · have hle := IRegion_integrand_le h
    obtain ⟨-, h1, h2, -⟩ := h
    have hw : w ∈ boxI n S := by
      intro i _
      refine ⟨(h1 i).le, ?_⟩
      have : w i ≤ ∑ j, w j :=
        Finset.single_le_sum (fun j _ => by linarith [h1 j]) (Finset.mem_univ i)
      unfold lastU at h2
      linarith
    rw [Set.indicator_of_mem hw]
    simpa using hle
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) w

lemma Iint_le_pow {n : ℕ} {s : ℝ} (hs : s ≤ 9) : Iint (n + 1) s ≤ 8 ^ n := by
  rw [Iint_succ']
  calc ∫ w, Ifun n s w ≤ ∫ w, (boxI n 9).indicator 1 w :=
        integral_mono_of_nonneg (ae_of_all _ (Ifun_nonneg n s)) (integrable_boxI n 9)
          (ae_of_all _ (Ifun_le_box hs))
    _ = 8 ^ n := by
        rw [integral_indicator_one (measurableSet_boxI n 9), Measure.real, boxI,
          volume_pi_pi]
        simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num)]
        norm_num

lemma Iint_le {t : ℕ} {s : ℝ} (hs : s ≤ 9) : Iint t s ≤ 8 ^ t := by
  rcases t with _ | n
  · simp [Iint]
  · exact (Iint_le_pow hs).trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))

lemma volume_sum_level_null {m : ℕ} (hm : 0 < m) (a : ℝ) :
    volume {w : Fin m → ℝ | ∑ i, w i = a} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
  have hL : L ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (fun _ => 1)
    simp [L] at this
    omega
  have := volume_linear_level_null L hL a
  simpa [L] using this

lemma volume_sum_add_level_null {m : ℕ} (i : Fin m) (a : ℝ) :
    volume {w : Fin m → ℝ | ∑ j, w j + w i = a} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := ∑ j, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j + LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
  have hL : L ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (fun _ => 1)
    simp [L] at this
    linarith
  have := volume_linear_level_null L hL a
  simpa [L] using this

lemma continuousAt_Ifun {n : ℕ} {s0 : ℝ} {w : Fin n → ℝ} (hw1 : ∑ i, w i ≠ s0 - 1)
    (hw2 : ∀ i, ∑ j, w j + w i ≠ s0) : ContinuousAt (fun s => Ifun n s w) s0 := by
  classical
  by_cases hR : IRegion n s0 w
  · obtain ⟨hA, hB, hC, hD⟩ := hR
    unfold lastU at hC hD
    have hev : ∀ᶠ s in 𝓝 s0, IRegion n s w := by
      have hC' : ∀ᶠ s in 𝓝 s0, 1 < s - ∑ i, w i :=
        continuousAt_const.eventually_lt (continuousAt_id.sub continuousAt_const) hC
      have hD' : ∀ᶠ s in 𝓝 s0, ∀ i, s - ∑ i, w i < w i :=
        Filter.eventually_all.mpr fun i =>
          (continuousAt_id.sub continuousAt_const).eventually_lt continuousAt_const (hD i)
      filter_upwards [hC', hD'] with s h1 h2
      exact ⟨hA, hB, h1, h2⟩
    have hcont : ContinuousAt (fun s => 1 / ((∏ i, w i) * lastU s w)) s0 := by
      unfold lastU
      have hp : 0 < ∏ i, w i := Finset.prod_pos fun i _ => by linarith [hB i]
      have hne : (∏ i, w i) * (s0 - ∑ i, w i) ≠ 0 := (mul_pos hp (by linarith)).ne'
      refine continuousAt_const.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)) ?_
      exact hne
    refine hcont.congr ?_
    filter_upwards [hev] with s hs
    simp [Ifun, hs]
  · have hev : ∀ᶠ s in 𝓝 s0, ¬ IRegion n s w := by
      unfold IRegion lastU at hR ⊢
      by_cases hA : StrictAnti w
      swap
      · exact Filter.Eventually.of_forall fun s h => hA h.1
      by_cases hB : ∀ i, 1 < w i
      swap
      · exact Filter.Eventually.of_forall fun s h => hB h.2.1
      by_cases hC : 1 < s0 - ∑ i, w i
      · have hD : ∃ i, ¬ (s0 - ∑ j, w j < w i) := by
          by_contra hc; push_neg at hc; exact hR ⟨hA, hB, hC, hc⟩
        obtain ⟨i, hi⟩ := hD
        push_neg at hi
        have hi' : w i < s0 - ∑ j, w j := lt_of_le_of_ne hi (fun h => hw2 i (by linarith))
        have : ∀ᶠ s in 𝓝 s0, w i < s - ∑ j, w j :=
          continuousAt_const.eventually_lt (continuousAt_id.sub continuousAt_const) hi'
        filter_upwards [this] with s hs h
        linarith [h.2.2.2 i]
      · push_neg at hC
        have hC' : s0 - ∑ i, w i < 1 := lt_of_le_of_ne hC (fun h => hw1 (by linarith))
        have : ∀ᶠ s in 𝓝 s0, s - ∑ i, w i < 1 :=
          (continuousAt_id.sub continuousAt_const).eventually_lt continuousAt_const hC'
        filter_upwards [this] with s hs h
        linarith [h.2.2.1]
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with s hs
    simp [Ifun, hs]

theorem continuous_Iint_two_le (n : ℕ) : Continuous (Iint (n + 2)) := by
  rw [continuous_iff_continuousAt]
  intro s0
  have hfun : Iint (n + 2) = fun s => ∫ w, Ifun (n + 1) s w := by
    funext s; exact Iint_succ' (n + 1) s
  rw [hfun]
  refine continuousAt_of_dominated (bound := (boxI (n + 1) (s0 + 1)).indicator 1) ?_ ?_
    (integrable_boxI _ _) ?_
  · exact Filter.Eventually.of_forall fun s => (measurable_Ifun _ s).aestronglyMeasurable
  · have : ∀ᶠ s in 𝓝 s0, s < s0 + 1 := eventually_lt_nhds (by linarith)
    filter_upwards [this] with s hs
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_of_nonneg (Ifun_nonneg _ _ _)]
    exact Ifun_le_box hs.le w
  · have h1 := volume_sum_level_null (m := n + 1) (by omega) (s0 - 1)
    have h2 : volume (⋃ i : Fin (n + 1), {w : Fin (n + 1) → ℝ | ∑ j, w j + w i = s0}) = 0 :=
      measure_iUnion_null fun i => volume_sum_add_level_null i s0
    have hnull := measure_union_null h1 h2
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists] at hc
    exact hw (continuousAt_Ifun hc.1 hc.2)

theorem continuousAt_Iint {t : ℕ} {s0 : ℝ} (h : t ≠ 1 ∨ 1 < s0) : ContinuousAt (Iint t) s0 := by
  rcases t with _ | _ | n
  · have : Iint 0 = fun _ => 0 := by funext s; simp [Iint]
    rw [this]; exact continuousAt_const
  · have h1 : 1 < s0 := by simpa using h
    have : Iint 1 =ᶠ[𝓝 s0] fun s => 1 / s := by
      filter_upwards [eventually_gt_nhds h1] with s hs
      exact Iint_one hs
    exact (continuousAt_const.div continuousAt_id (by simp only [id]; exact ne_of_gt (by linarith))).congr this.symm
  · exact (continuous_Iint_two_le n).continuousAt

theorem continuousOn_Fjr : ContinuousOn Fjr (Set.Ioi 1) := by
  intro s0 hs0
  apply ContinuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := exists_nat_gt s0
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) < M := lt_trans hs0 hM
    exact_mod_cast this.le
  have heq : Fjr =ᶠ[𝓝 s0] fun s => 2 * Real.exp Real.eulerMascheroniConstant *
      ∑ t ∈ (Finset.range M).filter Odd, Iint t s := by
    filter_upwards [eventually_lt_nhds hM] with s hs
    exact Fjr_eq_sum hM1 hs
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (fun s => ∑ t ∈ (Finset.range M).filter Odd, Iint t s) s0 :=
    tendsto_finsetSum _ fun t _ => continuousAt_Iint (Or.inr hs0)
  exact continuousAt_const.mul hc

theorem continuous_fjr : Continuous fjr := by
  rw [continuous_iff_continuousAt]
  intro s0
  obtain ⟨M, hM⟩ := exists_nat_gt s0
  have hM1 : 1 ≤ M + 1 := by omega
  have hM' : s0 < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
  have heq : fjr =ᶠ[𝓝 s0] fun s => 2 * Real.exp Real.eulerMascheroniConstant *
      ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint t s := by
    filter_upwards [eventually_lt_nhds hM'] with s hs
    exact fjr_eq_sum hM1 hs
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (fun s => ∑ t ∈ (Finset.range (M + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint t s) s0 := by
    refine tendsto_finsetSum _ fun t ht => continuousAt_Iint (Or.inl ?_)
    simp only [Finset.mem_filter] at ht
    omega
  exact continuousAt_const.mul hc

theorem continuousOn_fjr : ContinuousOn fjr (Set.Ioi 0) := continuous_fjr.continuousOn

/-! ## Explicit bounds -/

lemma sum_filter_Iint_le {P : ℕ → Prop} [DecidablePred P] {s : ℝ} (hs : s ≤ 9) :
    ∑ t ∈ (Finset.range 10).filter P, Iint t s ≤ 8 ^ 10 := by
  calc ∑ t ∈ (Finset.range 10).filter P, Iint t s ≤ ∑ t ∈ Finset.range 10, Iint t s :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun t _ _ => Iint_nonneg t s)
    _ ≤ ∑ t ∈ Finset.range 10, (8 : ℝ) ^ t := Finset.sum_le_sum fun t _ => Iint_le hs
    _ ≤ 8 ^ 10 := by simp [Finset.sum_range_succ]; norm_num

theorem Fjr_le {s : ℝ} (hs : s ≤ 9) : Fjr s ≤ 2 * Real.exp Real.eulerMascheroniConstant * 8 ^ 10 := by
  rw [Fjr_eq_sum (M := 10) (by norm_num) (by norm_num; linarith)]
  exact mul_le_mul_of_nonneg_left (sum_filter_Iint_le hs) (by positivity)

theorem fjr_le {s : ℝ} (hs : s ≤ 9) : fjr s ≤ 2 * Real.exp Real.eulerMascheroniConstant * 8 ^ 10 := by
  rw [fjr_eq_sum (M := 10) (by norm_num) (by norm_num; linarith)]
  exact mul_le_mul_of_nonneg_left (sum_filter_Iint_le hs) (by positivity)

/-- The explicit bounds of deliverable 3 (`0 < s ≤ 9`). -/
theorem Fjr_bounds {s : ℝ} (hs : s ≤ 9) :
    0 ≤ Fjr s ∧ Fjr s ≤ 2 * Real.exp Real.eulerMascheroniConstant * 8 ^ 10 :=
  ⟨Fjr_nonneg s, Fjr_le hs⟩

theorem fjr_bounds {s : ℝ} (hs : s ≤ 9) :
    0 ≤ fjr s ∧ fjr s ≤ 2 * Real.exp Real.eulerMascheroniConstant * 8 ^ 10 :=
  ⟨fjr_nonneg s, fjr_le hs⟩

end Palprimes.MT
