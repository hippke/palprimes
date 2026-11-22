import Palprimes.MainTerm.E1
import Palprimes.Sieve.Vendor.Mertens
import Palprimes.Defs

/-! # Multi-dimensional prime sums as Riemann sums

In log-log coordinates `σ_y(p) = log(log p / log y)`, the measure `Σ_p gB(p) δ_{σ_y(p)}` on
`(log a, 0]` converges on intervals to Lebesgue measure (Mertens 2). Hence, for `f` bounded and
a.e. continuous on the box `(log a, 0]^r` (Riemann integrable, Mathlib's `BoxIntegral`),
`Σ_{p_1,…,p_r ∈ (y^a, y]} Π gB(p_i) f(σ_y(p⃗)) → ∫_{(log a,0]^r} f`. -/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace Palprimes.MT

/-- `b³ − b ≠ 0` for `b ≥ 2` (copy of `bigB_ne_zero'`, to keep the import chain short). -/
theorem bigB_ne_zero' (b : ℕ) (hb : 2 ≤ b) : Palprimes.bigB b ≠ 0 := by
  unfold Palprimes.bigB
  have h4 : 4 ≤ b * b := Nat.mul_le_mul hb hb
  have h3 : b * 4 ≤ b ^ 3 := by
    calc b * 4 ≤ b * (b * b) := Nat.mul_le_mul_left _ h4
      _ = b ^ 3 := by ring
  omega

/-- Log-log coordinate. -/
noncomputable def sig (y : ℝ) (p : ℕ) : ℝ := Real.log (Real.log p / Real.log y)

/-- Primes in `(y^a, y]`. -/
noncomputable def Pset (y a : ℝ) : Finset ℕ := (Ioc ⌊y ^ a⌋₊ ⌊y⌋₊).filter Nat.Prime

/-- The one-dimensional mass of `(l, u]`. -/
noncomputable def mu1 (b : ℕ) (y a l u : ℝ) : ℝ :=
  open Classical in ∑ p ∈ (Pset y a).filter (fun p => sig y p ∈ Set.Ioc l u), gB b p

theorem sig_mem_Ioc (y : ℝ) (hy : 1 < y) (l u : ℝ) (p : ℕ) (hp : 1 < p) :
    sig y p ∈ Set.Ioc l u ↔ y ^ Real.exp l < p ∧ (p : ℝ) ≤ y ^ Real.exp u := by
  have hL : 0 < Real.log y := Real.log_pos hy
  have hp0 : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hq : 0 < Real.log p / Real.log y := div_pos hp0 hL
  unfold sig
  rw [Set.mem_Ioc, ← Real.exp_lt_exp, Real.exp_log hq, ← Real.exp_le_exp (x := Real.log _), Real.exp_log hq,
    lt_div_iff₀ hL, div_le_iff₀ hL]
  have hpos : (0 : ℝ) < p := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← Real.exp_log hpos, Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_lt_exp.2 (by linarith)
    · rw [← Real.exp_log hpos, Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_le_exp.2 (by linarith)
  · rintro ⟨h1, h2⟩
    rw [Real.rpow_def_of_pos (by linarith)] at h1 h2
    have h1' := Real.log_lt_log (Real.exp_pos _) h1
    have h2' := Real.log_le_log hpos h2
    rw [Real.log_exp] at h1' h2'
    constructor <;> linarith

theorem gB_eq (b p : ℕ) (hb : 2 ≤ b) (hp : p.Prime) (hpB : bigB b < p) : gB b p = 1 / p := by
  have hc : Nat.Coprime p (Palprimes.bigB b) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hB0 : 0 < Palprimes.bigB b := by have := bigB_ne_zero' b hb; omega
    exact absurd (Nat.le_of_dvd hB0 hdvd) (by omega)
  unfold gB
  rw [if_pos ⟨hp, hc⟩]

/-- **Mertens on log-log intervals**: `mu1 (l, u] → u − l`. -/
theorem mu1_tendsto (b : ℕ) (hb : 2 ≤ b) (a l u : ℝ) (ha : 0 < a) (hla : Real.log a ≤ l) (hlu : l ≤ u)
    (hu : u ≤ 0) : Tendsto (fun y => mu1 b y a l u) atTop (𝓝 (u - l)) := by
  classical
  obtain ⟨C, hC⟩ := Palprimes.mertens2_interval
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hel : 0 < Real.exp l := Real.exp_pos l
  -- choose `Y` with `Y^{e^l} ≥ max 2 (B+1)` and `|C|/(e^l log Y) < ε`
  obtain ⟨Y0, hY0⟩ : ∃ Y0 : ℝ, 1 < Y0 ∧ ∀ y ≥ Y0, max 2 ((bigB b : ℝ) + 1) ≤ y ^ Real.exp l ∧
      |C| / (Real.exp l * Real.log y) < ε := by
    set K : ℝ := max (max 2 ((bigB b : ℝ) + 1)) (Real.exp ((|C| / ε + 1) / Real.exp l)) with hK
    refine ⟨Real.exp ((Real.log K + 1) / Real.exp l) , ?_, ?_⟩
    · have : 0 < (Real.log K + 1) / Real.exp l := by
        have : 0 ≤ Real.log K := Real.log_nonneg (by rw [hK]; exact le_trans (by norm_num) (le_max_left _ _ |>.trans (le_max_left _ _)))
        positivity
      have := Real.add_one_lt_exp (ne_of_gt this); linarith
    · intro y hy
      have hK1 : 1 ≤ K := le_trans (by norm_num) ((le_max_left _ _).trans (le_max_left _ _))
      have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
      have hly : (Real.log K + 1) / Real.exp l ≤ Real.log y := by
        have := Real.log_le_log (Real.exp_pos _) hy; rwa [Real.log_exp] at this
      have hly' : Real.log K + 1 ≤ Real.exp l * Real.log y := by
        rw [div_le_iff₀ hel] at hly; linarith
      constructor
      · rw [Real.rpow_def_of_pos hy0]
        calc max 2 ((bigB b : ℝ) + 1) ≤ K := le_max_left _ _
          _ = Real.exp (Real.log K) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (Real.log y * Real.exp l) := Real.exp_le_exp.2 (by linarith)
      · have hK2 : (|C| / ε + 1) / Real.exp l ≤ Real.log K := by
          rw [Real.le_log_iff_exp_le (by linarith)]; exact le_max_right _ _
        rw [div_le_iff₀ hel] at hK2
        have hpos : 0 < Real.exp l * Real.log y := by nlinarith [Real.log_nonneg hK1]
        rw [div_lt_iff₀ hpos]
        have hel1 : Real.exp l ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (le_trans hlu hu)
        have hlK : 0 ≤ Real.log K := Real.log_nonneg hK1
        have h3 : Real.log K * Real.exp l ≤ Real.log K := by nlinarith
        have : |C| / ε < Real.exp l * Real.log y := by linarith
        rwa [div_lt_iff₀ hε, mul_comm] at this
  obtain ⟨hY1, hY⟩ := hY0
  refine ⟨Y0, fun y hy => ?_⟩
  obtain ⟨hy2, hyε⟩ := hY y hy
  have hy1 : 1 < y := lt_of_lt_of_le hY1 hy
  have hy0 : 0 < y := by linarith
  have hL : 0 < Real.log y := Real.log_pos hy1
  set A := y ^ Real.exp l with hA
  set Bt := y ^ Real.exp u with hBt
  have hA2 : 2 ≤ A := le_trans (le_max_left _ _) hy2
  have hAB : A ≤ Bt := Real.rpow_le_rpow_of_exponent_le hy1.le (Real.exp_le_exp.2 hlu)
  have hBy : Bt ≤ y := by
    calc Bt ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 hu)
      _ = y := Real.rpow_one y
  have hya : y ^ a ≤ A := Real.rpow_le_rpow_of_exponent_le hy1.le (by
    rw [← Real.exp_log ha]; exact Real.exp_le_exp.2 hla)
  -- the filtered set is the primes in `(A, B]`
  have hset : (Pset y a).filter (fun p => sig y p ∈ Set.Ioc l u) = (Ioc ⌊A⌋₊ ⌊Bt⌋₊).filter Nat.Prime := by
    ext p
    simp only [Pset, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_, _⟩, hp⟩, hs⟩
      rw [sig_mem_Ioc y hy1 l u p hp.one_lt] at hs
      exact ⟨⟨Nat.floor_lt' (by have := hp.pos; omega) |>.2 hs.1, Nat.le_floor hs.2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      have hs1 : A < p := (Nat.floor_lt' (by have := hp.pos; omega)).1 h1
      have hs2 : (p : ℝ) ≤ Bt := le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
      refine ⟨⟨⟨?_, ?_⟩, hp⟩, (sig_mem_Ioc y hy1 l u p hp.one_lt).2 ⟨hs1, hs2⟩⟩
      · exact (Nat.floor_lt' (by have := hp.pos; omega)).2 (lt_of_le_of_lt hya hs1)
      · exact Nat.le_floor (le_trans hs2 hBy)
  have hsum : mu1 b y a l u = ∑ p ∈ (Ioc ⌊A⌋₊ ⌊Bt⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    unfold mu1
    rw [hset]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    apply gB_eq b p hb hp.2
    have hpA : A < p := (Nat.floor_lt' (by have := hp.2.pos; omega)).1 hp.1.1
    have : ((bigB b : ℕ) : ℝ) + 1 ≤ A := le_trans (le_max_right _ _) hy2
    have : ((bigB b : ℕ) : ℝ) < p := by linarith
    exact_mod_cast this
  have hM := hC A Bt hA2 hAB
  have hll : Real.log (Real.log Bt) - Real.log (Real.log A) = u - l := by
    rw [hA, hBt, Real.log_rpow hy0, Real.log_rpow hy0, Real.log_mul (Real.exp_pos _).ne' hL.ne',
      Real.log_mul (Real.exp_pos _).ne' hL.ne', Real.log_exp, Real.log_exp]; ring
  rw [hll] at hM
  have hlogA : Real.log A = Real.exp l * Real.log y := by rw [hA, Real.log_rpow hy0]
  rw [Real.dist_eq, hsum]
  calc _ ≤ C / Real.log A := hM
    _ ≤ |C| / Real.log A := div_le_div_of_nonneg_right (le_abs_self C) (Real.log_pos (by linarith)).le
    _ < ε := by rw [hlogA]; exact hyε

open BoxIntegral

/-- The box `(log a, 0]^r`. -/
noncomputable def boxA (r : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : Box (Fin r) where
  lower := fun _ => Real.log a
  upper := fun _ => 0
  lower_lt_upper := fun _ => Real.log_neg ha0 ha1

/-- The vector of log-log coordinates. -/
noncomputable def sigv {r : ℕ} (y : ℝ) (q : Fin r → ℕ) : Fin r → ℝ := fun i => sig y (q i)

theorem gB_nonneg (b p : ℕ) : 0 ≤ gB b p := by
  unfold gB; split_ifs <;> positivity

theorem sigv_mem_box {r : ℕ} (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (y : ℝ) (hy : 1 < y)
    (q : Fin r → ℕ) (hq : q ∈ Fintype.piFinset (fun _ => Pset y a)) :
    sigv y q ∈ (boxA r a ha0 ha1 : Set (Fin r → ℝ)) := by
  rw [Box.mem_coe, Box.mem_mk]
  intro i
  have hqi := Fintype.mem_piFinset.1 hq i
  simp only [Pset, mem_filter, mem_Ioc] at hqi
  obtain ⟨⟨h1, h2⟩, hp⟩ := hqi
  rw [sigv, sig_mem_Ioc y hy _ _ (q i) hp.one_lt]
  show y ^ Real.exp (Real.log a) < (q i : ℝ) ∧ (q i : ℝ) ≤ y ^ Real.exp 0
  rw [Real.exp_log ha0, Real.exp_zero, Real.rpow_one]
  refine ⟨(Nat.floor_lt' (by have := hp.pos; omega)).1 h1, ?_⟩
  exact le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))

/-- The mass of a sub-box is a product of one-dimensional masses. -/
theorem box_mass {r : ℕ} (b : ℕ) (a : ℝ) (y : ℝ) (J : Box (Fin r)) :
    (∑ q ∈ Fintype.piFinset (fun _ => Pset y a),
        open Classical in if sigv y q ∈ (J : Set (Fin r → ℝ)) then ∏ i, gB b (q i) else 0) =
      ∏ i, mu1 b y a (J.lower i) (J.upper i) := by
  classical
  unfold mu1
  rw [Finset.prod_univ_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    simp only [mem_filter, Fintype.mem_piFinset, Box.mem_coe, Box.mem_mk, sigv]
    constructor
    · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · intro q _; rfl

/-- The box mass converges to the volume. -/
theorem box_mass_tendsto {r : ℕ} (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (J : Box (Fin r)) (hJ : J ≤ boxA r a ha0 ha1) :
    Tendsto (fun y => ∑ q ∈ Fintype.piFinset (fun _ => Pset y a),
        open Classical in if sigv y q ∈ (J : Set (Fin r → ℝ)) then ∏ i, gB b (q i) else 0)
      atTop (𝓝 ((MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal)) := by
  classical
  simp_rw [box_mass b a]
  rw [Box.volume_apply']
  apply tendsto_finsetProd
  intro i _
  have hle := Box.le_iff_bounds.1 hJ
  apply mu1_tendsto b hb a _ _ ha0
  · exact hle.1 i
  · exact (J.lower_lt_upper i).le
  · exact hle.2 i

/-- `x` lies in exactly one box of a partition. -/
theorem sum_boxes_indicator {r : ℕ} {I : Box (Fin r)} (Pt : Prepartition I) (hPt : Pt.IsPartition)
    (x : Fin r → ℝ) (hx : x ∈ I) :
    (∑ J ∈ Pt.boxes, (open Classical in if x ∈ (J : Set (Fin r → ℝ)) then (1 : ℝ) else 0)) = 1 := by
  classical
  obtain ⟨J0, hJ0, hxJ0⟩ := hPt x hx
  rw [Finset.sum_eq_single J0]
  · simp [hxJ0]
  · intro J hJ hne
    rw [if_neg]
    intro hxJ
    exact hne (Pt.eq_of_mem_of_mem hJ hJ0 hxJ hxJ0)
  · intro h; exact absurd hJ0 h

/-- Near-supremum tags. -/
theorem exists_near_sup {r : ℕ} (f : (Fin r → ℝ) → ℝ) (J : Box (Fin r)) (C : ℝ)
    (hC : ∀ x ∈ Box.Icc J, f x ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ Box.Icc J, ∀ x ∈ Box.Icc J, f x ≤ f t + ε := by
  have hne : (f '' Box.Icc J).Nonempty := ⟨f J.upper, ⟨J.upper, J.upper_mem_Icc, rfl⟩⟩
  have hbdd : BddAbove (f '' Box.Icc J) := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  obtain ⟨v, ⟨t, ht, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne (by linarith : sSup (f '' Box.Icc J) - ε < sSup (f '' Box.Icc J))
  refine ⟨t, ht, fun x hx => ?_⟩
  have := le_csSup hbdd ⟨x, hx, rfl⟩
  linarith

/-- **The upper estimate**: for every `ε > 0`, eventually `S_y(f) ≤ ∫ f + ε (2 + vol)`. -/
theorem prime_sum_upper {r : ℕ} (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f : (Fin r → ℝ) → ℝ)
    (hbd : ∃ C, ∀ x ∈ Box.Icc (boxA r a ha0 ha1), ‖f x‖ ≤ C)
    (hcont : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin r → ℝ)), ContinuousAt f x)
    (hint : MeasureTheory.IntegrableOn f (boxA r a ha0 ha1 : Set (Fin r → ℝ))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in atTop, ∑ q ∈ Fintype.piFinset (fun _ => Pset y a), (∏ i, gB b (q i)) * f (sigv y q) <
      (∫ x in (boxA r a ha0 ha1 : Set (Fin r → ℝ)), f x) +
        ε * (2 + (MeasureTheory.volume (boxA r a ha0 ha1 : Set (Fin r → ℝ))).toReal) := by
  classical
  set I := boxA r a ha0 ha1 with hIdef
  set vol : Fin r →ᵇᵃ (ℝ →L[ℝ] ℝ) :=
    (MeasureTheory.volume : MeasureTheory.Measure (Fin r → ℝ)).toBoxAdditive.toSMul with hvol
  set L := ∫ x in (I : Set (Fin r → ℝ)), f x with hL
  set V := (MeasureTheory.volume (I : Set (Fin r → ℝ))).toReal with hV
  obtain ⟨C, hC⟩ := hbd
  -- Riemann integrability with the Lebesgue value
  have hR : HasIntegral I IntegrationParams.Riemann f vol L := by
    have h1 := (integrable_of_bounded_and_ae_continuous IntegrationParams.Riemann ⟨C, hC⟩
      MeasureTheory.volume hcont).hasIntegral
    have h2 := hint.hasBoxIntegral IntegrationParams.McShane rfl
    have h1' := h1.mono IntegrationParams.henstock_le_riemann
    have h2' := h2.mono IntegrationParams.henstock_le_mcShane
    rwa [h1'.unique h2'] at h1
  rw [hasIntegral_iff] at hR
  obtain ⟨rr, hrr, hrr2⟩ := hR ε hε
  set c0 := I.distortion
  set ρ : ℝ := (rr c0 0 : ℝ) with hρ
  have hρ0 : 0 < ρ := (rr c0 0).2
  have hconst : ∀ x, rr c0 x = rr c0 0 := hrr c0 rfl
  set r' : (Fin r → ℝ) → Set.Ioi (0 : ℝ) := fun _ => ⟨ρ / 2, Set.mem_Ioi.2 (half_pos hρ0)⟩ with hr'
  obtain ⟨Pt, hPt, hPtg⟩ := IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann I le_rfl r'
  -- near-supremum tags
  have hfC : ∀ J : Box (Fin r), J ≤ I → ∀ x ∈ Box.Icc J, f x ≤ C := by
    intro J hJ x hx
    have := hC x (Box.le_iff_Icc.1 hJ hx)
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  set tg : Box (Fin r) → (Fin r → ℝ) := fun J =>
    if h : J ≤ I then Classical.choose (exists_near_sup f J C (hfC J h) ε hε) else I.upper with htg
  have htg_mem : ∀ J, J ≤ I → tg J ∈ Box.Icc J ∧ ∀ x ∈ Box.Icc J, f x ≤ f (tg J) + ε := by
    intro J hJ
    simp only [htg, dif_pos hJ]
    exact Classical.choose_spec (exists_near_sup f J C (hfC J hJ) ε hε)
  let Ptg : TaggedPrepartition I :=
    { toPrepartition := Pt.toPrepartition
      tag := tg
      tag_mem_Icc := fun J => by
        by_cases hJ : J ≤ I
        · exact Box.le_iff_Icc.1 hJ (htg_mem J hJ).1
        · simp only [htg, dif_neg hJ]; exact I.upper_mem_Icc }
  have hmem : IntegrationParams.Riemann.MemBaseSet I c0 (rr c0) Ptg := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro J hJ x hx
      have hJI : J ≤ I := Pt.le_of_mem hJ
      rw [Metric.mem_closedBall, hconst]
      have hsub := hPt.isSubordinate J hJ
      have h1 : x ∈ Metric.closedBall (Pt.tag J) (ρ / 2) := hsub hx
      have h2 : tg J ∈ Metric.closedBall (Pt.tag J) (ρ / 2) := hsub (htg_mem J hJI).1
      rw [Metric.mem_closedBall] at h1 h2
      calc dist x (tg J) ≤ dist x (Pt.tag J) + dist (tg J) (Pt.tag J) := dist_triangle_right _ _ _
        _ ≤ ρ / 2 + ρ / 2 := add_le_add h1 h2
        _ = ρ := by ring
    · intro _ J hJ; exact (htg_mem J (Pt.le_of_mem hJ)).1
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  have hsumPtg := hrr2 c0 Ptg hmem hPtg
  have hint_sum : integralSum f vol Ptg = ∑ J ∈ Pt.boxes, (MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal * f (tg J) := by
    simp only [integralSum, hvol, BoxAdditiveMap.toSMul_apply, MeasureTheory.Measure.toBoxAdditive_apply,
      smul_eq_mul, MeasureTheory.measureReal_def]
    rfl
  have hvolsum : ∑ J ∈ Pt.boxes, (MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal = V := by
    have := (MeasureTheory.volume : MeasureTheory.Measure (Fin r → ℝ)).toBoxAdditive.sum_partition_boxes le_top hPtg
    simp only [MeasureTheory.Measure.toBoxAdditive_apply, MeasureTheory.measureReal_def] at this
    rw [hV]; exact this
  -- the bound function `U(y)` and its limit
  set mass : Box (Fin r) → ℝ → ℝ := fun J y => ∑ q ∈ Fintype.piFinset (fun _ => Pset y a),
    (if sigv y q ∈ (J : Set (Fin r → ℝ)) then ∏ i, gB b (q i) else 0) with hmass
  have hlim : Tendsto (fun y => ∑ J ∈ Pt.boxes, (f (tg J) + ε) * mass J y) atTop
      (𝓝 (∑ J ∈ Pt.boxes, (f (tg J) + ε) * (MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal)) := by
    apply tendsto_finsetSum
    intro J hJ
    exact (box_mass_tendsto b hb a ha0 ha1 J (Pt.le_of_mem hJ)).const_mul _
  have hval : ∑ J ∈ Pt.boxes, (f (tg J) + ε) * (MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal ≤ L + ε + ε * V := by
    have e : ∑ J ∈ Pt.boxes, (f (tg J) + ε) * (MeasureTheory.volume (J : Set (Fin r → ℝ))).toReal =
        integralSum f vol Ptg + ε * V := by
      rw [hint_sum, ← hvolsum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro J _; ring
    rw [e]
    have hd : |integralSum f vol Ptg - L| ≤ ε := by rw [← Real.dist_eq]; exact hsumPtg
    have := (abs_le.1 hd).2
    linarith
  have hev := (tendsto_order.1 hlim).2 (L + ε * (2 + V)) (by linarith)
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with y hy hy1
  refine lt_of_le_of_lt ?_ hy
  -- `S_y ≤ U(y)`
  have hdec : ∑ q ∈ Fintype.piFinset (fun _ => Pset y a), (∏ i, gB b (q i)) * f (sigv y q) =
      ∑ J ∈ Pt.boxes, ∑ q ∈ Fintype.piFinset (fun _ => Pset y a),
        (if sigv y q ∈ (J : Set (Fin r → ℝ)) then (∏ i, gB b (q i)) * f (sigv y q) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q hq
    have h1 := sum_boxes_indicator Pt.toPrepartition hPtg (sigv y q) (sigv_mem_box a ha0 ha1 y hy1 q hq)
    calc (∏ i, gB b (q i)) * f (sigv y q) = (∏ i, gB b (q i)) * f (sigv y q) *
          ∑ J ∈ Pt.boxes, (if sigv y q ∈ (J : Set (Fin r → ℝ)) then (1 : ℝ) else 0) := by rw [h1, mul_one]
      _ = _ := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro J _
          split_ifs <;> simp
  rw [hdec]
  apply Finset.sum_le_sum
  intro J hJ
  simp only [hmass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  split_ifs with hq
  · have hx : sigv y q ∈ Box.Icc J := Box.coe_subset_Icc hq
    have hf := (htg_mem J (Pt.le_of_mem hJ)).2 _ hx
    have hg0 : 0 ≤ ∏ i, gB b (q i) := Finset.prod_nonneg (fun i _ => gB_nonneg b _)
    rw [mul_comm (f (tg J) + ε)]
    exact mul_le_mul_of_nonneg_left hf hg0
  · simp

/-- **Prime sums converge to the integral** (bounded, a.e. continuous, integrable `f`). -/
theorem prime_sum_tendsto {r : ℕ} (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (f : (Fin r → ℝ) → ℝ)
    (hbd : ∃ C, ∀ x ∈ Box.Icc (boxA r a ha0 ha1), ‖f x‖ ≤ C)
    (hcont : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin r → ℝ)), ContinuousAt f x)
    (hint : MeasureTheory.IntegrableOn f (boxA r a ha0 ha1 : Set (Fin r → ℝ))) :
    Tendsto (fun y => ∑ q ∈ Fintype.piFinset (fun _ => Pset y a), (∏ i, gB b (q i)) * f (sigv y q))
      atTop (𝓝 (∫ x in (boxA r a ha0 ha1 : Set (Fin r → ℝ)), f x)) := by
  set V := (MeasureTheory.volume (boxA r a ha0 ha1 : Set (Fin r → ℝ))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set L := ∫ x in (boxA r a ha0 ha1 : Set (Fin r → ℝ)), f x with hL
  rw [tendsto_order]
  constructor
  · intro t ht
    -- lower bound via `-f`
    set ε := (L - t) / (2 * (2 + V)) with hε
    have hε0 : 0 < ε := by rw [hε]; apply div_pos (by linarith); positivity
    have hneg := prime_sum_upper b hb a ha0 ha1 (fun x => -f x)
      (by obtain ⟨C, hC⟩ := hbd; exact ⟨C, fun x hx => by simpa using hC x hx⟩)
      (hcont.mono (fun x hx => hx.neg)) hint.neg ε hε0
    filter_upwards [hneg] with y hy
    simp only [mul_neg, Finset.sum_neg_distrib, MeasureTheory.integral_neg] at hy
    have : ε * (2 + V) < L - t := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  · intro t ht
    set ε := (t - L) / (2 * (2 + V)) with hε
    have hε0 : 0 < ε := by rw [hε]; apply div_pos (by linarith); positivity
    have hpos := prime_sum_upper b hb a ha0 ha1 f hbd hcont hint ε hε0
    filter_upwards [hpos] with y hy
    have : ε * (2 + V) < t - L := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith

end Palprimes.MT
