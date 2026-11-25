import KappaOmega2.Items.M02_P

/-! # M02 helpers (copied from S08, renamed), part S: step functions, piece integrals, the prime-sum limit `S(s) → Â(s)`. -/

namespace KappaOmega2

open Finset Palprimes MeasureTheory

set_option linter.style.longLine false

lemma m02_foldl (u : ℝ) (l : List (ℚ × ℚ)) (acc : ℝ) :
    l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) acc =
      if (∃ pr ∈ l, (pr.1 : ℝ) ≤ u) then l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) 0
      else acc := by
  classical
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (if (a.1 : ℝ) ≤ u then (a.2 : ℝ) else 0)]
    by_cases h : ∃ pr ∈ l, (pr.1 : ℝ) ≤ u
    · have h' : ∃ pr ∈ a :: l, (pr.1 : ℝ) ≤ u := by
        obtain ⟨pr, hpr, h2⟩ := h; exact ⟨pr, List.mem_cons_of_mem _ hpr, h2⟩
      rw [if_pos h, if_pos h', if_pos h]
    · rw [if_neg h, if_neg h]
      by_cases ha : (a.1 : ℝ) ≤ u
      · have h' : ∃ pr ∈ a :: l, (pr.1 : ℝ) ≤ u := ⟨a, List.mem_cons_self, ha⟩
        rw [if_pos h', if_pos ha, if_pos ha]
      · have h' : ¬ ∃ pr ∈ a :: l, (pr.1 : ℝ) ≤ u := by
          rintro ⟨pr, hpr, h2⟩
          rcases List.mem_cons.1 hpr with rfl | hpr'
          · exact ha h2
          · exact h ⟨pr, hpr', h2⟩
        rw [if_neg h', if_neg ha]

/-- `η̂ = piece + rest` (no sortedness needed). -/
lemma m02_eval_cons (pr : ℚ × ℚ) (rest : StepFn) (u : ℝ) :
    StepFn.eval (pr :: rest) u =
      (if (pr.1 : ℝ) ≤ u ∧ ∀ pr' ∈ rest, u < (pr'.1 : ℝ) then (pr.2 : ℝ) else 0) + StepFn.eval rest u := by
  classical
  unfold StepFn.eval
  simp only [List.foldl_cons]
  rw [m02_foldl u rest, m02_foldl u rest 0]
  by_cases h : ∃ pr' ∈ rest, (pr'.1 : ℝ) ≤ u
  · rw [if_pos h, if_pos h, if_neg]
    · ring
    · rintro ⟨_, h2⟩
      obtain ⟨pr', hpr', h3⟩ := h
      exact absurd (h2 pr' hpr') (not_lt.2 h3)
  · rw [if_neg h, if_neg h, add_zero]
    push_neg at h
    by_cases ha : (pr.1 : ℝ) ≤ u
    · rw [if_pos ha, if_pos ⟨ha, h⟩]
    · rw [if_neg ha, if_neg (fun h' => ha h'.1)]

/-- `min(2, left ends of rest)`. -/
noncomputable def m02mL (rest : StepFn) : ℝ := (rest.map (fun pr => (pr.1 : ℝ))).foldr min 2

lemma m02_mL_iff (rest : StepFn) (u : ℝ) (hu : u < 2) : (∀ pr' ∈ rest, u < (pr'.1 : ℝ)) ↔ u < m02mL rest := by
  unfold m02mL
  induction rest with
  | nil => simp [hu]
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, List.mem_cons, forall_eq_or_imp, lt_min_iff]
    rw [ih]

lemma m02_meas_forall (rest : StepFn) : MeasurableSet {v : ℝ | ∀ pr' ∈ rest, v < (pr'.1 : ℝ)} := by
  induction rest with
  | nil => simp
  | cons a l ih =>
    have : {v : ℝ | ∀ pr' ∈ a :: l, v < (pr'.1 : ℝ)} = Set.Iio (a.1 : ℝ) ∩ {v : ℝ | ∀ pr' ∈ l, v < (pr'.1 : ℝ)} := by
      ext v; simp
    rw [this]; exact measurableSet_Iio.inter ih

lemma m02_eval_meas (e : StepFn) : Measurable (fun v => StepFn.eval e v) := by
  classical
  induction e with
  | nil => simp only [StepFn.eval, List.foldl_nil]; exact measurable_const
  | cons pr rest ih =>
    have : (fun v => StepFn.eval (pr :: rest) v) = fun v =>
        (if (pr.1 : ℝ) ≤ v ∧ ∀ pr' ∈ rest, v < (pr'.1 : ℝ) then (pr.2 : ℝ) else 0) + StepFn.eval rest v := by
      funext v; exact m02_eval_cons pr rest v
    rw [this]
    apply Measurable.add _ ih
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_Ici (a := (pr.1 : ℝ))).inter (m02_meas_forall rest)

/-- General integrability: bounded measurable `F` vanishing below `a > 0`. -/
lemma m02_intble (F : ℝ → ℝ) (hF : Measurable F) (M a s : ℝ) (hM : ∀ v, |F v| ≤ M) (ha : 0 < a)
    (h0 : ∀ v, v < a → F v = 0) (hs : 0 ≤ s) :
    IntervalIntegrable (fun v => F v * (s - v) / v) volume 0 s := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  apply IntervalIntegrable.mono_fun' (g := fun _ => M * (s / a + 1)) intervalIntegrable_const
  · exact ((hF.mul (measurable_const.sub measurable_id)).div measurable_id).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    apply Filter.Eventually.of_forall
    intro v hv
    rw [Set.uIoc_of_le hs, Set.mem_Ioc] at hv
    simp only [Real.norm_eq_abs]
    by_cases hva : v < a
    · rw [h0 v hva]; simp only [zero_mul, zero_div, abs_zero]; positivity
    · push_neg at hva
      have hv0 : 0 < v := hv.1
      rw [abs_div, abs_mul, abs_of_pos hv0]
      have h1 : |s - v| ≤ s + v := by rw [abs_le]; constructor <;> linarith
      have h2 : |F v| * |s - v| ≤ M * (s + v) := mul_le_mul (hM v) h1 (abs_nonneg _) hM0
      rw [div_le_iff₀ hv0]
      have h3 : s / a * v ≥ s := by
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ ha]; nlinarith
      nlinarith

/-- The piece integral. -/
lemma m02_int_piece (a m s : ℝ) (ha : 0 < a) (hs : 0 ≤ s) :
    ∫ v in (0 : ℝ)..s, (if a ≤ v ∧ v < m then (1 : ℝ) else 0) * (s - v) / v = m02Ip a m s := by
  classical
  unfold m02Ip
  set m' := min m s with hm'
  split_ifs with ham
  swap
  · have hz : ∫ v in (0 : ℝ)..s, (if a ≤ v ∧ v < m then (1 : ℝ) else 0) * (s - v) / v =
        ∫ v in (0 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le hs, Set.mem_Icc] at hv
      simp only
      split_ifs with h
      · push_neg at ham
        have : v = s := by
          rcases le_total m s with hms | hms
          · rw [hm', min_eq_left hms] at ham; linarith [h.2]
          · rw [hm', min_eq_right hms] at ham; linarith [h.1]
        rw [this]; ring
      · ring
    rw [hz]; simp
  have hm's : m' ≤ s := min_le_right _ _
  have hm'm : m' ≤ m := min_le_left _ _
  -- a.e. equal to the indicator of `(a, m']`
  have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc (0 : ℝ) s →
      (if a ≤ v ∧ v < m then (1 : ℝ) else 0) * (s - v) / v = Set.indicator (Set.Ioc a m') (fun v => (s - v) / v) v := by
    have h1 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ a := by
      rw [ae_iff]; simp [measure_singleton]
    have h2 : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ m := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [h1, h2] with v hva hvm hv
    rw [Set.uIoc_of_le hs, Set.mem_Ioc] at hv
    simp only [Set.indicator, Set.mem_Ioc]
    split_ifs with hA hB hB
    · ring
    · exfalso; apply hB
      refine ⟨lt_of_le_of_ne hA.1 (Ne.symm hva), le_min hA.2.le hv.2⟩
    · exfalso
      have : v < m := lt_of_le_of_ne (le_trans hB.2 hm'm) hvm
      exact hA ⟨hB.1.le, this⟩
    · ring
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_of_le hs,
    setIntegral_indicator measurableSet_Ioc]
  have hsub : Set.Ioc (0 : ℝ) s ∩ Set.Ioc a m' = Set.Ioc a m' := by
    apply Set.inter_eq_right.2
    intro v hv; rw [Set.mem_Ioc] at hv ⊢; exact ⟨by linarith [hv.1], le_trans hv.2 hm's⟩
  rw [hsub, ← intervalIntegral.integral_of_le ham.le]
  have hpos : ∀ v ∈ Set.uIcc a m', 0 < v := by
    intro v hv; rw [Set.uIcc_of_le ham.le, Set.mem_Icc] at hv; linarith
  have hcongr : ∫ v in a..m', (s - v) / v = ∫ v in a..m', (s * v⁻¹ - 1) := by
    apply intervalIntegral.integral_congr
    intro v hv
    have := hpos v hv
    simp only; field_simp
  have h0 : (0 : ℝ) ∉ Set.uIcc a m' := fun h => lt_irrefl 0 (hpos 0 h)
  rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_inv h0,
    intervalIntegral.integral_const, Real.log_div (by linarith) ha.ne']
  · simp
  · exact (intervalIntegral.intervalIntegrable_inv (fun v hv => (hpos v hv).ne') continuousOn_id).const_mul s
  · exact intervalIntegrable_const

/-! ### Bounds on step functions (copies of the S09 helpers) -/

lemma m02_foldl2 (u : ℝ) (l : List (ℚ × ℚ)) (acc : ℝ) :
    l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) acc = acc ∨
      ∃ pr ∈ l, (pr.1 : ℝ) ≤ u ∧
        l.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) acc = (pr.2 : ℝ) := by
  induction l generalizing acc with
  | nil => left; rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases ih (if (a.1 : ℝ) ≤ u then (a.2 : ℝ) else acc) with h | ⟨pr, hpr, h1, h2⟩
    · by_cases ha : (a.1 : ℝ) ≤ u
      · right; exact ⟨a, List.mem_cons_self, ha, by rw [h]; simp [ha]⟩
      · left; rw [h]; simp [ha]
    · right; exact ⟨pr, List.mem_cons_of_mem _ hpr, h1, h2⟩

lemma m02_eval_cases (e : StepFn) (u : ℝ) :
    StepFn.eval e u = 0 ∨ ∃ pr ∈ e, (pr.1 : ℝ) ≤ u ∧ StepFn.eval e u = (pr.2 : ℝ) := by
  unfold StepFn.eval
  exact m02_foldl2 u e 0

noncomputable def m02Mv (e : StepFn) : ℝ := (e.map (fun pr => |(pr.2 : ℝ)|)).sum

noncomputable def m02u0 (e : StepFn) : ℝ := (e.map (fun pr => (pr.1 : ℝ))).foldr min 1

lemma m02_u0_pos (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) : 0 < m02u0 e := by
  unfold m02u0
  have : ∀ l : List (ℚ × ℚ), (∀ pr ∈ l, (0 : ℚ) < pr.1) → 0 < (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      exact lt_min (by exact_mod_cast h a List.mem_cons_self) (ih (fun pr hpr => h pr (List.mem_cons_of_mem _ hpr)))
  exact this e he

lemma m02_u0_le (e : StepFn) (pr : ℚ × ℚ) (hpr : pr ∈ e) : m02u0 e ≤ (pr.1 : ℝ) := by
  unfold m02u0
  have : ∀ l : List (ℚ × ℚ), pr ∈ l → (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 ≤ (pr.1 : ℝ) := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons a l ih =>
      intro h
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h')
  exact this e hpr

lemma m02_Mv_nonneg (e : StepFn) : 0 ≤ m02Mv e :=
  List.sum_nonneg (by intro x hx; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _)

lemma m02_eval_abs (e : StepFn) (u : ℝ) : |StepFn.eval e u| ≤ m02Mv e := by
  rcases m02_eval_cases e u with h | ⟨pr, hpr, _, h⟩
  · rw [h]; simpa using m02_Mv_nonneg e
  · rw [h]
    unfold m02Mv
    apply List.single_le_sum (l := e.map (fun pr => |(pr.2 : ℝ)|))
    · intro x hx; obtain ⟨pr, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    · exact List.mem_map.2 ⟨pr, hpr, rfl⟩

lemma m02_eval_zero (e : StepFn) (u : ℝ) (hu : u < m02u0 e) : StepFn.eval e u = 0 := by
  rcases m02_eval_cases e u with h0 | ⟨pr, hpr, h1, _⟩
  · exact h0
  · exact absurd (lt_of_le_of_lt (m02_u0_le e pr hpr) (lt_of_le_of_lt h1 hu)) (lt_irrefl _)

lemma m02_eval_intble (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) (s : ℝ) (hs : 0 ≤ s) :
    IntervalIntegrable (fun v => StepFn.eval e v * (s - v) / v) volume 0 s :=
  m02_intble _ (m02_eval_meas e) (m02Mv e) (m02u0 e) s (m02_eval_abs e) (m02_u0_pos e he)
    (fun v hv => m02_eval_zero e v hv) hs

lemma m02_u_lt_one (z : ℝ) (hz : 1 < z) (p : ℕ) (hp : p ∈ m02Pz z) : m02u z p < 1 := by
  unfold m02Pz at hp
  rw [Finset.mem_filter, m02_mem_ltSet] at hp
  unfold m02u
  have hL : 0 < Real.log z := Real.log_pos hz
  rw [div_lt_one hL]
  exact Real.log_lt_log (by exact_mod_cast hp.2.pos) hp.1.2

/-- **Prime sums of step functions** (uniform in `s ∈ [0, 1]`): `S(s) → Â(s)`. -/
theorem m02_PS (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z : ℝ, 1 < z → K ≤ Real.log z →
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * max (s - m02u z p) 0 -
        ∫ v in (0 : ℝ)..s, StepFn.eval e v * (s - v) / v| ≤ ε := by
  classical
  induction e with
  | nil =>
    intro ε hε
    refine ⟨0, fun z _ _ s _ _ => ?_⟩
    simp only [StepFn.eval, List.foldl_nil, mul_zero, zero_mul, zero_div, Finset.sum_const_zero,
      intervalIntegral.integral_zero, sub_zero, abs_zero]
    exact hε.le
  | cons pr rest ih =>
    intro ε hε
    have hpr : (0 : ℚ) < pr.1 := he pr List.mem_cons_self
    have hrest : ∀ pr' ∈ rest, (0 : ℚ) < pr'.1 := fun pr' h => he pr' (List.mem_cons_of_mem _ h)
    have ha : (0 : ℝ) < pr.1 := by exact_mod_cast hpr
    set a : ℝ := (pr.1 : ℝ) with hadef
    set c : ℝ := (pr.2 : ℝ) with hcdef
    set mL := m02mL rest
    obtain ⟨C, hC0, hC⟩ := m02_piece a mL ha
    obtain ⟨K1, hK1⟩ := ih hrest (ε / 2) (by linarith)
    refine ⟨max K1 (max (Real.log 4 / a) (2 * (|c| * C + 1) / ε)), ?_⟩
    intro z hz hK s hs0 hs1
    have hL : 0 < Real.log z := Real.log_pos hz
    have hK1' : K1 ≤ Real.log z := le_trans (le_max_left _ _) hK
    have h4 : Real.log 4 ≤ a * Real.log z := by
      have : Real.log 4 / a ≤ Real.log z := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
      rw [div_le_iff₀ ha] at this; linarith
    have hKc : 2 * (|c| * C + 1) / ε ≤ Real.log z := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
    -- pieces
    set ind : ℝ → ℝ := fun u => if a ≤ u ∧ u < mL then 1 else 0 with hind
    have hsum : ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval (pr :: rest) (m02u z p) * max (s - m02u z p) 0 =
        c * ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * max (s - m02u z p) 0 +
          ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval rest (m02u z p) * max (s - m02u z p) 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hu2 : m02u z p < 2 := by linarith [m02_u_lt_one z hz p hp]
      rw [m02_eval_cons]
      simp only [m02_mL_iff rest _ hu2, hind]
      split_ifs <;> ring
    have hint : ∫ v in (0 : ℝ)..s, StepFn.eval (pr :: rest) v * (s - v) / v =
        c * m02Ip a mL s + ∫ v in (0 : ℝ)..s, StepFn.eval rest v * (s - v) / v := by
      have hcongr : ∫ v in (0 : ℝ)..s, StepFn.eval (pr :: rest) v * (s - v) / v =
          ∫ v in (0 : ℝ)..s, (c * (ind v * (s - v) / v) + StepFn.eval rest v * (s - v) / v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hs0, Set.mem_Icc] at hv
        have hv2 : v < 2 := by linarith
        simp only
        rw [m02_eval_cons]
        simp only [m02_mL_iff rest _ hv2, hind]
        split_ifs <;> ring
      have hpi : IntervalIntegrable (fun v => ind v * (s - v) / v) volume 0 s := by
        apply m02_intble ind _ 1 a s _ ha _ hs0
        · exact Measurable.ite (measurableSet_Ici.inter measurableSet_Iio) measurable_const measurable_const
        · intro v; simp only [hind]; split_ifs <;> simp
        · intro v hv; simp only [hind]; rw [if_neg]; intro h; linarith [h.1]
      rw [hcongr, intervalIntegral.integral_add (hpi.const_mul c) (m02_eval_intble rest hrest s hs0),
        intervalIntegral.integral_const_mul]
      congr 2
      exact m02_int_piece a mL s ha hs0
    rw [hsum, hint]
    have hp := hC z hz h4 s hs0 hs1
    have hr := hK1 z hz hK1' s hs0 hs1
    have hcC : |c| * (C / Real.log z) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hL]
      rw [div_le_iff₀ hε] at hKc
      nlinarith [abs_nonneg c]
    calc _ = |c * (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * ind (m02u z p) * max (s - m02u z p) 0 - m02Ip a mL s) +
          (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval rest (m02u z p) * max (s - m02u z p) 0 -
            ∫ v in (0 : ℝ)..s, StepFn.eval rest v * (s - v) / v)| := by ring_nf
      _ ≤ |c| * (C / Real.log z) + ε / 2 := by
          refine le_trans (abs_add_le _ _) (add_le_add ?_ hr)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ ε := by linarith

end KappaOmega2
