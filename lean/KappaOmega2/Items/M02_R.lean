import KappaOmega2.Items.M02_D

/-! # M02 helpers, part R: Riemann sums over primes, `Σ_{a ≤ u_p < b} F(u_p)/p → ∫_a^b F(v)/v dv`. -/

namespace KappaOmega2

open Finset Palprimes MeasureTheory

set_option linter.style.longLine false

/-- Splitting `[a, t')` at `t`. -/
lemma m02_split (z : ℝ) (f : ℕ → ℝ) (a t t' : ℝ) (ht : t ≤ t') :
    ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < t'), f p =
      ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < t), f p +
        ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ t ≤ m02u z p ∧ m02u z p < t'), f p := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => m02u z p < t)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, lt_of_lt_of_le h3 ht⟩, h3⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h4, h3⟩
    · rintro ⟨h1, h2, h4, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩

/-- **Riemann lemma** on `[a, b] ⊂ (0, 1]`. -/
theorem m02_riemann (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc a b)) : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ z : ℝ, 1 < z → K ≤ Real.log z →
      |∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b), (1 / (p : ℝ)) * F (m02u z p) -
        ∫ v in a..b, F v / v| ≤ ε := by
  classical
  intro ε hε
  obtain ⟨C2, hC2, hM2⟩ := m02_mertens2
  obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hF
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf a ⟨le_rfl, hab.le⟩)
  set Lab := Real.log (b / a) with hLab
  have hLab0 : 0 ≤ Lab := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  set ω := ε / (4 * (Lab + 1)) with hω
  have hω0 : 0 < ω := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := a) (b := b)).uniformContinuousOn_of_continuous hF) ω hω0
  set N : ℕ := ⌈(b - a) / δ⌉₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  set h := (b - a) / N with hh
  have hh0 : 0 < h := div_pos (by linarith) hNr
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hNr]
    have h1 : (b - a) / δ ≤ ⌈(b - a) / δ⌉₊ := Nat.le_ceil _
    have h2 : (⌈(b - a) / δ⌉₊ : ℝ) < N := by rw [hN]; push_cast; linarith
    rw [div_le_iff₀ hδ0] at h1
    nlinarith
  set t : ℕ → ℝ := fun i => a + i * h with ht
  have ht0 : t 0 = a := by simp [ht]
  have htN : t N = b := by simp only [ht, hh]; field_simp; ring
  have htmono : ∀ i, t i ≤ t (i + 1) := fun i => by simp only [ht]; push_cast; nlinarith
  have hta : ∀ i, a ≤ t i := fun i => by
    have : (0 : ℝ) ≤ i * h := mul_nonneg (Nat.cast_nonneg i) hh0.le
    simp only [ht]; linarith
  have htb : ∀ i ≤ N, t i ≤ b := by
    intro i hi
    rw [← htN]; simp only [ht]
    have : (i : ℝ) ≤ N := by exact_mod_cast hi
    nlinarith
  refine ⟨max (Real.log 4 / a) (max (C2 / a) (2 * N * (Mf + 1) * C2 / (a * ε) + 1)), ?_⟩
  intro z hz hK
  have hL : 0 < Real.log z := Real.log_pos hz
  have hz0 : 0 < z := by linarith
  set L := Real.log z with hLdef
  have h4 : Real.log 4 ≤ a * L := by
    have := le_trans (le_max_left _ _) hK; rw [div_le_iff₀ ha] at this; linarith
  have hC2L : C2 ≤ a * L := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK; rw [div_le_iff₀ ha] at this; linarith
  have hNL : 2 * N * (Mf + 1) * C2 / (a * ε) ≤ L := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK; linarith
  -- Mertens on a cell `[s, s')`, `a ≤ s ≤ s' ≤ 1`
  have hcell : ∀ s s' : ℝ, a ≤ s → s ≤ s' → s' ≤ 1 →
      |∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ s ≤ m02u z p ∧ m02u z p < s'), (1 : ℝ) / p -
        (Real.log s' - Real.log s)| ≤ C2 / (a * L) := by
    intro s s' has hss' hs'1
    have hs0 : 0 < s := lt_of_lt_of_le ha has
    have hfe : (m02Pz z).filter (fun p => a ≤ m02u z p ∧ s ≤ m02u z p ∧ m02u z p < s') =
        (m02Pz z).filter (fun p => s ≤ m02u z p ∧ m02u z p < s') := by
      apply Finset.filter_congr; intro p _
      constructor
      · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨le_trans has h2, h2, h3⟩
    rw [hfe]
    have hmem := m02_mem_set z hz s s' hs'1
    have hA4 : 4 ≤ z ^ s := by
      rw [Real.rpow_def_of_pos hz0, ← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_right has hL.le
      linarith
    have hAT : z ^ s ≤ z ^ s' := Real.rpow_le_rpow_of_exponent_le hz.le hss'
    have m2 := hM2 _ (z ^ s) (z ^ s') hA4 hAT (fun p hp => (hmem p).1 hp) (fun p h1 h2 h3 => (hmem p).2 ⟨h1, h2, h3⟩)
    rw [Real.log_rpow hz0, Real.log_rpow hz0, Real.log_mul (by linarith) hL.ne',
      Real.log_mul hs0.ne' hL.ne'] at m2
    have : C2 / (s * L) ≤ C2 / (a * L) :=
      div_le_div_of_nonneg_left hC2 (by positivity) (mul_le_mul_of_nonneg_right has hL.le)
    have e : Real.log s' + Real.log L - (Real.log s + Real.log L) = Real.log s' - Real.log s := by ring
    rw [e] at m2; linarith
  -- decomposition into cells
  set cell : ℕ → Finset ℕ := fun i =>
    (m02Pz z).filter (fun p => a ≤ m02u z p ∧ t i ≤ m02u z p ∧ m02u z p < t (i + 1)) with hcelldef
  have hdec : ∀ f : ℕ → ℝ, ∀ n ≤ N, ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < t n), f p =
      ∑ i ∈ range n, ∑ p ∈ cell i, f p := by
    intro f n
    induction n with
    | zero =>
      intro _
      rw [Finset.range_zero, Finset.sum_empty, ht0]
      apply Finset.sum_eq_zero; intro p hp
      rw [Finset.mem_filter] at hp; exact absurd (lt_of_le_of_lt hp.2.1 hp.2.2) (lt_irrefl _)
    | succ n ih =>
      intro hn
      rw [m02_split z f a (t n) (t (n + 1)) (htmono n), ih (by omega), Finset.sum_range_succ]
  -- integrals
  have hint : ∀ i < N, IntervalIntegrable (fun v => F v / v) volume (t i) (t (i + 1)) := by
    intro i hi
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (htmono i)]
    apply ContinuousOn.div (hF.mono _) continuousOn_id
    · intro v hv; exact (lt_of_lt_of_le ha (le_trans (hta i) hv.1)).ne'
    · intro v hv; exact ⟨le_trans (hta i) hv.1, le_trans hv.2 (htb (i + 1) (by omega))⟩
  have hIsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [ht0, htN] at hIsum
  have hPsum := hdec (fun p => (1 / (p : ℝ)) * F (m02u z p)) N le_rfl
  have hPsum1 := hdec (fun p => (1 : ℝ) / p) N le_rfl
  rw [htN] at hPsum hPsum1
  rw [hPsum, ← hIsum, ← Finset.sum_sub_distrib]
  -- per cell
  have hper : ∀ i < N, |∑ p ∈ cell i, (1 / (p : ℝ)) * F (m02u z p) - ∫ v in t i..t (i + 1), F v / v| ≤
      ω * ∑ p ∈ cell i, (1 : ℝ) / p + Mf * (C2 / (a * L)) + ω * (Real.log (t (i + 1)) - Real.log (t i)) := by
    intro i hi
    have hti : t i ∈ Set.Icc a b := ⟨hta i, htb i (by omega)⟩
    have hti1 : t (i + 1) ≤ b := htb (i + 1) (by omega)
    have htipos : 0 < t i := lt_of_lt_of_le ha (hta i)
    set Fi := F (t i)
    have hFi : |Fi| ≤ Mf := by have := hMf (t i) hti; rwa [Real.norm_eq_abs] at this
    -- prime side
    have hX : |∑ p ∈ cell i, (1 / (p : ℝ)) * F (m02u z p) - Fi * ∑ p ∈ cell i, (1 : ℝ) / p| ≤
        ω * ∑ p ∈ cell i, (1 : ℝ) / p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro p hp
      simp only [hcelldef, Finset.mem_filter] at hp
      have hpos : (0 : ℝ) ≤ 1 / p := by positivity
      have hu : m02u z p ∈ Set.Icc a b := ⟨hp.2.1, le_trans hp.2.2.2.le hti1⟩
      have hd : dist (m02u z p) (t i) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hp.2.2.1])]
        have : t (i + 1) - t i = h := by simp only [ht]; push_cast; ring
        linarith [hp.2.2.2]
      have hF' := hδ _ hu _ hti hd
      rw [Real.dist_eq] at hF'
      have e : 1 / (p : ℝ) * F (m02u z p) - Fi * (1 / p) = (1 / p) * (F (m02u z p) - Fi) := by ring
      rw [e, abs_mul, abs_of_nonneg hpos]
      rw [mul_comm ω]
      exact mul_le_mul_of_nonneg_left hF'.le hpos
    have hY := hcell (t i) (t (i + 1)) (hta i) (htmono i) (le_trans hti1 hb1)
    have hY' : |Fi * ∑ p ∈ cell i, (1 : ℝ) / p - Fi * (Real.log (t (i + 1)) - Real.log (t i))| ≤ Mf * (C2 / (a * L)) := by
      rw [← mul_sub, abs_mul]; exact mul_le_mul hFi hY (abs_nonneg _) hMf0
    -- integral side
    have hpos' : ∀ v ∈ Set.uIcc (t i) (t (i + 1)), 0 < v := by
      intro v hv; rw [Set.uIcc_of_le (htmono i)] at hv; linarith [hv.1]
    have h0 : (0 : ℝ) ∉ Set.uIcc (t i) (t (i + 1)) := fun h => lt_irrefl 0 (hpos' 0 h)
    have hinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume (t i) (t (i + 1)) :=
      intervalIntegral.intervalIntegrable_inv (fun v hv => (hpos' v hv).ne') continuousOn_id
    have hconst : ∫ v in t i..t (i + 1), Fi / v = Fi * (Real.log (t (i + 1)) - Real.log (t i)) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv h0, Real.log_div (by have := htmono i; linarith : (0:ℝ) < t (i + 1)).ne' htipos.ne']
    have hdiff : |(∫ v in t i..t (i + 1), F v / v) - ∫ v in t i..t (i + 1), Fi / v| ≤
        ω * (Real.log (t (i + 1)) - Real.log (t i)) := by
      have hFint : IntervalIntegrable (fun v : ℝ => Fi / v) volume (t i) (t (i + 1)) := by
        simpa [div_eq_mul_inv] using hinv.const_mul Fi
      have hsub := intervalIntegral.integral_sub (hint i hi) hFint
      rw [← hsub]
      have hgi : IntervalIntegrable (fun v => F v / v - Fi / v) volume (t i) (t (i + 1)) := (hint i hi).sub hFint
      have hωi : IntervalIntegrable (fun v : ℝ => ω / v) volume (t i) (t (i + 1)) := by
        simpa [div_eq_mul_inv] using hinv.const_mul ω
      have hωint : ∫ v in t i..t (i + 1), ω / v = ω * (Real.log (t (i + 1)) - Real.log (t i)) := by
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_const_mul, integral_inv h0, Real.log_div (by have := htmono i; linarith : (0:ℝ) < t (i + 1)).ne' htipos.ne']
      have hb : ∀ v ∈ Set.Icc (t i) (t (i + 1)), |F v / v - Fi / v| ≤ ω / v := by
        intro v hv
        have hv0 : 0 < v := by linarith [hv.1]
        have hvab : v ∈ Set.Icc a b := ⟨le_trans (hta i) hv.1, le_trans hv.2 hti1⟩
        have hd : dist v (t i) < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.1])]
          have : t (i + 1) - t i = h := by simp only [ht]; push_cast; ring
          linarith [hv.2]
        have hF' := hδ _ hvab _ hti hd
        rw [Real.dist_eq] at hF'
        rw [← sub_div, abs_div, abs_of_pos hv0]
        exact div_le_div_of_nonneg_right hF'.le hv0.le
      rw [abs_le]
      constructor
      · have := intervalIntegral.integral_mono_on (htmono i) hωi.neg hgi (fun v hv => by
          have := hb v hv; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith [this.1])
        simp only [Pi.neg_apply] at this
        rw [intervalIntegral.integral_neg, hωint] at this; linarith
      · have := intervalIntegral.integral_mono_on (htmono i) hgi hωi (fun v hv => by
          have := hb v hv; rw [abs_le] at this; linarith [this.2])
        rw [hωint] at this; linarith
    rw [hconst] at hdiff
    set X := ∑ p ∈ cell i, (1 / (p : ℝ)) * F (m02u z p)
    set Y := ∑ p ∈ cell i, (1 : ℝ) / p
    set D := Real.log (t (i + 1)) - Real.log (t i)
    have e : X - ∫ v in t i..t (i + 1), F v / v = (X - Fi * Y) + (Fi * Y - Fi * D) -
        ((∫ v in t i..t (i + 1), F v / v) - Fi * D) := by ring
    rw [e]
    refine le_trans (abs_sub _ _) ?_
    exact add_le_add (le_trans (abs_add_le _ _) (add_le_add hX hY')) hdiff
  calc _ ≤ ∑ i ∈ range N, |∑ p ∈ cell i, (1 / (p : ℝ)) * F (m02u z p) - ∫ v in t i..t (i + 1), F v / v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, (ω * ∑ p ∈ cell i, (1 : ℝ) / p + Mf * (C2 / (a * L)) +
          ω * (Real.log (t (i + 1)) - Real.log (t i))) :=
        Finset.sum_le_sum (fun i hi => hper i (Finset.mem_range.1 hi))
    _ = ω * ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b), (1 : ℝ) / p + N * (Mf * (C2 / (a * L))) +
          ω * (Real.log b - Real.log a) := by
        have hA : ∑ i ∈ range N, ω * ∑ p ∈ cell i, (1 : ℝ) / p =
            ω * ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b), (1 : ℝ) / p := by
          rw [← Finset.mul_sum, hPsum1]
        have hB : ∑ i ∈ range N, Mf * (C2 / (a * L)) = N * (Mf * (C2 / (a * L))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hC : ∑ i ∈ range N, ω * (Real.log (t (i + 1)) - Real.log (t i)) = ω * (Real.log b - Real.log a) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => Real.log (t i)), ht0, htN]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC]
    _ ≤ ε := by
        have hPb := hcell a b le_rfl hab.le hb1
        have hfe : (m02Pz z).filter (fun p => a ≤ m02u z p ∧ a ≤ m02u z p ∧ m02u z p < b) =
            (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b) := by
          apply Finset.filter_congr; intro p _; tauto
        rw [hfe, abs_le] at hPb
        have hC : C2 / (a * L) ≤ 1 := by rw [div_le_one (by positivity)]; exact hC2L
        have hS : ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b), (1 : ℝ) / p ≤ Lab + 1 := by
          rw [hLab, Real.log_div (by linarith) ha.ne']; linarith
        have hlog : Real.log b - Real.log a = Lab := by rw [hLab, Real.log_div (by linarith) ha.ne']
        have hNM : N * (Mf * (C2 / (a * L))) ≤ ε / 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < a * ε)] at hNL
          have h1 : N * (Mf * (C2 / (a * L))) = N * Mf * C2 / (a * L) := by ring
          rw [h1, div_le_iff₀ (by positivity)]
          have : (N : ℝ) * Mf * C2 ≤ N * (Mf + 1) * C2 := by
            apply mul_le_mul_of_nonneg_right _ hC2; nlinarith
          nlinarith
        have hωe : ω * (Lab + 1) * 4 = ε := by rw [hω]; field_simp
        have : ω * ∑ p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b), (1 : ℝ) / p ≤ ω * (Lab + 1) :=
          mul_le_mul_of_nonneg_left hS hω0.le
        rw [hlog]
        nlinarith

end KappaOmega2
