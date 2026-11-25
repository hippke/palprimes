import KappaOmega2.Statements

namespace KappaOmega2

open Finset Real Palprimes

lemma l06_sumIoo_even (h : ℤ → ℝ) (hh : ∀ k, h (-k) = h k) (n : ℕ) :
    ∑ k ∈ Finset.Ioo (-((n:ℤ)+1)) ((n:ℤ)+1), h k = h 0 + 2 * ∑ u ∈ Finset.Icc 1 n, h (u:ℤ) := by
  induction n with
  | zero =>
    have e : Finset.Ioo (-1:ℤ) 1 = {0} := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_singleton]; omega
    simp [e]
  | succ n ih =>
    have e : Finset.Ioo (-(((n+1:ℕ):ℤ)+1)) (((n+1:ℕ):ℤ)+1)
        = insert (-((n:ℤ)+1)) (insert ((n:ℤ)+1) (Finset.Ioo (-((n:ℤ)+1)) ((n:ℤ)+1))) := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_insert]; push_cast; omega
    have hn1 : (-((n:ℤ)+1)) ∉ insert ((n:ℤ)+1) (Finset.Ioo (-((n:ℤ)+1)) ((n:ℤ)+1)) := by
      simp only [Finset.mem_insert, Finset.mem_Ioo, not_or]; omega
    have hn2 : ((n:ℤ)+1) ∉ Finset.Ioo (-((n:ℤ)+1)) ((n:ℤ)+1) := by
      simp only [Finset.mem_Ioo, not_and, not_lt]; omega
    rw [e, Finset.sum_insert hn1, Finset.sum_insert hn2, ih, Finset.sum_Icc_succ_top (by omega),
      hh ((n:ℤ)+1)]
    push_cast
    ring

lemma l06_gauss (n : ℕ) : 2 * ∑ u ∈ Finset.Icc 1 n, (u:ℝ) = (n:ℝ) * ((n:ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast; ring

lemma l06_fejTau_nonneg (n u : ℕ) (hu : u ∈ Finset.Icc 1 n) :
    0 ≤ fejTau (n+1) u ∧ fejTau (n+1) u = (((n:ℝ)+1) - u) / ((n:ℝ)+1)^2 := by
  rw [Finset.mem_Icc] at hu
  have hu0 : u ≠ 0 := by omega
  have hlt : u < n + 1 := by omega
  unfold fejTau
  simp only [hu0, ite_false, hlt, ite_true]
  have hu' : (u:ℝ) ≤ (n:ℝ) := by exact_mod_cast hu.2
  refine ⟨?_, ?_⟩
  · apply div_nonneg
    · push_cast; linarith
    · positivity
  · push_cast; ring

lemma l06_fejer_trig (n : ℕ) (y : ℝ) : fejerK (n+1) y = trigEval n (fejTau (n+1)) y := by
  unfold fejerK trigEval
  have hs := l06_sumIoo_even
    (fun k : ℤ => (1 - (|k| : ℝ) / (((n+1 : ℕ)) : ℝ)) * Real.cos (2 * Real.pi * k * y))
    (by intro k; simp [abs_neg, Real.cos_neg]) n
  push_cast at hs ⊢
  rw [hs]
  have hτ0 : fejTau (n+1) 0 = 1 / ((n:ℝ)+1) := by
    simp [fejTau]
  rw [hτ0]
  have hcongr : ∑ u ∈ Finset.Icc 1 n,
      (1 / ((n:ℝ)+1)) * ((1 - |(u:ℝ)| / ((n:ℝ)+1)) * Real.cos (2 * Real.pi * (u:ℝ) * y))
      = ∑ u ∈ Finset.Icc 1 n, fejTau (n+1) u * Real.cos (2 * Real.pi * (u:ℝ) * y) := by
    apply Finset.sum_congr rfl
    intro u hu
    obtain ⟨_, hτ⟩ := l06_fejTau_nonneg n u hu
    rw [hτ, Nat.abs_cast]
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    field_simp
  rw [mul_add]
  congr 1
  · simp
  · rw [mul_left_comm, Finset.mul_sum]
    try simp only [Int.cast_natCast] at hcongr ⊢
    rw [hcongr]



lemma l06_trig_fejer_le_one (n : ℕ) (y : ℝ) : trigEval n (fejTau (n+1)) y ≤ 1 := by
  unfold trigEval
  have hτ0 : fejTau (n+1) 0 = 1 / ((n:ℝ)+1) := by simp [fejTau]
  have hsum : ∑ u ∈ Finset.Icc 1 n, (((n:ℝ)+1) - (u:ℝ)) = (n:ℝ) * ((n:ℝ)+1) / 2 := by
    have := l06_gauss n
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    linarith
  have hτs : ∑ u ∈ Finset.Icc 1 n, fejTau (n+1) u = (n:ℝ) / (2 * ((n:ℝ)+1)) := by
    rw [Finset.sum_congr rfl (fun u hu => (l06_fejTau_nonneg n u hu).2), ← Finset.sum_div, hsum]
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    field_simp
  have hle : ∑ u ∈ Finset.Icc 1 n, fejTau (n+1) u * Real.cos (2 * Real.pi * (u:ℝ) * y)
      ≤ ∑ u ∈ Finset.Icc 1 n, fejTau (n+1) u := by
    apply Finset.sum_le_sum
    intro u hu
    have h1 := (l06_fejTau_nonneg n u hu).1
    have h2 := Real.cos_le_one (2 * Real.pi * (u:ℝ) * y)
    nlinarith
  have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h2S : 2 * ∑ u ∈ Finset.Icc 1 n, fejTau (n+1) u = (n:ℝ) / ((n:ℝ)+1) := by
    rw [hτs]; field_simp
  have hone : 1 / ((n:ℝ)+1) + (n:ℝ) / ((n:ℝ)+1) = 1 := by field_simp; ring
  rw [hτ0]
  linarith [hle, h2S, hone]

lemma l06_trig_affine (H : ℕ) (p c : ℝ) (f : ℕ → ℝ) (t : ℝ) :
    trigEval H (fun u => (if u = 0 then c else 0) + p * f u) t = c + p * trigEval H f t := by
  unfold trigEval
  have hs : ∑ u ∈ Finset.Icc 1 H, ((if u = 0 then c else 0) + p * f u) * Real.cos (2 * Real.pi * (u:ℝ) * t)
      = p * ∑ u ∈ Finset.Icc 1 H, f u * Real.cos (2 * Real.pi * (u:ℝ) * t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hu0 : u ≠ 0 := by rw [Finset.mem_Icc] at hu; omega
    rw [if_neg hu0, zero_add]
    ring
  simp only [↓reduceIte]
  rw [hs]
  ring

lemma l06_ee_norm (x : ℝ) : ‖ee x‖ = 1 := by
  have h : ee x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold ee; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma l06_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : ∀ a ∈ Finset.range b, 0 ≤ g a) (t : ℝ) :
    ‖Gg b g t‖ ≤ ∑ a ∈ Finset.range b, g a := by
  unfold Gg
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul, l06_ee_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hg a ha)]

lemma l06_recP_mem (b : ℕ) (hb : 5 ≤ b) : 0 ≤ recP b ∧ recP b ≤ 1 := by
  unfold recP
  have hb' : (5:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  split_ifs
  · norm_num
  · have h1 : 1 / (b:ℝ)^2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have h2 : 0 ≤ 1 / (b:ℝ)^2 := by positivity
    constructor <;> linarith

theorem itemL06 : ItemL06 := by
  intro hB hF hC6 hC8 b hb t
  obtain ⟨hp0, hp1⟩ := l06_recP_mem b hb
  have hnn : 0 ≤ ‖Gg b (recGR b) t‖ := norm_nonneg _
  by_cases h6 : b = 6
  · subst h6
    have hpos : ∀ a ∈ Finset.range 6, 0 ≤ recGR 6 a := by
      intro a ha
      rw [Finset.mem_range] at ha
      interval_cases a <;> norm_num [recGR, recG, g6list]
    have hsum : ∑ a ∈ Finset.range 6, recGR 6 a = 1 := by
      simp [Finset.sum_range_succ, recGR, recG, g6list]; norm_num
    have hG1 : ‖Gg 6 (recGR 6) t‖ ≤ 1 := by
      have := l06_Gg_norm_le 6 (recGR 6) hpos t
      linarith
    have hBer := hB ‖Gg 6 (recGR 6) t‖ (recP 6) hnn hG1 hp0 hp1
    have hC := hC6 t
    have hH : recH 6 = 3 := by simp [recH]
    have hτ : recTau 6 = fun u => (if u = 0 then 1 - recP 6 else 0) + recP 6 * (fun u => (P6list.getD u 0 : ℝ)) u := by
      funext u; simp [recTau, recPoly]
    have hRHS : trigEval (recH 6) (recTau 6) t
        = (1 - recP 6) + recP 6 * trigEval 3 (fun u => (P6list.getD u 0 : ℝ)) t := by
      rw [hH, hτ, l06_trig_affine]
    rw [hRHS]
    have := mul_le_mul_of_nonneg_left hC hp0
    linarith
  by_cases h8 : b = 8
  · subst h8
    have hpos : ∀ a ∈ Finset.range 8, 0 ≤ recGR 8 a := by
      intro a ha
      rw [Finset.mem_range] at ha
      interval_cases a <;> norm_num [recGR, recG, g8list]
    have hsum : ∑ a ∈ Finset.range 8, recGR 8 a = 1 := by
      simp [Finset.sum_range_succ, recGR, recG, g8list]; norm_num
    have hG1 : ‖Gg 8 (recGR 8) t‖ ≤ 1 := by
      have := l06_Gg_norm_le 8 (recGR 8) hpos t
      linarith
    have hBer := hB ‖Gg 8 (recGR 8) t‖ (recP 8) hnn hG1 hp0 hp1
    have hC := hC8 t
    have hH : recH 8 = 5 := by simp [recH]
    have hτ : recTau 8 = fun u => (if u = 0 then 1 - recP 8 else 0) + recP 8 * (fun u => (P8list.getD u 0 : ℝ)) u := by
      funext u; simp [recTau, recPoly]
    have hRHS : trigEval (recH 8) (recTau 8) t
        = (1 - recP 8) + recP 8 * trigEval 5 (fun u => (P8list.getD u 0 : ℝ)) t := by
      rw [hH, hτ, l06_trig_affine]
    rw [hRHS]
    have := mul_le_mul_of_nonneg_left hC hp0
    linarith
  -- Fejer case
  have hm1 : 1 ≤ mB b := by unfold mB; omega
  obtain ⟨n, hn⟩ : ∃ n, mB b = n + 1 := ⟨mB b - 1, by omega⟩
  have hterm : ∀ a, recGR b a = ((fejerW (mB b) a : ℚ) : ℝ) := by
    intro a; simp [recGR, recG, h6, h8]
  have hrange : Gg b (recGR b) t
      = ∑ a ∈ Finset.range (2 * mB b - 1), ((fejerW (mB b) a : ℚ) : ℂ) * ee (a * t) := by
    unfold Gg
    simp only [hterm]
    symm
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_range] at ha ⊢
      have : 2 * mB b ≤ b + 1 := by unfold mB; omega
      omega
    · intro a _ hna
      rw [Finset.mem_range] at hna
      have hz : fejerW (mB b) a = 0 := by
        unfold fejerW
        rw [if_neg (by omega)]
      simp [hz]
  have hFk := hF (mB b) hm1 t
  have hGT : ‖Gg b (recGR b) t‖ = trigEval n (fejTau (n+1)) t := by
    rw [hrange, hFk, hn, l06_fejer_trig]
  have hG1 : ‖Gg b (recGR b) t‖ ≤ 1 := by
    rw [hGT]; exact l06_trig_fejer_le_one n t
  have hBer := hB ‖Gg b (recGR b) t‖ (recP b) hnn hG1 hp0 hp1
  have hrec : recH b = n := by
    unfold recH
    rw [if_neg h6, if_neg h8]
    omega
  have hτ : recTau b = fun u => (if u = 0 then 1 - recP b else 0) + recP b * (fun u => fejTau (n+1) u) u := by
    funext u
    simp only [recTau, recPoly, if_neg h6, if_neg h8, hn]
  have hRHS : trigEval (recH b) (recTau b) t
      = (1 - recP b) + recP b * trigEval n (fejTau (n+1)) t := by
    rw [hrec, hτ, l06_trig_affine]
  rw [hRHS, hGT] 
  rw [hGT] at hBer
  exact hBer
