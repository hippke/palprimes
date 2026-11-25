import Omega3.Statements

namespace Omega3

open Finset Complex Palprimes

open Finset Complex

lemma L01_count_pairs (m a : ℕ) :
    (∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then 1 else 0 : ℕ) = min (a + 1) (2 * m - 1 - a) := by
  have inner : ∀ i ∈ range m, (∑ j ∈ range m, if i + j = a then 1 else 0 : ℕ) =
      if (i ≤ a ∧ a < i + m) then 1 else 0 := by
    intro i _
    by_cases h : i ≤ a
    · have hj : ∀ j : ℕ, (i + j = a ↔ j = a - i) := fun j => by omega
      simp only [hj, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> omega
    · have hz : ∀ j ∈ range m, (if i + j = a then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (by omega)
      rw [Finset.sum_eq_zero hz, if_neg (by omega : ¬ (i ≤ a ∧ a < i + m))]
  rw [Finset.sum_congr rfl inner, ← Finset.card_filter]
  have hf : (range m).filter (fun i => i ≤ a ∧ a < i + m) =
      Finset.Ico (a + 1 - m) (min m (a + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, min_def, min_def]
  split_ifs <;> omega

lemma L01_sum_pairs {R : Type*} [CommSemiring R] (m : ℕ) (G : ℕ → R) :
    ∑ i ∈ range m, ∑ j ∈ range m, G (i + j) =
      ∑ a ∈ range (2 * m - 1), ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) * G a := by
  have hc : ∀ a : ℕ, ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) =
      ∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then (1 : R) else 0 := by
    intro a
    have h := congrArg (fun k : ℕ => (k : R)) (L01_count_pairs m a)
    push_cast at h
    exact h.symm
  have hL : ∀ i ∈ range m, ∀ j ∈ range m, G (i + j) =
      ∑ a ∈ range (2 * m - 1), if i + j = a then G a else 0 := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (show i + j < 2 * m - 1 by omega))]
  calc ∑ i ∈ range m, ∑ j ∈ range m, G (i + j)
      = ∑ i ∈ range m, ∑ a ∈ range (2 * m - 1), ∑ j ∈ range m, if i + j = a then G a else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j hj => hL i hi j hj)
    _ = ∑ a ∈ range (2 * m - 1), ∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then G a else 0 :=
        Finset.sum_comm
    _ = ∑ a ∈ range (2 * m - 1), ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) * G a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hc a, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [ite_mul, one_mul, zero_mul]

lemma L01_fejerW_cast (m a : ℕ) (ha : a < 2 * m - 1) :
    ((fejerW m a : ℚ) : ℂ) = ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℂ) * (((m : ℂ) ^ 2)⁻¹) := by
  have h : a + 1 < 2 * m := by omega
  unfold fejerW
  rw [if_pos h]
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  rfl

lemma L01_e_add (x z : ℝ) : ee (x + z) = ee x * ee z := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma L01_re_e_conj (x z : ℝ) :
    (ee x * (starRingEnd ℂ) (ee z)).re = Real.cos (2 * Real.pi * (x - z)) := by
  have h : ee x * (starRingEnd ℂ) (ee z) =
      Complex.exp (((2 * Real.pi * (x - z) : ℝ) : ℂ) * Complex.I) := by
    unfold ee
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

lemma L01_coeff_val (n a : ℕ) (ha : a < 2 * (n + 1) - 1) :
    ((min (a + 1) (2 * (n + 1) - 1 - a) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - |(a : ℝ) - n| := by
  rcases le_total a n with h | h
  · have hmin : min (a + 1) (2 * (n + 1) - 1 - a) = a + 1 := min_eq_left (by omega)
    have hr : (a : ℝ) ≤ n := by exact_mod_cast h
    rw [hmin, abs_of_nonpos (show (a : ℝ) - n ≤ 0 by linarith)]
    push_cast
    ring
  · have hmin : min (a + 1) (2 * (n + 1) - 1 - a) = 2 * (n + 1) - 1 - a := min_eq_right (by omega)
    have hr : (n : ℝ) ≤ a := by exact_mod_cast h
    have hs : ((2 * (n + 1) - 1 - a : ℕ) : ℝ) + a = 2 * n + 1 := by
      have : (2 * (n + 1) - 1 - a : ℕ) + a = 2 * n + 1 := by omega
      exact_mod_cast this
    rw [hmin, abs_of_nonneg (show (0 : ℝ) ≤ a - n by linarith)]
    push_cast at hs ⊢
    linarith

lemma L01_reindex_sum (n : ℕ) (y : ℝ) :
    ∑ a ∈ range (2 * (n + 1) - 1), ((min (a + 1) (2 * (n + 1) - 1 - a) : ℕ) : ℝ) *
        Real.cos (2 * Real.pi * ((a : ℝ) - n) * y)
      = ∑ k ∈ Finset.Ioo (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
          (((n + 1 : ℕ) : ℝ) - |(k : ℝ)|) * Real.cos (2 * Real.pi * (k : ℝ) * y) := by
  apply Finset.sum_nbij' (fun a : ℕ => (a : ℤ) - n) (fun k : ℤ => (k + n).toNat)
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioo] at ha ⊢
    omega
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_Ioo] at hk ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro k hk
    simp only [Finset.mem_Ioo] at hk
    omega
  · intro a ha
    have ha' : a < 2 * (n + 1) - 1 := Finset.mem_range.mp ha
    rw [L01_coeff_val n a ha']
    push_cast
    ring_nf

theorem itemL01 : ItemL01 := by
  unfold ItemL01 FejerAbsStmt
  intro m hm y
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set D : ℂ := ∑ j ∈ range (n + 1), ee ((j : ℝ) * y) with hD
  have hS1 : ∑ a ∈ range (2 * (n + 1) - 1), ((fejerW (n + 1) a : ℚ) : ℂ) * ee ((a : ℝ) * y)
      = (∑ a ∈ range (2 * (n + 1) - 1),
          ((min (a + 1) (2 * (n + 1) - 1 - a) : ℕ) : ℂ) * ee ((a : ℝ) * y))
        * (((n + 1 : ℕ) : ℂ) ^ 2)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [L01_fejerW_cast (n + 1) a (Finset.mem_range.mp ha)]
    ring
  have hS2 : ∑ a ∈ range (2 * (n + 1) - 1),
      ((min (a + 1) (2 * (n + 1) - 1 - a) : ℕ) : ℂ) * ee ((a : ℝ) * y)
      = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ee (((i + j : ℕ) : ℝ) * y) :=
    (L01_sum_pairs (R := ℂ) (n + 1) (fun a : ℕ => ee ((a : ℝ) * y))).symm
  have hDD : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), ee (((i + j : ℕ) : ℝ) * y) = D * D := by
    rw [hD, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← L01_e_add]
    congr 1
    push_cast
    ring
  have hnorm : ‖D * D * (((n + 1 : ℕ) : ℂ) ^ 2)⁻¹‖
      = Complex.normSq D * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, ← sq,
      ← Complex.normSq_eq_norm_sq]
  have hre : Complex.normSq D = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
      Real.cos (2 * Real.pi * ((i : ℝ) * y - (j : ℝ) * y)) := by
    have h2 : Complex.normSq D = (D * (starRingEnd ℂ) D).re := by
      rw [Complex.mul_conj]
      simp
    rw [h2, hD, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact L01_re_e_conj _ _
  have hR : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
      Real.cos (2 * Real.pi * ((i : ℝ) * y - (j : ℝ) * y))
      = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
          Real.cos (2 * Real.pi * (((i + j : ℕ) : ℝ) - n) * y) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hnat : n + 1 - 1 - j = n - j := by omega
    rw [hnat, Nat.cast_sub (show j ≤ n by omega)]
    congr 1
    push_cast
    ring
  have hG := L01_sum_pairs (R := ℝ) (n + 1) (fun a : ℕ => Real.cos (2 * Real.pi * ((a : ℝ) - n) * y))
  beta_reduce at hG
  rw [hS1, hS2, hDD, hnorm, hre, hR, hG, L01_reindex_sum n y]
  unfold fejerK
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hpos : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp


end Omega3
