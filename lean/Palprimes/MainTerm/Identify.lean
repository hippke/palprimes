import Palprimes.MainTerm.Limit
import Palprimes.MainTerm.CoV
import Palprimes.MainTerm.Mval

/-! # Identification of the limit with `2e^γ 𝓜`

* `integral_split_last`, `integrable_split_last`: Fubini on the last coordinate;
* `strictAnti_snoc`, `RosX_snoc_iff` (`RosX` of a tuple ↔ Greaves' `RosserX`), `Gs_eq_Gr`. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Palprimes.MT

open Palprimes.Greaves

theorem snoc_eq_symm {n : ℕ} (t : ℝ) (v : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm (t, v) = Fin.snoc v t := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_last' t v

theorem integrable_split_last {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.snoc p.2 p.1)) (volume.prod volume) := by
  have hs := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have h := (hs.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := F)).2 hF
  rw [← Measure.volume_eq_prod]
  convert h using 1
  funext p
  rcases p with ⟨t, v⟩
  simp only [Function.comp, snoc_eq_symm]

theorem integral_split_last {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F) :
    (∫ x, F x) = ∫ t : ℝ, ∫ v : Fin n → ℝ, F (Fin.snoc v t) := by
  have hs := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have h := hs.integral_comp (MeasurableEquiv.measurableEmbedding _) F
  rw [← h, Measure.volume_eq_prod, integral_prod _ (by
    have := integrable_split_last F hF
    convert this using 1; funext p; rcases p with ⟨t, v⟩; simp only [snoc_eq_symm])]
  congr 1; funext t; congr 1; funext v
  rw [snoc_eq_symm]

theorem integrable_inner_last {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F) :
    Integrable (fun t : ℝ => ∫ v : Fin n → ℝ, F (Fin.snoc v t)) :=
  (integrable_split_last F hF).integral_prod_left

/-! ## Tuples with a last coordinate -/

theorem strictAnti_snoc {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    StrictAnti (Fin.snoc v t : Fin (n + 1) → ℝ) ↔ StrictAnti v ∧ ∀ i, t < v i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (Fin.castSucc_lt_castSucc_iff.2 hij)
      simpa using this
    · have := h (Fin.castSucc_lt_last i)
      simpa using this
  · rintro ⟨h1, h2⟩ a b hab
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]; exact h1 (Fin.castSucc_lt_castSucc_iff.1 hab)
      · exact absurd hab (not_lt.2 (Fin.le_last _))
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact h2 a'
      · exact absurd hab (lt_irrefl _)

theorem getD_ofFn_snoc {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (i : ℕ) (hi : i ≤ n) :
    (List.ofFn (Fin.snoc v t : Fin (n + 1) → ℝ)).getD i 0 = chainX t v i := by
  rw [getD_ofFn, dif_pos (by omega)]
  unfold chainX
  by_cases h : i < n
  · rw [dif_pos h]
    have : (⟨i, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i, h⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg h]
    have : (⟨i, by omega⟩ : Fin (n + 1)) = Fin.last n := by ext; simp; omega
    rw [this, Fin.snoc_last]

theorem RosX_snoc_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    RosX false 1 (List.ofFn (Fin.snoc v t : Fin (n + 1) → ℝ)) ↔ RosserX t v := by
  rw [RosX_false_iff]
  unfold RosserX
  simp only [List.length_ofFn]
  apply forall_congr'; intro j
  apply imp_congr_right; intro hj
  apply imp_congr_right; intro h2
  have e : psum (List.ofFn (Fin.snoc v t : Fin (n + 1) → ℝ)) (2 * j - 1) = ∑ i ∈ Finset.range (2 * j - 1), chainX t v i := by
    unfold psum
    apply Finset.sum_congr rfl
    intro i hi
    exact getD_ofFn_snoc v t i (by have := Finset.mem_range.1 hi; omega)
  rw [e, getD_ofFn_snoc v t _ (by omega)]

theorem sum_snoc {n : ℕ} (v : Fin n → ℝ) (t : ℝ) (f : ℝ → ℝ) :
    ∑ i, f ((Fin.snoc v t : Fin (n + 1) → ℝ) i) = ∑ i, f (v i) + f t := by
  rw [Fin.sum_univ_castSucc]; simp

theorem prod_snoc {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ∏ i, (Fin.snoc v t : Fin (n + 1) → ℝ) i = (∏ i, v i) * t := by
  rw [Fin.prod_univ_castSucc]; simp

theorem Gs_eq_Gr (n : ℕ) (s : ℝ) (hs : s ≠ 1) : Gs (stF false (n + 1)) s = Gr (n + 1) s := by
  unfold Gs Gr
  by_cases h : Odd (n + 1)
  · rw [if_pos ((stF_false_iff _).2 h), if_pos h]
    unfold FjrC; rw [if_neg hs]
  · have h' : stF false (n + 1) = false := by
      cases hh : stF false (n + 1)
      · rfl
      · exact absurd ((stF_false_iff _).1 hh) h
    rw [h', if_neg h]; rfl

/-! ## The chain integrand in `x`-coordinates -/

noncomputable def Fch (P : WPar) (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  (Set.pi Set.univ (fun _ => Set.Ioc P.T0 1)).indicator (fun x => fch P n (logv x) / ∏ i, x i) x

noncomputable def Kch (P : WPar) (n : ℕ) (t : ℝ) : ℝ :=
  open Classical in if P.T0 < t ∧ t < 1 / 2 then (-1) ^ n * P.W t / t ^ 2 * kr (n + 1) t else 0

theorem measurableSet_boxx (r : ℕ) (a : ℝ) : MeasurableSet (Set.pi Set.univ (fun _ : Fin r => Set.Ioc a 1)) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem Ich_eq (P : WPar) (n : ℕ) : Ich P n = ∫ x, Fch P n x := by
  unfold Ich Fch
  rw [box_cov, integral_indicator (measurableSet_boxx _ _)]

theorem Fch_integrable (P : WPar) (hT9 : 1 / 9 ≤ P.T0) (n : ℕ) : Integrable (Fch P n) := by
  unfold Fch
  rw [integrable_indicator_iff (measurableSet_boxx _ _)]
  exact box_cov_integrable _ _ _ _ _ (integrableOn_box _ _ _ _ (fch_measurable P n) _ (fch_bound P hT9 n))

theorem strictAnti_logv_iff {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 < x i) : StrictAnti (logv x) ↔ StrictAnti x := by
  constructor
  · intro h i j hij; have := h hij; unfold logv at this; exact (Real.log_lt_log_iff (hx j) (hx i)).1 this
  · intro h i j hij; unfold logv; exact Real.log_lt_log (hx j) (h hij)

theorem fch_logv (P : WPar) (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 < x i) :
    fch P n (logv x) = open Classical in if StrictAnti x then PhiL P (List.ofFn x) else 0 := by
  classical
  unfold fch
  have : (fun i => Real.exp (logv x i)) = x := by funext i; unfold logv; rw [Real.exp_log (hx i)]
  rw [this]
  by_cases h : StrictAnti x
  · rw [if_pos ((strictAnti_logv_iff x hx).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((strictAnti_logv_iff x hx).1 h')), if_neg h]

theorem KRegion_lt_one {n : ℕ} (t : ℝ) (v : Fin n → ℝ) (ht : 0 < t) (hK : KRegion n t v) (i : Fin n) : v i < 1 := by
  obtain ⟨hSA, hgt, hR⟩ := hK
  have hn : 1 ≤ n := by have := i.2; omega
  have h1 := hR 1 le_rfl (by omega)
  simp only [Nat.mul_one, Nat.reduceSub, Finset.range_one, Finset.sum_singleton] at h1
  have e0 : chainX t v 0 = v ⟨0, by omega⟩ := by unfold chainX; rw [dif_pos (by omega)]
  have e1 : 0 < chainX t v 1 := by
    unfold chainX; split_ifs with h
    · exact lt_trans ht (hgt _)
    · exact ht
  rw [e0] at h1
  have hvi : v i ≤ v ⟨0, by omega⟩ := hSA.antitone (show (⟨0, by omega⟩ : Fin n) ≤ i from Nat.zero_le _)
  linarith

theorem Fch_snoc (P : WPar) (n : ℕ) (v : Fin n → ℝ) (t : ℝ) (h0 : P.T0 < t) (h1 : t < 1 / 2)
    (hv : ∑ i, v i ≠ 1 - 2 * t) :
    Fch P n (Fin.snoc v t) = (-1) ^ n * P.W t / t ^ 2 *
      (open Classical in if KRegion n t v then Gr (n + 1) ((1 - t - ∑ i, v i) / t) / ∏ i, v i else 0) := by
  classical
  have hT := T0_pos P
  have ht : 0 < t := lt_trans hT h0
  unfold Fch
  by_cases hK : KRegion n t v
  · rw [if_pos hK]
    obtain ⟨hSA, hgt, hR⟩ := hK
    have hlt1 := KRegion_lt_one t v ht ⟨hSA, hgt, hR⟩
    have hmem : (Fin.snoc v t : Fin (n + 1) → ℝ) ∈ Set.pi Set.univ (fun _ => Set.Ioc P.T0 1) := by
      intro i _
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]; exact ⟨lt_trans h0 (hgt i'), (hlt1 i').le⟩
      · simp only [Fin.snoc_last]; exact ⟨h0, by linarith⟩
    have hpos : ∀ i, 0 < (Fin.snoc v t : Fin (n + 1) → ℝ) i := fun i => lt_trans hT (hmem i (Set.mem_univ _)).1
    rw [Set.indicator_of_mem hmem, fch_logv P n _ hpos, if_pos ((strictAnti_snoc v t).2 ⟨hSA, hgt⟩)]
    unfold PhiL
    rw [getLastD_ofFn, Fin.snoc_last, List.length_ofFn, Nat.add_sub_cancel, List.sum_ofFn,
      if_pos ⟨(RosX_snoc_iff v t).2 hR, h1⟩, prod_snoc]
    have hsum : ∑ i, (Fin.snoc v t : Fin (n + 1) → ℝ) i = ∑ i, v i + t := sum_snoc v t id
    have hs : (1 - t - ∑ i, v i) / t ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq ht.ne'] at h; apply hv; linarith
    rw [hsum, show 1 - (∑ i, v i + t) = 1 - t - ∑ i, v i by ring, Gs_eq_Gr n _ hs]
    have hPv : 0 < ∏ i, v i := Finset.prod_pos (fun i _ => lt_trans ht (hgt i))
    field_simp
  · rw [if_neg hK, mul_zero]
    by_cases hmem : (Fin.snoc v t : Fin (n + 1) → ℝ) ∈ Set.pi Set.univ (fun _ => Set.Ioc P.T0 1)
    · have hpos : ∀ i, 0 < (Fin.snoc v t : Fin (n + 1) → ℝ) i := fun i => lt_trans hT (hmem i (Set.mem_univ _)).1
      rw [Set.indicator_of_mem hmem, fch_logv P n _ hpos]
      split_ifs with hSA
      · obtain ⟨h1', h2'⟩ := (strictAnti_snoc v t).1 hSA
        unfold PhiL
        rw [if_neg (fun h => hK ⟨h1', h2', (RosX_snoc_iff v t).1 h.1⟩), zero_div]
      · rw [zero_div]
    · rw [Set.indicator_of_notMem hmem]

theorem Fch_snoc_zero (P : WPar) (n : ℕ) (v : Fin n → ℝ) (t : ℝ) (h : ¬ (P.T0 < t ∧ t < 1 / 2)) :
    Fch P n (Fin.snoc v t) = 0 := by
  classical
  have hT := T0_pos P
  unfold Fch
  by_cases hmem : (Fin.snoc v t : Fin (n + 1) → ℝ) ∈ Set.pi Set.univ (fun _ => Set.Ioc P.T0 1)
  · have hpos : ∀ i, 0 < (Fin.snoc v t : Fin (n + 1) → ℝ) i := fun i => lt_trans hT (hmem i (Set.mem_univ _)).1
    have ht := hmem (Fin.last n) (Set.mem_univ _)
    rw [Fin.snoc_last] at ht
    have h12 : ¬ t < 1 / 2 := fun h' => h ⟨ht.1, h'⟩
    rw [Set.indicator_of_mem hmem, fch_logv P n _ hpos]
    split_ifs
    · unfold PhiL
      rw [getLastD_ofFn, Fin.snoc_last, if_neg (fun h' => h12 h'.2), zero_div]
    · rw [zero_div]
  · rw [Set.indicator_of_notMem hmem]

theorem inner_fch (P : WPar) (n : ℕ) (t : ℝ) : ∫ v : Fin n → ℝ, Fch P n (Fin.snoc v t) = Kch P n t := by
  classical
  unfold Kch
  by_cases h : P.T0 < t ∧ t < 1 / 2
  · rw [if_pos h]
    have hae : ∀ᵐ v : Fin n → ℝ ∂volume, ∑ i, v i ≠ 1 - 2 * t := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact Filter.Eventually.of_forall (fun v => by simp; linarith [h.2])
      · rw [ae_iff]; simpa using volume_sum_level_null hn (1 - 2 * t)
    rw [integral_congr_ae (hae.mono (fun v hv => Fch_snoc P n v t h.1 h.2 hv)), integral_const_mul]
    congr 1
  · rw [if_neg h]
    simp only [Fch_snoc_zero P n _ t h, MeasureTheory.integral_zero]

theorem Ich_eq_Kch (P : WPar) (hT9 : 1 / 9 ≤ P.T0) (n : ℕ) :
    Ich P n = ∫ t, Kch P n t ∧ Integrable (Kch P n) := by
  have hF := Fch_integrable P hT9 n
  have e : (fun t : ℝ => ∫ v : Fin n → ℝ, Fch P n (Fin.snoc v t)) = Kch P n := funext (inner_fch P n)
  refine ⟨?_, ?_⟩
  · rw [Ich_eq, integral_split_last _ hF, e]
  · rw [← e]; exact integrable_inner_last _ hF

/-! ## Summing over chain lengths: Lemma 5.2 -/

theorem sum_Kch (P : WPar) (hT8 : 1 / 8 ≤ P.T0) (t : ℝ) :
    ∑ n ∈ Finset.range 8, Kch P n t = (Set.Ioo P.T0 (1 / 2)).indicator
      (fun t => 2 * Real.exp Real.eulerMascheroniConstant * (P.W t * (1 / (1 - t) - hk 1 t - hk 2 t) / t)) t := by
  classical
  unfold Kch
  by_cases h : P.T0 < t ∧ t < 1 / 2
  · simp only [if_pos h]
    rw [Set.indicator_of_mem (show t ∈ Set.Ioo P.T0 (1 / 2) from h)]
    have ht : 0 < t := lt_of_le_of_lt (by linarith) h.1
    have hL := lemma52 (x := t) (by linarith [h.1]) h.2
    have hre : ∑ r ∈ Finset.Icc 1 8, (-1 : ℝ) ^ (r + 1) * kr r t = ∑ n ∈ Finset.range 8, (-1 : ℝ) ^ n * kr (n + 1) t := by
      rw [show (Finset.Icc 1 8 : Finset ℕ) = Finset.Ico 1 (1 + 8) from rfl, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      rw [show 1 + n + 1 = n + 2 by ring, show 1 + n = n + 1 by ring, pow_add, neg_one_sq, mul_one]
    have e : ∑ n ∈ Finset.range 8, (-1 : ℝ) ^ n * P.W t / t ^ 2 * kr (n + 1) t =
        P.W t / t ^ 2 * ∑ n ∈ Finset.range 8, (-1 : ℝ) ^ n * kr (n + 1) t := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
    rw [e, ← hre, hL]
    field_simp
  · simp only [if_neg h, Finset.sum_const_zero]
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioo P.T0 (1 / 2) from h)]

theorem sum_Ich (P : WPar) (hT8 : 1 / 8 ≤ P.T0) :
    ∑ n ∈ Finset.range 8, Ich P n = 2 * Real.exp Real.eulerMascheroniConstant *
      ∫ t in P.T0..(1 / 2 : ℝ), P.W t * (1 / (1 - t) - hk 1 t - hk 2 t) / t := by
  have hT9 : 1 / 9 ≤ P.T0 := by linarith
  have hT2 : P.T0 ≤ 1 / 2 := by have := P.hT1; linarith
  have h1 : ∑ n ∈ Finset.range 8, Ich P n = ∑ n ∈ Finset.range 8, ∫ t, Kch P n t :=
    Finset.sum_congr rfl (fun n _ => (Ich_eq_Kch P hT9 n).1)
  rw [h1, ← integral_finsetSum _ (fun n _ => (Ich_eq_Kch P hT9 n).2)]
  simp only [sum_Kch P hT8]
  rw [integral_indicator measurableSet_Ioo, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hT2]

/-! ## The large primes -/

theorem Ibig_eq (P : WPar) :
    Ibig P = 2 * Real.exp Real.eulerMascheroniConstant *
      ∫ t in (1 / 2 : ℝ)..P.U, (P.W t - (P.U - P.V)) / ((1 - t) * t) := by
  classical
  have hT := T0_pos P
  have hU := P.hU; have hU1 := P.hU1; have hT1 := P.hT1
  unfold Ibig
  rw [box_cov, ← integral_indicator (measurableSet_boxx _ _)]
  have hs := (volume_preserving_funUnique (Fin 1) ℝ).symm
  set G := (Set.pi Set.univ (fun _ : Fin 1 => Set.Ioc P.T0 1)).indicator (fun x => fbig P (logv x) / ∏ i, x i)
  rw [show (∫ x, G x) = ∫ t, G ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t) from
    (hs.integral_comp (MeasurableEquiv.measurableEmbedding _) G).symm]
  have hpt : ∀ t : ℝ, (Set.pi Set.univ (fun _ : Fin 1 => Set.Ioc P.T0 1)).indicator
      (fun x => fbig P (logv x) / ∏ i, x i) ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t) =
      (Set.Icc (1 / 2) P.U).indicator
        (fun t => 2 * Real.exp Real.eulerMascheroniConstant * ((P.W t - (P.U - P.V)) / ((1 - t) * t))) t := by
    intro t
    have hsy : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm t = fun _ => t := rfl
    rw [hsy]
    have hmem : (fun _ : Fin 1 => t) ∈ Set.pi Set.univ (fun _ : Fin 1 => Set.Ioc P.T0 1) ↔ t ∈ Set.Ioc P.T0 1 := by
      simp [Set.mem_pi]
    by_cases ht : t ∈ Set.Ioc P.T0 1
    · rw [Set.indicator_of_mem (hmem.2 ht)]
      have ht0 : 0 < t := lt_trans hT ht.1
      have hfb : fbig P (logv (fun _ : Fin 1 => t)) =
          if 1 / 2 ≤ t then (P.W t - (P.U - P.V)) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - t) else 0 := by
        unfold fbig logv; rw [Real.exp_log ht0]
      rw [hfb, Fin.prod_univ_one]
      by_cases h2 : 1 / 2 ≤ t
      · rw [if_pos h2]
        by_cases hUt : t ≤ P.U
        · rw [Set.indicator_of_mem (show t ∈ Set.Icc (1 / 2) P.U from ⟨h2, hUt⟩)]
          have h1t : 1 - t ≠ 0 := by intro h; linarith
          field_simp
        · rw [Set.indicator_of_notMem (show t ∉ Set.Icc (1 / 2) P.U from fun h => hUt h.2), W_gt_U P t (not_le.1 hUt)]; simp
      · rw [if_neg h2, zero_div, Set.indicator_of_notMem (show t ∉ Set.Icc (1 / 2) P.U from fun h => h2 h.1)]
    · rw [Set.indicator_of_notMem (fun h => ht (hmem.1 h))]
      have : t ∉ Set.Icc (1 / 2) P.U := by
        intro h; apply ht; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_notMem this]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

/-- **The limit is `2e^γ 𝓜`.** -/
theorem limit_eq (P : WPar) (hT8 : 1 / 8 ≤ P.T0) :
    Ibig P + ∑ n ∈ Finset.range 8, Ich P n = 2 * Real.exp Real.eulerMascheroniConstant * Mval P := by
  rw [Ibig_eq, sum_Ich P hT8, Mval]; ring

end Palprimes.MT
