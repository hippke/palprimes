import KappaOmega2.StatementsK
import KappaOmega2.Items.LK07_Prod
import KappaOmega2.Items.L07_Fej
import KappaOmega2.Items.LK06
import KappaOmega2.Items.LK01
import KappaOmega2.FejerPsi4

/-!
# LK07: record numerics of the κ route for every `b ≥ 3`

Weight, exponent `p = 1 − b^{−6}`, degree, `τ₀ > 0`, mass `= 1`, fourth moment `m_w(4) ≤ 1/b` (Fejér closed form for
odd `b` through `FejerM4Stmt`, product-weight closed form `LK07_Prod` for even `b`, then `ψ₄ ≥ 1` from
`KappaOmega2.FejerPsi4`), and the rate `ψ = 5/8`: `τ₀⁸ b⁵ ≤ 1` (explicitly for `b ≤ 6`, by `τ₀ b ≤ 2.01` for `b ≥ 7`), and
`(7/20)(5/8) + (3/10)p ≥ 103/200 + 1/1000` as `p ≥ 1 − 3^{−6}`.
-/

namespace KappaOmega2

open Finset Real Palprimes

lemma LK07_prodW_eq (m i : ℕ) : prodW m i = (pU m i : ℚ) / ((m : ℚ) * (m + 1)) := by
  unfold prodW pU; split_ifs <;> simp

lemma LK07_prodW_zero (m i : ℕ) (h : 2 * m ≤ i) : prodW m i = 0 := by
  unfold prodW; rw [if_neg (by omega)]

/-- Closed form of `m_w(4)` for the product weight of `b = 2m`. -/
lemma LK07_mw4_prod (m : ℕ) (hm : 1 ≤ m) :
    mw4 (2 * m) (fun a => ((prodW m a : ℚ) : ℝ)) =
      ((((m : ℚ) * (m + 1) * (2 * m + 1) * (151 * (m : ℚ) ^ 4 + 302 * (m : ℚ) ^ 3 + 161 * (m : ℚ) ^ 2 +
        10 * m + 6) / 630) / ((m : ℚ) * (m + 1)) ^ 4 : ℚ) : ℝ) := by
  set F : ℕ → ℚ := fun s => ∑ i ∈ range (s + 1), prodW m i * prodW m (s - i) with hFdef
  have hinner : ∀ s, (∑ i ∈ range (s + 1),
      (if i < 2 * m ∧ s - i < 2 * m then ((prodW m i : ℚ) : ℝ) * ((prodW m (s - i) : ℚ) : ℝ) else 0)) =
        ((F s : ℚ) : ℝ) := by
    intro s
    rw [hFdef]; push_cast
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hc
    · rfl
    · rcases not_and_or.mp hc with hc | hc
      · rw [LK07_prodW_zero m i (by omega)]; simp
      · rw [LK07_prodW_zero m (s - i) (by omega)]; simp
  have hD : ((m : ℚ) * (m + 1)) ≠ 0 := by positivity
  have hFphi : ∀ s, F s = pPhi m s / ((m : ℚ) * (m + 1)) ^ 2 := by
    intro s
    rw [hFdef, ← pU_conv, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [LK07_prodW_eq, LK07_prodW_eq]
    field_simp
  have hFz : ∀ s, 4 * m - 1 ≤ s → F s = 0 := by
    intro s hs
    rw [hFdef]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi2 : 2 * m ≤ i
    · rw [LK07_prodW_zero m i hi2]; simp
    · rw [LK07_prodW_zero m (s - i) (by omega)]; simp
  have hsum : ∑ s ∈ range (4 * m - 1), F s ^ 2 = ∑ s ∈ range (4 * m + 1), F s ^ 2 := by
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      rw [hFz x hx]; simp
  unfold mw4
  simp_rw [hinner]
  have hc : (∑ s ∈ range (2 * (2 * m) - 1), ((F s : ℚ) : ℝ) ^ 2) =
      ((∑ s ∈ range (2 * (2 * m) - 1), F s ^ 2 : ℚ) : ℝ) := by push_cast; rfl
  rw [hc, show 2 * (2 * m) - 1 = 4 * m - 1 by omega, hsum]
  congr 1
  simp_rw [hFphi, div_pow]
  rw [← Finset.sum_div, pSumPhi]
  ring

lemma LK07_recPK_bounds (b : ℕ) (hb : 3 ≤ b) :
    recPK b = 1 - 1 / (b : ℝ) ^ 6 ∧ 0 < 1 / (b : ℝ) ^ 6 ∧ 1 / (b : ℝ) ^ 6 ≤ 1 / 729 := by
  refine ⟨rfl, by positivity, ?_⟩
  have hb' : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have : (729 : ℝ) ≤ (b : ℝ) ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num) hb' 6
    norm_num at this; linarith
  exact one_div_le_one_div_of_le (by norm_num) this

lemma LK07_fejTau_nonneg (m u : ℕ) : 0 ≤ fejTau m u := by
  unfold fejTau
  split_ifs with h0 h1
  · positivity
  · apply div_nonneg _ (by positivity)
    have : (u : ℝ) < m := by exact_mod_cast h1
    linarith
  · exact le_rfl

lemma LK07_recPolyK_nonneg (b u : ℕ) : 0 ≤ recPolyK b u := by
  unfold recPolyK
  split_ifs
  · exact LK07_fejTau_nonneg _ _
  · have := LK07_fejTau_nonneg (b / 2) u
    have := LK07_fejTau_nonneg (b / 2 + 1) u
    linarith

lemma LK07_mass_eq (H : ℕ) (τ : ℕ → ℝ) (hτ : ∀ u, 0 ≤ τ u) : trigMass H τ = trigEval H τ 0 := by
  unfold trigMass trigEval
  rw [abs_of_nonneg (hτ 0)]
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  rw [abs_of_nonneg (hτ u)]
  simp

/-- `P(0) = recPolyK b 0` satisfies `0 < P(0)` and `P(0) b ≤ 2`. -/
lemma LK07_P0 (b : ℕ) (hb : 3 ≤ b) : 0 < recPolyK b 0 ∧ recPolyK b 0 * b ≤ 2 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  unfold recPolyK
  split_ifs with hodd
  · simp only [fejTau, if_true]
    have hm : (2 : ℝ) * (((b + 1) / 2 : ℕ) : ℝ) = b + 1 := by
      have : 2 * ((b + 1) / 2) = b + 1 := by omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < (((b + 1) / 2 : ℕ) : ℝ) := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    linarith
  · simp only [fejTau, if_true]
    have hm : (2 : ℝ) * ((b / 2 : ℕ) : ℝ) = b := by
      have : 2 * (b / 2) = b := by omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < ((b / 2 : ℕ) : ℝ) := by linarith
    refine ⟨by positivity, ?_⟩
    push_cast
    have h1 : 1 / ((b / 2 : ℕ) : ℝ) * b = 2 := by field_simp; linarith
    have h2 : 1 / (((b / 2 : ℕ) : ℝ) + 1) * b ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
    nlinarith

lemma LK07_tau0 (b : ℕ) (hb : 3 ≤ b) :
    recTauK b 0 = 1 / (b : ℝ) ^ 6 + recPK b * recPolyK b 0 := by
  simp [recTauK, recPK]

/-- From `τ⁸ b⁵ ≤ 1` to `τ ≤ b^{−5/8}`. -/
lemma LK07_rpow (b : ℕ) (hb : 1 ≤ b) (τ : ℝ) (hτ : 0 < τ) (h : τ ^ 8 * (b : ℝ) ^ 5 ≤ 1) :
    τ ≤ (b : ℝ) ^ (-(5 / 8 : ℝ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h1 : τ = (τ ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; norm_num
  have h2 : (b : ℝ) ^ (-(5 / 8 : ℝ)) = ((b : ℝ) ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_mul hb0.le]; norm_num
  have h3 : τ ^ (8 : ℕ) ≤ (b : ℝ) ^ (-(5 : ℝ)) := by
    rw [Real.rpow_neg hb0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h' : τ ^ 8 ≤ 1 / (b : ℝ) ^ 5 := by rw [le_div_iff₀ (by positivity)]; exact h
    rwa [one_div] at h'
  rw [h1, h2]
  exact Real.rpow_le_rpow (by positivity) h3 (by norm_num)

lemma LK07_tau_rate (b : ℕ) (hb : 3 ≤ b) : recTauK b 0 ^ 8 * (b : ℝ) ^ 5 ≤ 1 := by
  obtain ⟨hp, hε0, hε1⟩ := LK07_recPK_bounds b hb
  obtain ⟨hP0, hPb⟩ := LK07_P0 b hb
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hτ0 : 0 ≤ recTauK b 0 := by
    rw [LK07_tau0 b hb, hp]
    have : 0 ≤ 1 - 1 / (b : ℝ) ^ 6 := by linarith
    positivity
  have hτle : recTauK b 0 ≤ 1 / (b : ℝ) ^ 6 + recPolyK b 0 := by
    rw [LK07_tau0 b hb, hp]
    have : (1 - 1 / (b : ℝ) ^ 6) * recPolyK b 0 ≤ recPolyK b 0 := by
      have := hP0.le; nlinarith
    linarith
  by_cases hsmall : b ≤ 6
  · have hB : (1 / (b : ℝ) ^ 6 + recPolyK b 0) ^ 8 * (b : ℝ) ^ 5 ≤ 1 := by
      interval_cases b <;> norm_num [recPolyK, fejTau]
    calc recTauK b 0 ^ 8 * (b : ℝ) ^ 5 ≤ (1 / (b : ℝ) ^ 6 + recPolyK b 0) ^ 8 * (b : ℝ) ^ 5 := by
          gcongr
      _ ≤ 1 := hB
  · have hb7 : (7 : ℝ) ≤ b := by exact_mod_cast (show 7 ≤ b by omega)
    have hb0 : (0 : ℝ) < b := by linarith
    have he : 1 / (b : ℝ) ^ 6 * b ≤ 1 / 100 := by
      have : (100 : ℝ) ≤ (b : ℝ) ^ 5 := by
        have := pow_le_pow_left₀ (by norm_num) hb7 5
        norm_num at this; linarith
      rw [show 1 / (b : ℝ) ^ 6 * b = 1 / (b : ℝ) ^ 5 by field_simp]
      exact one_div_le_one_div_of_le (by norm_num) this
    have hτb : recTauK b 0 * b ≤ 201 / 100 := by
      have := mul_le_mul_of_nonneg_right hτle hb0.le
      nlinarith
    have hτb0 : 0 ≤ recTauK b 0 * b := by positivity
    have h8 : (recTauK b 0 * b) ^ 8 ≤ (b : ℝ) ^ 3 := by
      calc (recTauK b 0 * b) ^ 8 ≤ (201 / 100 : ℝ) ^ 8 := pow_le_pow_left₀ hτb0 hτb 8
        _ ≤ 7 ^ 3 := by norm_num
        _ ≤ (b : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hb7 3
    have hb3 : (0 : ℝ) < (b : ℝ) ^ 3 := by positivity
    have : recTauK b 0 ^ 8 * (b : ℝ) ^ 5 * (b : ℝ) ^ 3 ≤ 1 * (b : ℝ) ^ 3 := by
      calc recTauK b 0 ^ 8 * (b : ℝ) ^ 5 * (b : ℝ) ^ 3 = (recTauK b 0 * b) ^ 8 := by ring
        _ ≤ (b : ℝ) ^ 3 := h8
        _ = 1 * (b : ℝ) ^ 3 := by ring
    exact le_of_mul_le_mul_right this hb3

/-- `m_w(4) ≤ 1/b`. -/
lemma LK07_mw4 (hF : FejerM4Stmt) (b : ℕ) (hb : 3 ≤ b) : mw4 b (recGKR b) ≤ 1 / (b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  rw [le_div_iff₀ hbR]
  by_cases hodd : b % 2 = 1
  · have h6 : b ≠ 6 := by omega
    have h8 : b ≠ 8 := by omega
    have hm : 1 ≤ mB b := by unfold mB; omega
    have hfun : recGKR b = recGR b := by
      funext a
      simp [recGKR, recGR, recGK, recG, hodd, h6, h8, mB]
    rw [hfun, L07_mw4_fej hF b h6 h8 hm]
    have hM2 : (2 : ℚ) ≤ ((mB b : ℕ) : ℚ) := by
      have : 2 ≤ mB b := by unfold mB; omega
      exact_mod_cast this
    have key := KappaOmega2.psi4_odd ((mB b : ℕ) : ℚ) hM2
    have hbq : (b : ℚ) = 2 * ((mB b : ℕ) : ℚ) - 1 := by
      have : b + 1 = 2 * mB b := by unfold mB; omega
      have : (b : ℚ) + 1 = 2 * ((mB b : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    rw [← hbq] at key
    rw [show (b : ℝ) = ((b : ℚ) : ℝ) by norm_cast, ← Rat.cast_mul, show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num,
      Rat.cast_le]
    linarith
  · set m := b / 2 with hmdef
    have hm : 1 ≤ m := by omega
    have hb2 : b = 2 * m := by omega
    have hfun : recGKR b = fun a => ((prodW m a : ℚ) : ℝ) := by
      funext a
      simp [recGKR, recGK, hodd, hmdef]
    rw [hfun, hb2, LK07_mw4_prod m hm]
    have hM2 : (2 : ℚ) ≤ (m : ℚ) := by
      have : 2 ≤ m := by omega
      exact_mod_cast this
    have key := KappaOmega2.psi4_even (m : ℚ) hM2
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    have heq : ((m : ℚ) * (m + 1) * (2 * m + 1) * (151 * (m : ℚ) ^ 4 + 302 * (m : ℚ) ^ 3 + 161 * (m : ℚ) ^ 2 +
        10 * m + 6) / 630) / ((m : ℚ) * (m + 1)) ^ 4 =
        (2 * (m : ℚ) + 1) * (151 * (m : ℚ) ^ 4 + 302 * (m : ℚ) ^ 3 + 161 * (m : ℚ) ^ 2 + 10 * m + 6) /
          (630 * (m : ℚ) ^ 3 * ((m : ℚ) + 1) ^ 3) := by
      field_simp
    rw [heq]
    rw [show ((2 * m : ℕ) : ℝ) = (((2 * m : ℕ) : ℚ) : ℝ) by norm_cast, ← Rat.cast_mul,
      show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, Rat.cast_le]
    push_cast
    linarith

theorem itemLK07 : ItemLK07 := by
  unfold ItemLK07
  intro hF b hb
  obtain ⟨hp, hε0, hε1⟩ := LK07_recPK_bounds b hb
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  -- the weight
  have hnonneg : ∀ a, 0 ≤ recGKR b a := by
    intro a
    unfold recGKR recGK
    have : 0 ≤ recGK b a := by
      unfold recGK fejerW prodW
      split_ifs <;> positivity
    unfold recGK at this
    exact_mod_cast this
  have hsum : ∑ a ∈ range b, recGKR b a = 1 := by
    unfold recGKR
    rw [← Rat.cast_sum]
    norm_cast
    by_cases hodd : b % 2 = 1
    · set m := (b + 1) / 2 with hm
      have h2m : b = 2 * m - 1 := by omega
      have hm0 : (m : ℚ) ≠ 0 := by
        have : 1 ≤ m := by omega
        positivity
      have hp := L01_sum_pairs (R := ℚ) m (fun _ => (1 : ℚ))
      simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hp
      have : ∀ a ∈ range b, recGK b a = ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℚ) / (m : ℚ) ^ 2 := by
        intro a ha
        have ha' := Finset.mem_range.1 ha
        simp only [recGK, hodd, if_true, ← hm, fejerW]
        rw [if_pos (by omega)]
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, h2m, ← hp]
      field_simp
    · set m := b / 2 with hm
      have h2m : b = 2 * m := by omega
      have hm0 : (m : ℚ) * (m + 1) ≠ 0 := by
        have : 1 ≤ m := by omega
        positivity
      have hp := LK01_sum_pairs (R := ℚ) m (fun _ => (1 : ℚ))
      simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hp
      have : ∀ a ∈ range b, recGK b a = ((min (min (a + 1) m) (2 * m - a) : ℕ) : ℚ) / ((m : ℚ) * (m + 1)) := by
        intro a ha
        have ha' := Finset.mem_range.1 ha
        simp only [recGK, hodd, if_false, ← hm, prodW]
        rw [if_pos (by omega)]
      have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, h2m, ← hp]
      push_cast
      field_simp
  refine ⟨⟨hnonneg, hsum⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, LK07_mw4 hF b hb, ?_⟩
  · -- g(1) > 0
    unfold recGKR recGK
    split_ifs with hodd
    · have : (0 : ℚ) < fejerW ((b + 1) / 2) 1 := by
        unfold fejerW
        rw [if_pos (by omega)]
        have : 0 < min (1 + 1) (2 * ((b + 1) / 2) - 1 - 1) := by
          rw [lt_min_iff]; omega
        have h1 : (0 : ℚ) < ((min (1 + 1) (2 * ((b + 1) / 2) - 1 - 1) : ℕ) : ℚ) := by exact_mod_cast this
        have : 1 ≤ (b + 1) / 2 := by omega
        positivity
      exact_mod_cast this
    · have : (0 : ℚ) < prodW (b / 2) 1 := by
        unfold prodW
        rw [if_pos (by omega)]
        have : 0 < min (min (1 + 1) (b / 2)) (2 * (b / 2) - 1) := by
          rw [lt_min_iff, lt_min_iff]; omega
        have h1 : (0 : ℚ) < ((min (min (1 + 1) (b / 2)) (2 * (b / 2) - 1) : ℕ) : ℚ) := by exact_mod_cast this
        have : 1 ≤ b / 2 := by omega
        positivity
      exact_mod_cast this
  · -- g ≤ 1/2
    intro a
    unfold recGKR recGK
    split_ifs with hodd
    · have : fejerW ((b + 1) / 2) a ≤ 1 / 2 := by
        unfold fejerW
        split_ifs with ha
        · set m := (b + 1) / 2
          have hm2 : 2 ≤ m := by omega
          have hmin : min (a + 1) (2 * m - 1 - a) ≤ m := by omega
          have hmin' : ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hmin
          have hmq : (2 : ℚ) ≤ m := by exact_mod_cast hm2
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        · norm_num
      calc ((fejerW ((b + 1) / 2) a : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr this
        _ = 1 / 2 := by norm_num
    · have : prodW (b / 2) a ≤ 1 / 2 := by
        unfold prodW
        split_ifs with ha
        · set m := b / 2
          have hm1 : 1 ≤ m := by omega
          have hmin : min (min (a + 1) m) (2 * m - a) ≤ m := by omega
          have hmin' : ((min (min (a + 1) m) (2 * m - a) : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hmin
          have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm1
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        · norm_num
      calc ((prodW (b / 2) a : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr this
        _ = 1 / 2 := by norm_num
  · rw [hp]; linarith
  · rw [hp]; linarith
  · -- degree
    have h1 : b ≤ b * (b - 1) := Nat.le_mul_of_pos_right b (by omega)
    unfold recHK
    split_ifs <;> omega
  · -- τ₀ > 0
    rw [LK07_tau0 b hb, hp]
    have := (LK07_P0 b hb).1
    have : 0 ≤ 1 - 1 / (b : ℝ) ^ 6 := by linarith
    positivity
  · -- mass
    have hτ : ∀ u, 0 ≤ recTauK b u := by
      intro u
      unfold recTauK
      have h1 : 0 ≤ (if u = 0 then 1 - recPK b else 0) := by
        split_ifs
        · rw [hp]; linarith
        · exact le_rfl
      have h2 : 0 ≤ recPK b * recPolyK b u := by
        apply mul_nonneg _ (LK07_recPolyK_nonneg b u)
        rw [hp]; linarith
      linarith
    rw [LK07_mass_eq _ _ hτ]
    have hτf : recTauK b = fun u => (if u = 0 then 1 - recPK b else 0) + recPK b * recPolyK b u := by
      funext u; simp [recTauK]
    rw [hτf, l06_trig_affine]
    have hP1 := (LK06_main itemL01 itemLK01 b hb 0).2
    have hp0 : 0 ≤ recPK b := by rw [hp]; linarith
    have := mul_le_mul_of_nonneg_left hP1 hp0
    linarith
  · -- the rate ψ = 5/8
    refine ⟨5 / 8, ?_, ?_⟩
    · have hτ0 : 0 < recTauK b 0 := by
        rw [LK07_tau0 b hb, hp]
        have := (LK07_P0 b hb).1
        have : 0 ≤ 1 - 1 / (b : ℝ) ^ 6 := by linarith
        positivity
      exact LK07_rpow b (by omega) _ hτ0 (LK07_tau_rate b hb)
    · rw [hp]
      unfold thS
      linarith

end KappaOmega2
