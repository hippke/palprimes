import KappaOmega2.Statements

/-!
# L07 helper: facts on the Fejér record data (b ∉ {6, 8})
-/

namespace KappaOmega2

open Finset

lemma L07_mB_bounds (b : ℕ) : 2 * mB b - 1 ≤ b ∧ b ≤ 2 * mB b := by
  unfold mB; omega

lemma L07_recP_small (b : ℕ) (h : b ≤ 15) : recP b = 1023 / 1024 := by
  unfold recP; rw [if_pos h]

lemma L07_recP_large (b : ℕ) (h : ¬ b ≤ 15) : recP b = 1 - 1 / (b : ℝ) ^ 2 := by
  unfold recP; rw [if_neg h]

lemma L07_recH_fej (b : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) : recH b = mB b - 1 := by
  unfold recH; rw [if_neg h6, if_neg h8]

lemma L07_recTau_fej (b u : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) :
    recTau b u = (if u = 0 then 1 - recP b else 0) + recP b * fejTau (mB b) u := by
  unfold recTau recPoly; rw [if_neg h6, if_neg h8]

lemma L07_recGR_fej (b a : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) :
    recGR b a = ((fejerW (mB b) a : ℚ) : ℝ) := by
  unfold recGR recG; rw [if_neg h6, if_neg h8]

lemma L07_tau0_fej (b : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) :
    recTau b 0 = (1 - recP b) + recP b * (1 / (mB b : ℝ)) := by
  rw [L07_recTau_fej b 0 h6 h8]; simp [fejTau]

lemma L07_gauss (n : ℕ) : 2 * ∑ u ∈ Icc 1 n, (u : ℝ) = (n : ℝ) * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast; ring

/-- `trigMass` of the Fejér record majorant is `1`. -/
lemma L07_mass_fej (b : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) (hm : 1 ≤ mB b) (hp0 : 0 ≤ recP b)
    (hp1 : recP b ≤ 1) : trigMass (recH b) (recTau b) = 1 := by
  rw [L07_recH_fej b h6 h8]
  obtain ⟨n, hn⟩ : ∃ n, mB b = n + 1 := ⟨mB b - 1, by omega⟩
  have hsub : mB b - 1 = n := by omega
  rw [hsub]
  unfold trigMass
  have hterm : ∀ u ∈ Icc 1 n, |recTau b u| = recP b * (((n : ℝ) + 1) - u) / ((n : ℝ) + 1) ^ 2 := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    rw [L07_recTau_fej b u h6 h8, if_neg (by omega)]
    unfold fejTau
    rw [if_neg (by omega), if_pos (by omega), hn]
    push_cast
    have hnu : (u : ℝ) ≤ n := by exact_mod_cast hu.2
    rw [zero_add, abs_of_nonneg (by
      apply mul_nonneg hp0; apply div_nonneg _ (by positivity); linarith)]
    ring
  rw [Finset.sum_congr rfl hterm, L07_tau0_fej b h6 h8, hn]
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  push_cast
  have hg := L07_gauss n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_nonneg (by
    have : 0 ≤ recP b * (1 / ((n : ℝ) + 1)) := mul_nonneg hp0 (by positivity)
    linarith)]
  have hs : ∑ u ∈ Icc 1 n, (u : ℝ) = (n : ℝ) * (n + 1) / 2 := by linarith
  rw [hs, nsmul_eq_mul]
  field_simp
  ring

/-- The Fejér fourth moment through `FejerM4Stmt`. -/
lemma L07_mw4_fej (hF : FejerM4Stmt) (b : ℕ) (h6 : b ≠ 6) (h8 : b ≠ 8) (hm : 1 ≤ mB b) :
    mw4 b (recGR b) =
      (((151 * ((mB b : ℕ) : ℚ) ^ 6 + 70 * ((mB b : ℕ) : ℚ) ^ 4 + 49 * ((mB b : ℕ) : ℚ) ^ 2 + 45) /
        (315 * ((mB b : ℕ) : ℚ) ^ 7) : ℚ) : ℝ) := by
  set m := mB b with hmdef
  obtain ⟨h1, h2⟩ := L07_mB_bounds b
  rw [← hmdef] at h1 h2
  have hz : ∀ a, 2 * m - 1 ≤ a → fejerW m a = 0 := by
    intro a ha; unfold fejerW; rw [if_neg (by omega)]
  -- inner sums
  set F : ℕ → ℚ := fun s => ∑ i ∈ range (s + 1), fejerW m i * fejerW m (s - i) with hFdef
  have hinner : ∀ s, (∑ i ∈ range (s + 1),
      (if i < b ∧ s - i < b then recGR b i * recGR b (s - i) else 0)) = ((F s : ℚ) : ℝ) := by
    intro s
    rw [hFdef]; push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [L07_recGR_fej b i h6 h8, L07_recGR_fej b (s - i) h6 h8, ← hmdef]
    split_ifs with hc
    · rfl
    · rcases not_and_or.mp hc with hc | hc
      · rw [hz i (by omega)]; simp
      · rw [hz (s - i) (by omega)]; simp
  have hFz : ∀ s, 4 * m - 3 ≤ s → F s = 0 := by
    intro s hs
    rw [hFdef]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hi2 : 2 * m - 1 ≤ i
    · rw [hz i hi2]; simp
    · rw [hz (s - i) (by omega)]; simp
  have hsum : ∀ n, 4 * m - 3 ≤ n → ∑ s ∈ range n, F s ^ 2 = ∑ s ∈ range (4 * m - 3), F s ^ 2 := by
    intro n hn
    symm
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      rw [hFz x hx]; simp
  unfold mw4
  simp_rw [hinner]
  have hF' : ∑ s ∈ range (4 * m), F s ^ 2 = _ := hF m hm
  have hc : (∑ s ∈ range (2 * b - 1), ((F s : ℚ) : ℝ) ^ 2) =
      ((∑ s ∈ range (2 * b - 1), F s ^ 2 : ℚ) : ℝ) := by push_cast; rfl
  rw [hc, ← hF', hsum (2 * b - 1) (by omega), hsum (4 * m) (by omega)]

end KappaOmega2
