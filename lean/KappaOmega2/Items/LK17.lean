import KappaOmega2.StatementsK
import KappaOmega2.Items.LK17_Dig

/-!
# LK17: facts about the weighted κ-sequence

Digits of `n(u, w)` (helper `LK17_Dig`): `n(u, w)` determines `(u, w)` when `u_0 ≠ 0`, has `2N + 1` digits and is a
κ-palindrome. A pair with `n(u, w)` coprime to `b³ − b` has `u_0 = n mod b ≠ 0`.
-/

namespace KappaOmega2

open Finset Palprimes

lemma LK17_wK_nonneg (b : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (N : ℕ) (u : KVec b N) :
    0 ≤ wK b g N u :=
  Finset.prod_nonneg (fun k _ => hg _)

lemma LK17_wK_le (b : ℕ) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ a, 0 ≤ g a) (hM : ∀ a, g a ≤ M)
    (N : ℕ) (u : KVec b N) : wK b g N u ≤ M ^ mK N := by
  unfold wK
  calc ∏ k : Fin (mK N), g (u k) ≤ ∏ _k : Fin (mK N), M :=
        Finset.prod_le_prod₀ (fun _ _ => hg _) (fun _ _ => hM _)
    _ = M ^ mK N := by simp

lemma LK17_wK_sum (b : ℕ) (g : ℕ → ℝ) (hW : IsDigitWeight b g) (N : ℕ) :
    ∑ u : KVec b N, wK b g N u = 1 := by
  unfold wK
  have h := Finset.prod_univ_sum (fun _ : Fin (mK N) => (univ : Finset (Fin b)))
    (fun _ (j : Fin b) => g (j : ℕ))
  simp only [Fintype.piFinset_univ] at h
  rw [← h]
  have hs : ∑ j : Fin b, g (j : ℕ) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g i) b]
    exact hW.2
  simp [hs]

lemma LK17_bdvd (b : ℕ) : b ∣ bigB b := by
  unfold bigB
  exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl

/-- A pair with `n(u, w)` coprime to `b³ − b` has `u_0 ≠ 0`. -/
lemma LK17_u0 (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (u : KVec b N) (w : ℕ) (hw : w < WK b N)
    (hc : Nat.Coprime (kpalVal b N u w) (bigB b)) : (u ⟨0, LK17_m_pos N hN⟩ : ℕ) ≠ 0 := by
  intro h0
  have hmod := LK17_mod_b b N hN u w hw
  rw [h0] at hmod
  have hdiv : b ∣ kpalVal b N u w := Nat.dvd_of_mod_eq_zero hmod
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdiv hc) (LK17_bdvd b)
  omega

theorem itemLK17 : ItemLK17 := by
  unfold ItemLK17
  intro b g M N hb hN hg hM
  have hb2 : 2 ≤ b := by omega
  have hWpos : (0 : ℝ) < (WK b N : ℝ) := by
    have : 0 < WK b N := by unfold WK; exact pow_pos (by omega) _
    exact_mod_cast this
  have hM0 : 0 ≤ M := le_trans (hg 0) (hM 0)
  have hterm_nonneg : ∀ u : KVec b N, 0 ≤ wK b g N u / (WK b N : ℝ) :=
    fun u => div_nonneg (LK17_wK_nonneg b g hg N u) hWpos.le
  have hinj : ∀ u u' : KVec b N, ∀ w w' : ℕ, w < WK b N → w' < WK b N →
      Nat.Coprime (kpalVal b N u w) (bigB b) → Nat.Coprime (kpalVal b N u' w') (bigB b) →
      kpalVal b N u w = kpalVal b N u' w' → u = u' ∧ w = w' := by
    intro u u' w w' hw hw' hc hc' h
    exact LK17_inj b N hb2 hN u u' w w' hw hw' (LK17_u0 b N hb2 hN u w hw hc)
      (LK17_u0 b N hb2 hN u' w' hw' hc') h
  have hrange : ∀ u : KVec b N, ∀ w, w < WK b N → Nat.Coprime (kpalVal b N u w) (bigB b) →
      kpalVal b N u w ∈ kpiStar b N := by
    intro u w hw hc
    obtain ⟨h1, h2, h3⟩ := LK17_mem b N hb2 hN u w hw (LK17_u0 b N hb2 hN u w hw hc)
    unfold kpiStar
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h1, h2⟩, h3, hc⟩
  refine ⟨fun n => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold aK
    apply Finset.sum_nonneg; intro u _
    apply Finset.sum_nonneg; intro w _
    split_ifs
    · exact hterm_nonneg u
    · exact le_rfl
  · unfold aK
    by_cases hex : ∃ u : KVec b N, ∃ w, w < WK b N ∧ kpalVal b N u w = n ∧ Nat.Coprime n (bigB b)
    · obtain ⟨u0, w0, hw0, hn0, hc0⟩ := hex
      subst hn0
      rw [Finset.sum_eq_single u0]
      · rw [Finset.sum_eq_single w0]
        · rw [if_pos ⟨rfl, hc0⟩]
          exact div_le_div_of_nonneg_right (LK17_wK_le b g M hg hM N u0) hWpos.le
        · intro w hw hne
          rw [if_neg]
          rintro ⟨h, _⟩
          exact hne (hinj u0 u0 w w0 (Finset.mem_range.1 hw) hw0 (h ▸ hc0) hc0 h).2
        · intro h; exact absurd (Finset.mem_range.2 hw0) h
      · intro u _ hne
        apply Finset.sum_eq_zero
        intro w hw
        rw [if_neg]
        rintro ⟨h, _⟩
        exact hne (hinj u u0 w w0 (Finset.mem_range.1 hw) hw0 (h ▸ hc0) hc0 h).1
      · intro h; exact absurd (Finset.mem_univ u0) h
    · calc _ = (0 : ℝ) := by
            apply Finset.sum_eq_zero; intro u _
            apply Finset.sum_eq_zero; intro w hw
            rw [if_neg]
            rintro ⟨h1, h2⟩
            exact hex ⟨u, w, Finset.mem_range.1 hw, h1, h2⟩
        _ ≤ M ^ mK N / (WK b N : ℝ) := div_nonneg (pow_nonneg hM0 _) hWpos.le
  · intro hn
    by_contra hnot
    apply hn
    unfold aK
    apply Finset.sum_eq_zero; intro u _
    apply Finset.sum_eq_zero; intro w hw
    rw [if_neg]
    rintro ⟨h1, h2⟩
    subst h1
    exact hnot (hrange u w (Finset.mem_range.1 hw) h2)
  · intro q
    unfold AK aK
    have step1 : ∀ n ∈ range (b ^ (2 * N + 1)),
        (if q ∣ n then ∑ u : KVec b N, ∑ w ∈ range (WK b N),
            (if kpalVal b N u w = n ∧ Nat.Coprime n (bigB b) then wK b g N u / (WK b N : ℝ) else 0) else 0)
          = ∑ u : KVec b N, ∑ w ∈ range (WK b N),
            (if q ∣ n ∧ (kpalVal b N u w = n ∧ Nat.Coprime n (bigB b)) then wK b g N u / (WK b N : ℝ)
              else 0) := by
      intro n _
      by_cases h : q ∣ n
      · simp only [h, true_and, if_true]
      · simp [h]
    symm
    rw [Finset.sum_congr rfl step1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    have hw' := Finset.mem_range.1 hw
    by_cases hc : Nat.Coprime (kpalVal b N u w) (bigB b)
    · have hmem : kpalVal b N u w ∈ range (b ^ (2 * N + 1)) := by
        have := hrange u w hw' hc
        unfold kpiStar at this
        exact Finset.mem_range.2 (Finset.mem_Ico.1 (Finset.mem_filter.1 this).1).2
      rw [Finset.sum_eq_single (kpalVal b N u w)]
      · by_cases hq : q ∣ kpalVal b N u w
        · simp [hq, hc]
        · simp [hq]
      · intro n _ hne
        rw [if_neg]
        rintro ⟨_, hpn, _⟩
        exact hne hpn.symm
      · intro h
        exact absurd hmem h
    · rw [if_neg (fun h => hc h.1)]
      apply Finset.sum_eq_zero
      intro n _
      rw [if_neg]
      rintro ⟨_, hpn, hcn⟩
      exact hc (by rw [hpn]; exact hcn)
  · intro hDW
    unfold XK AK
    calc _ ≤ ∑ u : KVec b N, ∑ _w ∈ range (WK b N), wK b g N u / (WK b N : ℝ) := by
          apply Finset.sum_le_sum; intro u _
          apply Finset.sum_le_sum; intro w _
          split_ifs
          · exact le_rfl
          · exact hterm_nonneg u
      _ = ∑ u : KVec b N, wK b g N u := by
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
      _ = 1 := LK17_wK_sum b g hDW N

end KappaOmega2
