import Omega3.Statements
import Palprimes.Level.Level

namespace Omega3

open Finset Palprimes
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

lemma L17_wDig_nonneg (b : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (N : ℕ) (d : DigVec b N) :
    0 ≤ wDig b g N d := by
  unfold wDig
  exact Finset.prod_nonneg (fun k _ => hg _)

lemma L17_wDig_le (b : ℕ) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ a, 0 ≤ g a) (hM : ∀ a, g a ≤ M)
    (N : ℕ) (d : DigVec b N) : wDig b g N d ≤ M ^ (N + 1) := by
  unfold wDig
  calc ∏ k : Fin (N + 1), g (d k) ≤ ∏ _k : Fin (N + 1), M := by
        exact Finset.prod_le_prod₀ (fun k _ => hg _) (fun k _ => hM _)
    _ = M ^ (N + 1) := by simp

lemma L17_d0 (b N : ℕ) (hb : 2 ≤ b) (d : DigVec b N) (hc : Nat.Coprime (palVal b N d) (bigB b)) :
    (d 0 : ℕ) ≠ 0 := by
  intro h0
  have hz' : (extDig d 0 : ℤ) = 0 := by
    unfold extDig
    simp [h0]
  have hdiv : b ∣ palVal b N d := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hz : palVal b 0 d = 0 := by
        have := palVal_eq_sum b 0 d
        rw [Finset.sum_range_one] at this
        have hcK : (cK b 0 0 : ℤ) = 1 := by simp [cK]
        rw [hcK, hz', mul_one] at this
        exact_mod_cast this
      rw [hz]
      exact dvd_zero b
    · have hm := palVal_modEq_base b N hN d
      rw [hz', sub_zero] at hm
      exact_mod_cast hm
  have hbB : b ∣ bigB b := by
    unfold bigB
    exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdiv hc) hbB
  omega

theorem itemL17 : ItemL17 := by
  unfold ItemL17
  intro b g M N hb hg hM
  have hb0 : 0 ≤ M := le_trans (hg 0) (hM 0)
  have haW_nonneg : ∀ n, 0 ≤ aW b g N n := by
    intro n
    unfold aW
    apply Finset.sum_nonneg
    intro d _
    split_ifs
    · exact L17_wDig_nonneg b g hg N d
    · exact le_rfl
  have haW_le : ∀ n, aW b g N n ≤ M ^ (N + 1) := by
    intro n
    unfold aW
    by_cases hex : ∃ d : DigVec b N, palVal b N d = n ∧ Nat.Coprime n (bigB b)
    · obtain ⟨d0, hd0, hc0⟩ := hex
      rw [Finset.sum_eq_single d0
        (fun d _ hne => if_neg (fun h => hne (palVal_injective b N hb (h.1.trans hd0.symm))))
        (fun h => absurd (Finset.mem_univ d0) h)]
      rw [if_pos ⟨hd0, hc0⟩]
      exact L17_wDig_le b g M hg hM N d0
    · calc _ = 0 := Finset.sum_eq_zero (fun d _ => if_neg (fun h => hex ⟨d, h.1, h.2⟩))
        _ ≤ M ^ (N + 1) := pow_nonneg hb0 _
  have haW_supp : ∀ n, aW b g N n ≠ 0 → n ∈ piStar b N := by
    intro n hn
    by_contra hnot
    apply hn
    unfold aW
    apply Finset.sum_eq_zero
    intro d _
    rw [if_neg]
    rintro ⟨hdn, hc⟩
    apply hnot
    subst hdn
    have hd0 := L17_d0 b N hb d hc
    have hmem : palVal b N d ∈ (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := by
      rw [pal_eq_image b N hb]
      exact Finset.mem_image.2 ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd0⟩, rfl⟩
    unfold piStar
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hmem).1, (Finset.mem_filter.1 hmem).2, hc⟩
  have hAW : ∀ q, AW b g N q = ∑ n ∈ range (b ^ (2 * N + 1)), if q ∣ n then aW b g N n else 0 := by
    intro q
    unfold AW aW
    have step1 : ∀ n ∈ range (b ^ (2 * N + 1)),
        (if q ∣ n then ∑ d : DigVec b N, (if palVal b N d = n ∧ Nat.Coprime n (bigB b) then wDig b g N d else 0) else 0)
          = ∑ d : DigVec b N, (if q ∣ n ∧ (palVal b N d = n ∧ Nat.Coprime n (bigB b)) then wDig b g N d else 0) := by
      intro n _
      by_cases h : q ∣ n
      · simp only [h, true_and, if_true]
      · simp [h]
    rw [Finset.sum_congr rfl step1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hc : Nat.Coprime (palVal b N d) (bigB b)
    · have hd0 := L17_d0 b N hb d hc
      have hmem : palVal b N d ∈ range (b ^ (2 * N + 1)) := by
        have hI : palVal b N d ∈ (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := by
          rw [pal_eq_image b N hb]
          exact Finset.mem_image.2 ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd0⟩, rfl⟩
        exact Finset.mem_range.2 (Finset.mem_Ico.1 (Finset.mem_filter.1 hI).1).2
      rw [Finset.sum_eq_single (palVal b N d)]
      · by_cases hq : q ∣ palVal b N d
        · simp [hq, hc]
        · simp [hq]
      · intro n _ hne
        rw [if_neg]
        rintro ⟨_, hpn, _⟩
        exact hne hpn.symm
      · intro h
        exact absurd hmem h
    · rw [if_neg (fun h => hc h.1)]
      symm
      apply Finset.sum_eq_zero
      intro n _
      rw [if_neg]
      rintro ⟨_, hpn, hcn⟩
      exact hc (by rw [hpn]; exact hcn)
  refine ⟨fun n => ⟨haW_nonneg n, haW_le n, fun hn => haW_supp n hn⟩, hAW, ?_⟩
  intro hW
  have hsum1 : ∑ d : DigVec b N, wDig b g N d = 1 := by
    unfold wDig
    have h := Finset.prod_univ_sum (fun _ : Fin (N + 1) => (univ : Finset (Fin b)))
      (fun _ (j : Fin b) => g (j : ℕ))
    simp only [Fintype.piFinset_univ] at h
    rw [← h]
    have hs : ∑ j : Fin b, g (j : ℕ) = 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => g i) b]
      exact hW.2
    simp [hs]
  unfold XW AW
  refine le_trans (Finset.sum_le_sum (fun d _ => ?_)) (le_of_eq hsum1)
  split_ifs
  · exact le_rfl
  · exact L17_wDig_nonneg b g hg N d

end Omega3
