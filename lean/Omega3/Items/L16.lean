import Omega3.Statements
import Omega3.Items.L16_tent

namespace Omega3

open Finset

lemma L16_fej_nonneg (m a : ℕ) : 0 ≤ fejerW m a := by
  unfold fejerW
  split_ifs <;> positivity

lemma L16_fej_le (m a : ℕ) (hm : 1 ≤ m) : fejerW m a ≤ 1 / (m : ℚ) := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold fejerW
  split_ifs with h
  · have hmin : min (a + 1) (2 * m - 1 - a) ≤ m := by omega
    have hq : ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℚ) ≤ m := by exact_mod_cast hmin
    calc ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℚ) / (m : ℚ) ^ 2
        ≤ (m : ℚ) / (m : ℚ) ^ 2 := by gcongr
      _ = 1 / (m : ℚ) := by field_simp
  · positivity

lemma L16_fej_pos (m a : ℕ) (hm : 1 ≤ m) (ha : a < 2 * m - 1) : 0 < fejerW m a := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold fejerW
  rw [if_pos (by omega)]
  apply div_pos
  · exact_mod_cast (show 0 < min (a + 1) (2 * m - 1 - a) by omega)
  · exact pow_pos hm0 2

lemma L16_fej_sum (m : ℕ) (hm : 1 ≤ m) (b : ℕ) (h1 : 2 * m - 1 ≤ b) (h2 : b ≤ 2 * m) :
    ∑ a ∈ range b, fejerW m a = 1 := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsub : ∑ a ∈ range (2 * m - 1), fejerW m a = ∑ a ∈ range b, fejerW m a := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      unfold fejerW
      rw [if_neg (by omega)]
  rw [← hsub]
  have hc : ∀ a ∈ range (2 * m - 1), fejerW m a
      = ((min (a + 1) (2 * m - 1 - a) : ℕ) : ℚ) / ((m : ℚ) ^ 2) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    unfold fejerW
    rw [if_pos (by omega)]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_div, ← Nat.cast_sum, L16_tent_sum]
  push_cast
  field_simp

theorem itemL16 : ItemL16 := by
  unfold ItemL16
  intro b hb
  have hbR : (5 : ℝ) ≤ b := by exact_mod_cast hb
  have hP1 : 0 < recP b := by
    unfold recP
    split_ifs with h
    · norm_num
    · have h16 : (16 : ℝ) ≤ b := by exact_mod_cast (by omega : 16 ≤ b)
      have : (1 : ℝ) / (b : ℝ) ^ 2 < 1 := by
        rw [div_lt_one (pow_pos (by linarith) 2)]
        nlinarith
      linarith
  have hP2 : recP b < 1 := by
    unfold recP
    split_ifs with h
    · norm_num
    · have : (0 : ℝ) < 1 / (b : ℝ) ^ 2 := one_div_pos.mpr (pow_pos (by linarith) 2)
      linarith
  have hH : recH b ≤ 2 * b - 2 := by
    unfold recH
    split_ifs <;> (try unfold mB) <;> omega
  have hG : (∀ a, 0 ≤ recGR b a) ∧ (∑ a ∈ range b, recGR b a = 1) ∧ 0 < recGR b 0 ∧
      0 < recGR b 1 ∧ (∀ a, recGR b a ≤ 1 / 3) := by
    by_cases h6 : b = 6
    · subst h6
      refine ⟨fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
      · rcases a with _ | _ | _ | _ | _ | _ | a <;> norm_num [recGR, recG, g6list]
      · simp [Finset.sum_range_succ, recGR, recG, g6list]
        norm_num
      · norm_num [recGR, recG, g6list]
      · norm_num [recGR, recG, g6list]
      · rcases a with _ | _ | _ | _ | _ | _ | a <;> norm_num [recGR, recG, g6list]
    by_cases h8 : b = 8
    · subst h8
      refine ⟨fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
      · rcases a with _ | _ | _ | _ | _ | _ | _ | _ | a <;> norm_num [recGR, recG, g8list]
      · simp [Finset.sum_range_succ, recGR, recG, g8list]
        norm_num
      · norm_num [recGR, recG, g8list]
      · norm_num [recGR, recG, g8list]
      · rcases a with _ | _ | _ | _ | _ | _ | _ | _ | a <;> norm_num [recGR, recG, g8list]
    have hm3 : 3 ≤ mB b := by unfold mB; omega
    have hrec : ∀ a, recGR b a = ((fejerW (mB b) a : ℚ) : ℝ) := by
      intro a
      simp [recGR, recG, h6, h8]
    refine ⟨fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
    · rw [hrec]
      exact Rat.cast_nonneg.mpr (L16_fej_nonneg _ _)
    · rw [Finset.sum_congr rfl (fun a _ => hrec a), ← Rat.cast_sum,
        L16_fej_sum (mB b) (by omega) b (by unfold mB; omega) (by unfold mB; omega)]
      norm_num
    · rw [hrec]
      exact Rat.cast_pos.mpr (L16_fej_pos _ 0 (by omega) (by omega))
    · rw [hrec]
      exact Rat.cast_pos.mpr (L16_fej_pos _ 1 (by omega) (by omega))
    · rw [hrec]
      have h3 : (1 : ℚ) / (mB b : ℚ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm3)
      have hq : fejerW (mB b) a ≤ 1 / 3 := le_trans (L16_fej_le _ _ (by omega)) h3
      calc ((fejerW (mB b) a : ℚ) : ℝ) ≤ ((1 / 3 : ℚ) : ℝ) := Rat.cast_le.mpr hq
        _ = 1 / 3 := by norm_num
  obtain ⟨hnn, hsum, hp0, hp1, hle⟩ := hG
  exact ⟨⟨hnn, hsum⟩, hp0, hp1, hle, hP1, hP2, hH⟩

end Omega3
