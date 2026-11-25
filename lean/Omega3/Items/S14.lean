import Omega3.Statements

namespace Omega3

open Finset Palprimes.Greaves

theorem itemS14 : ItemS14 := by
  classical
  unfold ItemS14
  intro B hB y hy i δ hin
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  obtain ⟨hδp, hi, hlo, hhi⟩ := hin
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have hδpos : (0 : ℝ) < δ := Nat.cast_pos.mpr hδp.pos
  have hmono : ∀ j k : ℕ, j < k → k < B.xs.length → B.xs.getD j 0 < B.xs.getD k 0 := by
    intro j k hjk hk
    have hj : j < B.xs.length := by omega
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk]
    exact List.pairwise_iff_getElem.mp h4 j k hj hk hjk
  have hin_i : inBand B y i δ := ⟨hδp, hi, hlo, hhi⟩
  have huniq : ∀ j k : ℕ, inBand B y j δ → inBand B y k δ → j = k := by
    intro j k hj hk
    obtain ⟨_, hjl, hj1, hj2⟩ := hj
    obtain ⟨_, hkl, hk1, hk2⟩ := hk
    have hjx : j + 1 < B.xs.length := by omega
    have hkx : k < B.xs.length := by omega
    have hjx' : j < B.xs.length := by omega
    rcases lt_trichotomy j k with h | h | h
    · exfalso
      have hle : B.xs.getD (j + 1) 0 ≤ B.xs.getD k 0 := by
        rcases (show j + 1 = k ∨ j + 1 < k by omega) with e | e
        · rw [e]
        · exact le_of_lt (hmono _ _ e hkx)
      have hcast : ((B.xs.getD (j + 1) 0 : ℚ) : ℝ) ≤ ((B.xs.getD k 0 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hle
      have hpow : y ^ ((B.xs.getD (j + 1) 0 : ℚ) : ℝ) ≤ y ^ ((B.xs.getD k 0 : ℚ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hcast
      linarith
    · exact h
    · exfalso
      have hle : B.xs.getD (k + 1) 0 ≤ B.xs.getD j 0 := by
        rcases (show k + 1 = j ∨ k + 1 < j by omega) with e | e
        · rw [e]
        · exact le_of_lt (hmono _ _ e hjx')
      have hcast : ((B.xs.getD (k + 1) 0 : ℚ) : ℝ) ≤ ((B.xs.getD j 0 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hle
      have hpow : y ^ ((B.xs.getD (k + 1) 0 : ℚ) : ℝ) ≤ y ^ ((B.xs.getD j 0 : ℚ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hcast
      linarith
  have hfind : ∃ j, inBand B y j δ := ⟨i, hin_i⟩
  have hfeq : Nat.find hfind = i := huniq _ _ (Nat.find_spec hfind) hin_i
  have hcs_i : i < B.cs.length := by omega
  have hc1 : (1 : ℚ) ≤ B.cs.getD i 1 := by
    rw [List.getD_eq_getElem _ _ hcs_i]
    exact h6 _ (List.getElem_mem _)
  have hxi : (1 : ℚ) / 3 ≤ B.xs.getD i 0 := by
    rcases Nat.eq_zero_or_pos i with e | e
    · subst e
      have h0 : B.xs.getD 0 0 = 1 / 3 := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h3]
        simp
      rw [h0]
    · have hlt := hmono 0 i e (by omega)
      have h0 : B.xs.getD 0 0 = 1 / 3 := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h3]
        simp
      rw [h0] at hlt
      exact le_of_lt hlt
  have hxi1 : B.xs.getD (i + 1) 0 ≤ B.xn := by
    have hlast : B.xn = B.xs.getD (B.xs.length - 1) 0 := by
      unfold BandData.xn
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    rw [hlast]
    rcases (show i + 1 = B.xs.length - 1 ∨ i + 1 < B.xs.length - 1 by omega) with e | e
    · rw [e]
    · exact le_of_lt (hmono _ _ e (by omega))
  have t5 : ((B.xs.getD i 0 : ℚ) : ℝ) ≤ Real.log δ / Real.log y := by
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hy0 _) hlo
    rw [Real.log_rpow hy0] at hl
    rw [le_div_iff₀ hlogy]
    linarith
  have t6 : Real.log δ / Real.log y ≤ ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) := by
    have hl := Real.log_lt_log hδpos hhi
    rw [Real.log_rpow hy0] at hl
    rw [div_le_iff₀ hlogy]
    linarith
  have ht_lo : (1 / 3 : ℝ) ≤ Real.log δ / Real.log y := by
    have hx' : ((1 / 3 : ℚ) : ℝ) ≤ ((B.xs.getD i 0 : ℚ) : ℝ) := Rat.cast_le.mpr hxi
    push_cast at hx'
    linarith
  have ht_hi : Real.log δ / Real.log y ≤ UU := by
    have h9 : ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) ≤ ((B.xn : ℚ) : ℝ) := Rat.cast_le.mpr hxi1
    have hU : UU = 83 / 85 := rfl
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold etaOf
    rw [dif_pos hfind, hfeq]
  · unfold cOf
    rw [dif_pos hfind, hfeq]
  · rw [List.getD_eq_getElem _ _ (by omega : i < B.etas.length)]
    exact List.getElem_mem _
  · unfold cOf
    rw [dif_pos hfind, hfeq]
    exact_mod_cast hc1
  · exact t5
  · exact t6
  · unfold phiW wy Wf
    rw [Nat.Prime.primeFactors hδp, Finset.sum_singleton]
    have hmm : mm = 1 / 85 := rfl
    have hUU : UU = 83 / 85 := rfl
    have hW1 : W1 = 82 / 85 := rfl
    have hk : kSq = 9999 / 1000 := rfl
    set t := Real.log δ / Real.log y with ht
    rw [hmm] at *
    split_ifs with h1 h2 h3
    · exfalso
      norm_num at h1
      linarith
    · have ht3 : t = 1 / 3 := le_antisymm h2 ht_lo
      have hle : t - 1 / 85 ≤ kSq * t ^ 2 := by
        rw [hk, ht3]
        norm_num
      rw [min_eq_right hle, hW1, hUU, ht3]
      norm_num
    · rw [hW1, hmm, hUU]
      ring

end Omega3
