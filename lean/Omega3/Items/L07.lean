import Omega3.Statements
import Omega3.Items.L07_Gen
import Omega3.Items.L07_Fej

/-!
# L07: record numerics for every base `b ≥ 5` (plan in `L07_PLAN.md`)
-/

namespace Omega3

open Finset

/-- Fejér bases: the two scalar checks give the conclusion. -/
lemma L07_fej_case (hF : FejerM4Stmt) (b : ℕ) (hb : 5 ≤ b) (h6 : b ≠ 6) (h8 : b ≠ 8)
    (hp0 : 0 < recP b) (hp1 : recP b < 1)
    (hτ : ((1 - recP b) + recP b * (1 / (mB b : ℝ))) ^ 25 * (b : ℝ) ^ 17 < 1)
    (hbM : (b : ℝ) * (((151 * ((mB b : ℕ) : ℚ) ^ 6 + 70 * ((mB b : ℕ) : ℚ) ^ 4 +
        49 * ((mB b : ℕ) : ℚ) ^ 2 + 45) / (315 * ((mB b : ℕ) : ℚ) ^ 7) : ℚ) : ℝ) < 1) :
    ∃ ψ lA θw κ : ℝ,
      0 < recTau b 0 ∧ recTau b 0 ≤ (b : ℝ) ^ (-ψ) ∧ trigMass (recH b) (recTau b) ≤ (b : ℝ) ^ lA ∧
      mw4 b (recGR b) ≤ (b : ℝ) ^ (-(1 + θw)) ∧ 0 < θw ∧ 0 < κ ∧
      2 * thS + 2 * κ < ψ + (1 - recP b) * (2 * thS * θw - 2 * κ) / 3 ∧
      lA + 2 * κ < (1 - recP b) * (2 * th0 * θw - 2 * κ) / 3 ∧
      2 * c1 < ψ ∧ 3 * lA < (1 - recP b) * ψ * θw := by
  have hm : 1 ≤ mB b := by unfold mB; omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hmR : (0 : ℝ) < (mB b : ℝ) := by exact_mod_cast hm
  have hlb : 0 < Real.log b := Real.log_pos hbR
  have hτ0 : 0 < recTau b 0 := by
    rw [L07_tau0_fej b h6 h8]
    have : 0 < recP b * (1 / (mB b : ℝ)) := mul_pos hp0 (by positivity)
    linarith
  have hM0 : 0 < mw4 b (recGR b) := by
    rw [L07_mw4_fej hF b h6 h8 hm]
    have : (0 : ℚ) < ((151 * ((mB b : ℕ) : ℚ) ^ 6 + 70 * ((mB b : ℕ) : ℚ) ^ 4 +
        49 * ((mB b : ℕ) : ℚ) ^ 2 + 45) / (315 * ((mB b : ℕ) : ℚ) ^ 7)) := by
      have : (0 : ℚ) < (mB b : ℚ) := by exact_mod_cast hm
      positivity
    exact_mod_cast this
  have hA := L07_mass_fej b h6 h8 hm hp0.le hp1.le
  have hL2 : Real.log b ≤ (b : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have key := L07_gen (b : ℝ) (recTau b 0) (trigMass (recH b) (recTau b)) (mw4 b (recGR b))
    (1 - recP b) (Real.log b) ((b : ℝ) - 1) 0 hbR hlb le_rfl hL2 hτ0
    (by rw [L07_tau0_fej b h6 h8]; exact hτ) hM0
    (by rw [L07_mw4_fej hF b h6 h8 hm]; exact hbM) (by rw [hA]; norm_num) (by rw [hA]; norm_num)
    le_rfl (by linarith) (by linarith)
    (by
      have h1 : 0 < 1 - (b : ℝ) * mw4 b (recGR b) := by
        rw [L07_mw4_fej hF b h6 h8 hm]; linarith
      have h2 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      have h3 : 0 < 1 - recP b := by linarith
      rw [zero_div]
      positivity)
  exact key

/-- `(2b + 1)^25 < b^33` for `b ≥ 16`. -/
lemma L07_pow_ineq (b : ℕ) (hb : 16 ≤ b) : (2 * b + 1) ^ 25 < b ^ 33 := by
  have h1 : 16 * (2 * b + 1) ≤ 33 * b := by omega
  have h2 : (16 * (2 * b + 1)) ^ 25 ≤ (33 * b) ^ 25 := Nat.pow_le_pow_left h1 25
  have h3 : 33 ^ 25 < 16 ^ 33 := by norm_num
  have h4 : 16 ^ 8 ≤ b ^ 8 := Nat.pow_le_pow_left hb 8
  have hb25 : 0 < b ^ 25 := by positivity
  have h5 : 16 ^ 25 * (2 * b + 1) ^ 25 < 16 ^ 25 * b ^ 33 := by
    calc 16 ^ 25 * (2 * b + 1) ^ 25 = (16 * (2 * b + 1)) ^ 25 := by rw [mul_pow]
      _ ≤ (33 * b) ^ 25 := h2
      _ = 33 ^ 25 * b ^ 25 := by rw [mul_pow]
      _ < 16 ^ 33 * b ^ 25 := Nat.mul_lt_mul_of_pos_right h3 hb25
      _ = 16 ^ 25 * (16 ^ 8 * b ^ 25) := by ring
      _ ≤ 16 ^ 25 * (b ^ 8 * b ^ 25) := by gcongr
      _ = 16 ^ 25 * b ^ 33 := by ring
  exact Nat.lt_of_mul_lt_mul_left h5

lemma L07_b6 : ∃ ψ lA θw κ : ℝ,
      0 < recTau 6 0 ∧ recTau 6 0 ≤ ((6 : ℕ) : ℝ) ^ (-ψ) ∧
      trigMass (recH 6) (recTau 6) ≤ ((6 : ℕ) : ℝ) ^ lA ∧
      mw4 6 (recGR 6) ≤ ((6 : ℕ) : ℝ) ^ (-(1 + θw)) ∧ 0 < θw ∧ 0 < κ ∧
      2 * thS + 2 * κ < ψ + (1 - recP 6) * (2 * thS * θw - 2 * κ) / 3 ∧
      lA + 2 * κ < (1 - recP 6) * (2 * th0 * θw - 2 * κ) / 3 ∧
      2 * c1 < ψ ∧ 3 * lA < (1 - recP 6) * ψ * θw := by
  have hP : recP 6 = 1023 / 1024 := L07_recP_small 6 (by norm_num)
  have hτ : recTau 6 0 = 1 / 1024 + 1023 / 1024 * (1321873323313001 / 4503599627370496 : ℝ) := by
    simp [recTau, hP, recPoly, P6list]; norm_num
  have hIcc : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have hA : trigMass (recH 6) (recTau 6) ≤ 1 + 2 / 10 ^ 6 := by
    simp [trigMass, recH, hIcc, recTau, hP, recPoly, P6list]; norm_num
  have hA0 : 0 < trigMass (recH 6) (recTau 6) := by
    have : 0 < |recTau 6 0| := by rw [hτ]; norm_num
    unfold trigMass
    have : 0 ≤ ∑ u ∈ Icc 1 (recH 6), |recTau 6 u| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hM : mw4 6 (recGR 6) = 1 / 6 * (82206936 / 100000000 : ℝ) := by
    simp [mw4, Finset.sum_range_succ, recGR, recG, g6list]; norm_num
  have hlog : (1 : ℝ) ≤ Real.log ((6 : ℕ) : ℝ) := by
    have := Real.exp_one_lt_d9
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by push_cast; linarith)
  have hL2 : Real.log ((6 : ℕ) : ℝ) ≤ ((6 : ℕ) : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have key := L07_gen ((6 : ℕ) : ℝ) (recTau 6 0) (trigMass (recH 6) (recTau 6)) (mw4 6 (recGR 6))
    (1 - recP 6) 1 (((6 : ℕ) : ℝ) - 1) (2 / 10 ^ 6) (by norm_num) one_pos hlog hL2
    (by rw [hτ]; norm_num) (by rw [hτ]; norm_num) (by rw [hM]; norm_num) (by rw [hM]; norm_num)
    hA0 hA (by norm_num) (by rw [hP]; norm_num) (by rw [hP]; norm_num)
    (by rw [hP, hM]; norm_num)
  exact key

lemma L07_b8 : ∃ ψ lA θw κ : ℝ,
      0 < recTau 8 0 ∧ recTau 8 0 ≤ ((8 : ℕ) : ℝ) ^ (-ψ) ∧
      trigMass (recH 8) (recTau 8) ≤ ((8 : ℕ) : ℝ) ^ lA ∧
      mw4 8 (recGR 8) ≤ ((8 : ℕ) : ℝ) ^ (-(1 + θw)) ∧ 0 < θw ∧ 0 < κ ∧
      2 * thS + 2 * κ < ψ + (1 - recP 8) * (2 * thS * θw - 2 * κ) / 3 ∧
      lA + 2 * κ < (1 - recP 8) * (2 * th0 * θw - 2 * κ) / 3 ∧
      2 * c1 < ψ ∧ 3 * lA < (1 - recP 8) * ψ * θw := by
  have hP : recP 8 = 1023 / 1024 := L07_recP_small 8 (by norm_num)
  have hτ : recTau 8 0 = 1 / 1024 + 1023 / 1024 * (8383891917856039 / 36028797018963968 : ℝ) := by
    simp [recTau, hP, recPoly, P8list]; norm_num
  have hIcc : Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  have hA : trigMass (recH 8) (recTau 8) ≤ 1 + 2 / 10 ^ 6 := by
    simp [trigMass, recH, hIcc, recTau, hP, recPoly, P8list]; norm_num
  have hA0 : 0 < trigMass (recH 8) (recTau 8) := by
    have : 0 < |recTau 8 0| := by rw [hτ]; norm_num
    unfold trigMass
    have : 0 ≤ ∑ u ∈ Icc 1 (recH 8), |recTau 8 u| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  have hM : mw4 8 (recGR 8) ≤ 1 / 8 * (8507 / 10000 : ℝ) := by
    simp [mw4, Finset.sum_range_succ, recGR, recG, g8list]; norm_num
  have hM0 : 0 < mw4 8 (recGR 8) := by
    simp [mw4, Finset.sum_range_succ, recGR, recG, g8list]; norm_num
  have hlog : (1 : ℝ) ≤ Real.log ((8 : ℕ) : ℝ) := by
    have := Real.exp_one_lt_d9
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by push_cast; linarith)
  have hL2 : Real.log ((8 : ℕ) : ℝ) ≤ ((8 : ℕ) : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have key := L07_gen ((8 : ℕ) : ℝ) (recTau 8 0) (trigMass (recH 8) (recTau 8)) (mw4 8 (recGR 8))
    (1 - recP 8) 1 (((8 : ℕ) : ℝ) - 1) (2 / 10 ^ 6) (by norm_num) one_pos hlog hL2
    (by rw [hτ]; norm_num) (by rw [hτ]; norm_num) hM0 (by push_cast; linarith)
    hA0 hA (by norm_num) (by rw [hP]; norm_num) (by rw [hP]; norm_num)
    (by
      rw [hP]
      have : 1 - ((8 : ℕ) : ℝ) * mw4 8 (recGR 8) ≥ 1 - 8507 / 10000 := by push_cast; linarith
      have h7 : (((8 : ℕ) : ℝ) - 1) = 7 := by norm_num
      rw [h7]
      have : (1 - 8507 / 10000 : ℝ) / 7 ≤ (1 - ((8 : ℕ) : ℝ) * mw4 8 (recGR 8)) / 7 := by
        linarith
      norm_num at this ⊢
      linarith)
  exact key

theorem itemL07 : ItemL07 := by
  intro hF b hb
  by_cases h6 : b = 6
  · subst h6; exact L07_b6
  by_cases h8 : b = 8
  · subst h8; exact L07_b8
  by_cases hs : b ≤ 15
  · have hP := L07_recP_small b hs
    have hp0 : 0 < recP b := by rw [hP]; norm_num
    have hp1 : recP b < 1 := by rw [hP]; norm_num
    apply L07_fej_case hF b hb h6 h8 hp0 hp1
    · rw [hP]
      interval_cases b <;> first | omega | norm_num [mB]
    · interval_cases b <;> first | omega | norm_num [mB]
  · have hb16 : 16 ≤ b := by omega
    have hP := L07_recP_large b hs
    have hbR : (16 : ℝ) ≤ b := by exact_mod_cast hb16
    have hbpos : (0 : ℝ) < b := by linarith
    have hp0 : 0 < recP b := by
      rw [hP]
      have : 1 / (b : ℝ) ^ 2 ≤ 1 / 16 ^ 2 := by gcongr
      linarith
    have hp1 : recP b < 1 := by
      rw [hP]
      have : 0 < 1 / (b : ℝ) ^ 2 := by positivity
      linarith
    obtain ⟨hm1, hm2⟩ := L07_mB_bounds b
    have hm8 : 8 ≤ mB b := by omega
    have hmR : (8 : ℝ) ≤ (mB b : ℝ) := by exact_mod_cast hm8
    have hbm : (b : ℝ) ≤ 2 * (mB b : ℝ) := by exact_mod_cast hm2
    apply L07_fej_case hF b hb h6 h8 hp0 hp1
    · -- τ₀ ≤ (2b + 1)/b²
      have hq : 1 - recP b = 1 / (b : ℝ) ^ 2 := by rw [hP]; ring
      have hτle : (1 - recP b) + recP b * (1 / (mB b : ℝ)) ≤ (2 * b + 1) / (b : ℝ) ^ 2 := by
        rw [hq]
        have h1 : recP b * (1 / (mB b : ℝ)) ≤ 1 / (mB b : ℝ) := by
          have : 0 ≤ 1 / (mB b : ℝ) := by positivity
          nlinarith
        have h2 : 1 / (mB b : ℝ) ≤ 2 / b := by
          rw [div_le_div_iff₀ (by linarith) hbpos]; linarith
        have h3 : (2 * b + 1) / (b : ℝ) ^ 2 = 1 / (b : ℝ) ^ 2 + 2 / b := by
          field_simp; ring
        rw [h3]; linarith
      have hτ0 : 0 ≤ (1 - recP b) + recP b * (1 / (mB b : ℝ)) := by
        have : 0 ≤ recP b * (1 / (mB b : ℝ)) := mul_nonneg hp0.le (by positivity)
        linarith
      have hNat : (2 * b + 1) ^ 25 * b ^ 17 < (b ^ 2) ^ 25 := by
        have := L07_pow_ineq b hb16
        calc (2 * b + 1) ^ 25 * b ^ 17 < b ^ 33 * b ^ 17 :=
              Nat.mul_lt_mul_of_pos_right this (by positivity)
          _ = (b ^ 2) ^ 25 := by ring
      have hReal : ((2 * b + 1 : ℝ)) ^ 25 * (b : ℝ) ^ 17 < ((b : ℝ) ^ 2) ^ 25 := by
        exact_mod_cast hNat
      calc ((1 - recP b) + recP b * (1 / (mB b : ℝ))) ^ 25 * (b : ℝ) ^ 17
          ≤ ((2 * b + 1) / (b : ℝ) ^ 2) ^ 25 * (b : ℝ) ^ 17 := by gcongr
        _ = ((2 * b + 1 : ℝ)) ^ 25 * (b : ℝ) ^ 17 / ((b : ℝ) ^ 2) ^ 25 := by
            rw [div_pow]; ring
        _ < 1 := by rw [div_lt_one (by positivity)]; exact hReal
    · push_cast
      set t : ℝ := (mB b : ℝ) with ht
      have hM0 : 0 ≤ (151 * t ^ 6 + 70 * t ^ 4 + 49 * t ^ 2 + 45) / (315 * t ^ 7) := by positivity
      have h1 : (b : ℝ) * ((151 * t ^ 6 + 70 * t ^ 4 + 49 * t ^ 2 + 45) / (315 * t ^ 7)) ≤
          (2 * t) * ((151 * t ^ 6 + 70 * t ^ 4 + 49 * t ^ 2 + 45) / (315 * t ^ 7)) :=
        mul_le_mul_of_nonneg_right hbm hM0
      have h2 : (2 * t) * ((151 * t ^ 6 + 70 * t ^ 4 + 49 * t ^ 2 + 45) / (315 * t ^ 7)) < 1 := by
        have ht0 : 0 < t := by linarith
        rw [mul_div_assoc', div_lt_one (by positivity)]
        have hs2 : (64 : ℝ) ≤ t ^ 2 := by nlinarith
        have hp : 0 < t ^ 4 := by positivity
        have key : 140 * t ^ 4 + 98 * t ^ 2 + 90 < 13 * t ^ 6 := by
          have e1 : 13 * t ^ 6 = 13 * t ^ 2 * t ^ 4 := by ring
          have e2 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
          nlinarith
        nlinarith
      linarith

end Omega3
