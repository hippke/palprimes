import Omega3.Statements

/-!
# L07 helper: the generic real lemma (exponents chosen so that the `rpow` bounds are equalities)
-/

namespace Omega3

open Real

lemma L07_gen (b τ0 A M q L1 L2 e : ℝ) (hb : 1 < b) (hL1 : 0 < L1) (hL1b : L1 ≤ Real.log b)
    (hL2b : Real.log b ≤ L2) (hτ0 : 0 < τ0) (hτ : τ0 ^ 25 * b ^ 17 < 1) (hM : 0 < M) (hbM : b * M < 1)
    (hA : 0 < A) (hAe : A ≤ 1 + e) (he : 0 ≤ e) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hS2 : e / L1 < q * (3 / 5 * ((1 - b * M) / L2)) / 3) :
    ∃ ψ lA θw κ : ℝ,
      0 < τ0 ∧ τ0 ≤ b ^ (-ψ) ∧ A ≤ b ^ lA ∧ M ≤ b ^ (-(1 + θw)) ∧ 0 < θw ∧ 0 < κ ∧
      2 * thS + 2 * κ < ψ + q * (2 * thS * θw - 2 * κ) / 3 ∧
      lA + 2 * κ < q * (2 * th0 * θw - 2 * κ) / 3 ∧
      2 * c1 < ψ ∧ 3 * lA < q * ψ * θw := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hbM0 : 0 < b * M := mul_pos hb0 hM
  -- ψ
  set ψ := -Real.log τ0 / Real.log b with hψ
  have hψeq : b ^ (-ψ) = τ0 := by
    rw [Real.rpow_def_of_pos hb0, hψ]
    have : Real.log b * -(-Real.log τ0 / Real.log b) = Real.log τ0 := by
      field_simp
    rw [this, Real.exp_log hτ0]
  have hψgt : 17 / 25 < ψ := by
    have h1 : Real.log (τ0 ^ 25 * b ^ 17) < 0 :=
      Real.log_neg (by positivity) hτ
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h1
    rw [hψ, lt_div_iff₀ hlb]
    push_cast at h1
    linarith
  -- θw
  set θw := -Real.log (b * M) / Real.log b with hθ
  have hθeq : b ^ (-(1 + θw)) = M := by
    rw [Real.rpow_def_of_pos hb0, hθ]
    have : Real.log b * -(1 + -Real.log (b * M) / Real.log b) = Real.log M := by
      rw [Real.log_mul hb0.ne' hM.ne']
      field_simp
      ring
    rw [this, Real.exp_log hM]
  have hL2 : 0 < L2 := lt_of_lt_of_le hlb hL2b
  have hθlow : (1 - b * M) / L2 ≤ θw := by
    have h1 : 1 - b * M ≤ -Real.log (b * M) := by
      have := Real.log_le_sub_one_of_pos hbM0
      linarith
    have h2 : 0 ≤ 1 - b * M := by linarith
    rw [hθ]
    calc (1 - b * M) / L2 ≤ (1 - b * M) / Real.log b := div_le_div_of_nonneg_left h2 hlb hL2b
      _ ≤ -Real.log (b * M) / Real.log b := div_le_div_of_nonneg_right h1 hlb.le
  have hΘ0 : 0 < (1 - b * M) / L2 := div_pos (by linarith) hL2
  have hθpos : 0 < θw := lt_of_lt_of_le hΘ0 hθlow
  -- lA
  set lA := max 0 (Real.log A / Real.log b) with hlA
  have hAle : A ≤ b ^ lA := by
    have h1 : b ^ (Real.log A / Real.log b) = A := by
      rw [Real.rpow_def_of_pos hb0]
      have : Real.log b * (Real.log A / Real.log b) = Real.log A := by field_simp
      rw [this, Real.exp_log hA]
    calc A = b ^ (Real.log A / Real.log b) := h1.symm
      _ ≤ b ^ lA := Real.rpow_le_rpow_of_exponent_le hb.le (le_max_right _ _)
  have hlA0 : 0 ≤ lA := le_max_left _ _
  have hlAe : lA ≤ e / L1 := by
    have hlogA : Real.log A ≤ e := by
      have := Real.log_le_sub_one_of_pos hA
      linarith
    apply max_le (div_nonneg he hL1.le)
    calc Real.log A / Real.log b ≤ e / Real.log b := div_le_div_of_nonneg_right hlogA hlb.le
      _ ≤ e / L1 := div_le_div_of_nonneg_left he hL1 hL1b
  -- κ
  have hthS : thS = 17 / 50 := rfl
  have hth0 : th0 = 3 / 10 := rfl
  have hc1 : c1 = 83 / 250 := rfl
  set d1 := ψ + q * (2 * thS * θw) / 3 - 2 * thS with hd1
  set d2 := q * (2 * th0 * θw) / 3 - lA with hd2
  have hqθ : 0 ≤ q * θw := mul_nonneg hq0.le hθpos.le
  have hd1p : 0 < d1 := by
    rw [hd1, hthS]
    nlinarith
  have hd2p : 0 < d2 := by
    rw [hd2, hth0]
    have : q * (3 / 5 * ((1 - b * M) / L2)) ≤ q * (3 / 5 * θw) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    nlinarith
  set κ := min d1 d2 / 4 with hκ
  have hκp : 0 < κ := by
    rw [hκ]
    exact div_pos (lt_min hd1p hd2p) (by norm_num)
  have hκ1 : κ ≤ d1 / 4 := by
    rw [hκ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκ2 : κ ≤ d2 / 4 := by
    rw [hκ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hqκ : q * κ ≤ κ := by nlinarith
  refine ⟨ψ, lA, θw, κ, hτ0, hψeq.ge, hAle, hθeq.ge, hθpos, hκp, ?_, ?_, ?_, ?_⟩
  · have : q * (2 * thS * θw - 2 * κ) / 3 = q * (2 * thS * θw) / 3 - 2 * (q * κ) / 3 := by ring
    rw [this]
    linarith
  · have : q * (2 * th0 * θw - 2 * κ) / 3 = q * (2 * th0 * θw) / 3 - 2 * (q * κ) / 3 := by ring
    rw [this]
    linarith
  · rw [hc1]; linarith
  · have h1 : q * (17 / 25) * ((1 - b * M) / L2) ≤ q * ψ * θw := by
      have hq17 : q * (17 / 25) ≤ q * ψ := mul_le_mul_of_nonneg_left hψgt.le hq0.le
      exact mul_le_mul hq17 hθlow hΘ0.le (by nlinarith)
    linarith

end Omega3
