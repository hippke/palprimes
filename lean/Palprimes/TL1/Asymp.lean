import Palprimes.TL1.PropC
import Palprimes.Level.DivisorBound
import Palprimes.Level.Level

/-! # TL¹ asymptotically (dossier Proposition C, inner-only cut)

With `Y = b^N`, `x = b^{2N+1}`, a block majorant `M` with `T₀₀ ≤ b^{-lψ}`, `A ≤ b^{lλ}` and
* (ii′) `2θ + 4κ ≤ ψ + 2θ θ_b (1-p)/3`,
* (iii′) `λ + 2ε + 4κ ≤ δ θ_b (1-p)/3`,
the Farey sum `Σ_{q∈Qs} Σ*_h F(h/q + β)` is `≤ R₀ Y^{-κ}` for every `R₀ ∈ [Y^δ, x^θ]` once `N` is large.
The threshold is `τ = R₀^{-θ_b/3} Y^{2κ}`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

theorem thetaB_pos (b : ℕ) (hb : 2 ≤ b) : 0 < thetaB b := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  unfold thetaB
  apply Real.logb_pos hb1
  rw [one_lt_div (by positivity)]
  have : (1 : ℝ) < (b : ℝ) ^ 2 := by nlinarith
  linarith

theorem thetaB_le_one (b : ℕ) (hb : 2 ≤ b) : thetaB b ≤ 1 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold thetaB
  have hx : 3 * (b : ℝ) ^ 2 / (2 * (b : ℝ) ^ 2 + 1) ≤ b := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h := Real.logb_le_logb_of_le hb1 (by positivity) hx
  rwa [Real.logb_self_eq_one hb1] at h

/-- `m_b(4) = (2b²+1)/(3b³) = b^{-1-θ_b}`. -/
theorem m4_eq (b : ℕ) (hb : 2 ≤ b) :
    (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3) = (b : ℝ) ^ (-1 - thetaB b) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (b : ℝ) ≠ 1 := by exact_mod_cast (by omega : b ≠ 1)
  rw [Real.rpow_sub hb0, Real.rpow_neg_one, thetaB, Real.rpow_logb hb0 hb1 (by positivity)]
  field_simp

/-- The inner term: `τ^{-3} (…) m₄^j ≤ (16bN+18) b^{1+θ_b} R₀ Y^{-6κ}`. -/
theorem inner_term_le (b : ℕ) (hb : 2 ≤ b) (N j : ℕ) (hj : j ≤ N) (R0 : ℝ) (hR0 : 1 ≤ R0)
    (hbj : (b : ℝ) ^ j ≤ R0) (hbj1 : R0 < (b : ℝ) ^ (j + 1)) (Y κ : ℝ) (hY : 0 < Y) :
    (R0 ^ (-thetaB b / 3) * Y ^ (2 * κ))⁻¹ ^ 3 *
        ((4 * ((4 * b * j * b ^ (2 * j) + 1 : ℕ) : ℝ) + 12 * R0 ^ 2 + 2) *
          (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ j)) ≤
      (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b) * R0 * Y ^ (-(6 * κ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hR00 : 0 < R0 := by linarith
  set θ := thetaB b with hθ
  have hθ0 := thetaB_pos b hb
  -- τ⁻³ = R₀^θ Y^{-6κ}
  have hτ : (R0 ^ (-θ / 3) * Y ^ (2 * κ))⁻¹ ^ 3 = R0 ^ θ * Y ^ (-(6 * κ)) := by
    rw [inv_pow, mul_pow, ← Real.rpow_natCast (R0 ^ (-θ / 3)), ← Real.rpow_natCast (Y ^ (2 * κ)),
      ← Real.rpow_mul hR00.le, ← Real.rpow_mul hY.le]
    push_cast
    rw [show -θ / 3 * 3 = -θ by ring, show 2 * κ * 3 = 6 * κ by ring, Real.rpow_neg hR00.le,
      Real.rpow_neg hY.le]
    field_simp
  -- the bracket
  have hbr : (4 * ((4 * b * j * b ^ (2 * j) + 1 : ℕ) : ℝ) + 12 * R0 ^ 2 + 2) ≤
      (16 * b * N + 18) * R0 ^ 2 := by
    push_cast
    have h1 : ((b : ℝ) ^ (2 * j)) ≤ R0 ^ 2 := by
      rw [pow_mul, show ((b : ℝ) ^ 2) ^ j = ((b : ℝ) ^ j) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) hbj 2
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hR2 : 1 ≤ R0 ^ 2 := by nlinarith
    have h2 : (b : ℝ) * j * (b : ℝ) ^ (2 * j) ≤ b * N * R0 ^ 2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hjN hb0.le) h1 (by positivity) (by positivity)
    nlinarith
  -- m₄^j ≤ b^{1+θ} R₀^{-1-θ}
  have hm : ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ j ≤ (b : ℝ) ^ (1 + θ) * R0 ^ (-1 - θ) := by
    rw [m4_eq b hb, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    have hR' : R0 / b < (b : ℝ) ^ j := by
      rw [div_lt_iff₀ hb0, ← pow_succ]; exact hbj1
    have hRb : 0 < R0 / b := by positivity
    calc (b : ℝ) ^ ((-1 - θ) * (j : ℝ)) = ((b : ℝ) ^ (j : ℝ)) ^ (-1 - θ) := by
          rw [← Real.rpow_mul hb0.le, mul_comm]
      _ ≤ (R0 / b) ^ (-1 - θ) := by
          rw [Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_nonpos hRb hR'.le (by linarith)
      _ = (b : ℝ) ^ (1 + θ) * R0 ^ (-1 - θ) := by
          rw [Real.div_rpow hR00.le hb0.le, div_eq_mul_inv, ← Real.rpow_neg hb0.le, mul_comm]
          ring_nf
  rw [hτ]
  have hm0 : 0 ≤ ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ j := by positivity
  calc R0 ^ θ * Y ^ (-(6 * κ)) *
        ((4 * ((4 * b * j * b ^ (2 * j) + 1 : ℕ) : ℝ) + 12 * R0 ^ 2 + 2) *
          (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ j))
      ≤ R0 ^ θ * Y ^ (-(6 * κ)) * ((16 * b * N + 18) * R0 ^ 2 * ((b : ℝ) ^ (1 + θ) * R0 ^ (-1 - θ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hbr hm hm0 (by positivity)
    _ = (16 * b * N + 18) * (b : ℝ) ^ (1 + θ) * (R0 ^ θ * R0 ^ (2 : ℝ) * R0 ^ (-1 - θ)) * Y ^ (-(6 * κ)) := by
        rw [show (R0 ^ (2 : ℝ)) = R0 ^ 2 by norm_cast]; ring
    _ = (16 * b * N + 18) * (b : ℝ) ^ (1 + θ) * R0 * Y ^ (-(6 * κ)) := by
        rw [← Real.rpow_add hR00, ← Real.rpow_add hR00, show θ + 2 + (-1 - θ) = 1 by ring, Real.rpow_one]

/-- `x^a = exp(a log x)` for `x > 0`. -/
theorem rpow_eq_exp (x a : ℝ) (hx : 0 < x) : x ^ a = Real.exp (a * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

/-- The majorant term: `τ^{1-p} S t^R ≤ 4 b^{lψ+θ} R₀ Y^{-2κ}`. -/
theorem small_term_le (b l N R : ℕ) (hb : 2 ≤ b) (hlR : N ≤ l * R + l)
    (p ψ θ κ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hψ : 0 ≤ ψ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (hii : 2 * θ + 4 * κ ≤ ψ + 2 * θ * thetaB b * (1 - p) / 3)
    (R0 : ℝ) (hR0 : 1 ≤ R0) (hRx : R0 ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ)
    (S t : ℝ) (_hS0 : 0 ≤ S) (hS : S ≤ 4 * R0 ^ 2) (ht0 : 0 ≤ t) (ht : t ≤ (b : ℝ) ^ (-((l : ℝ) * ψ))) :
    (R0 ^ (-thetaB b / 3) * ((b : ℝ) ^ N) ^ (2 * κ)) ^ (1 - p) * (S * t ^ R) ≤
      4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) * R0 * ((b : ℝ) ^ N) ^ (-(2 * κ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hR00 : 0 < R0 := by linarith
  have hY0 : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  set β := Real.log b with hβ
  have hβ0 : 0 ≤ β := Real.log_nonneg hb1
  set r := Real.log R0 with hr
  have hr0 : 0 ≤ r := Real.log_nonneg hR0
  have hL : Real.log ((b : ℝ) ^ N) = N * β := by rw [Real.log_pow]
  have hθb0 := (thetaB_pos b hb).le
  have hθb1 := thetaB_le_one b hb
  -- log R₀ ≤ θ (2N+1) β
  have hrx : r ≤ θ * ((2 * N + 1) * β) := by
    have := Real.log_le_log hR00 hRx
    rw [Real.log_rpow (by positivity), Real.log_pow] at this
    push_cast at this; linarith
  -- bound t^R and S
  have htR : t ^ R ≤ Real.exp (-((l : ℝ) * ψ * R * β)) := by
    calc t ^ R ≤ ((b : ℝ) ^ (-((l : ℝ) * ψ))) ^ R := pow_le_pow_left₀ ht0 ht R
      _ = Real.exp (-((l : ℝ) * ψ * R * β)) := by
          rw [rpow_eq_exp _ _ hb0, ← Real.exp_natCast_mul]; congr 1; ring
  have hS' : S ≤ 4 * Real.exp (2 * r) := by
    rw [show 2 * r = (2 : ℕ) * r by norm_num, Real.exp_natCast_mul, Real.exp_log hR00]; exact hS
  have hτ : (R0 ^ (-thetaB b / 3) * ((b : ℝ) ^ N) ^ (2 * κ)) ^ (1 - p) =
      Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β))) := by
    rw [rpow_eq_exp _ _ hR00, rpow_eq_exp _ _ hY0, hL, ← Real.exp_add, ← Real.exp_mul]
    congr 1; ring
  have hrhs : 4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) * R0 * ((b : ℝ) ^ N) ^ (-(2 * κ)) =
      4 * Real.exp (((l : ℝ) * ψ + θ) * β + r - 2 * κ * (N * β)) := by
    rw [rpow_eq_exp _ _ hb0, rpow_eq_exp _ _ hY0, hL]
    conv_lhs => rw [show R0 = Real.exp r from (Real.exp_log hR00).symm]
    rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  rw [hτ, hrhs]
  calc Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β))) * (S * t ^ R)
      ≤ Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β))) *
          (4 * Real.exp (2 * r) * Real.exp (-((l : ℝ) * ψ * R * β))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul hS' htR (pow_nonneg ht0 _) (by positivity)
    _ = 4 * Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β)) + 2 * r - (l : ℝ) * ψ * R * β) := by
        rw [show (1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β)) + 2 * r - (l : ℝ) * ψ * R * β =
          (1 - p) * (-thetaB b / 3 * r + 2 * κ * (N * β)) + 2 * r + -((l : ℝ) * ψ * R * β) by ring,
          Real.exp_add, Real.exp_add]; ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2
        -- linear algebra in r, Nβ
        have hlR' : (N : ℝ) ≤ l * R + l := by exact_mod_cast hlR
        set c := 1 - (1 - p) * thetaB b / 3 with hc
        have hc0 : 0 ≤ c := by
          have : (1 - p) * thetaB b ≤ 1 := by nlinarith
          linarith
        have h1 : c * r ≤ c * (θ * ((2 * N + 1) * β)) := mul_le_mul_of_nonneg_left hrx hc0
        have hc1 : c ≤ 1 := by
          have : 0 ≤ (1 - p) * thetaB b := by nlinarith
          linarith
        have h2 : c * (θ * ((2 * N + 1) * β)) ≤ 2 * θ * c * (N * β) + θ * β := by
          have : c * (θ * β) ≤ θ * β := by
            have := mul_le_mul_of_nonneg_right hc1 (by positivity : 0 ≤ θ * β)
            linarith
          nlinarith
        have h3 : ψ * (N * β) ≤ (l : ℝ) * ψ * R * β + (l : ℝ) * ψ * β := by
          have := mul_le_mul_of_nonneg_left hlR' (by positivity : 0 ≤ ψ * β)
          nlinarith
        have hNβ : 0 ≤ (N : ℝ) * β := by positivity
        have h4 : (2 * θ * c + 2 * κ * (2 - p)) * (N * β) ≤ ψ * (N * β) := by
          apply mul_le_mul_of_nonneg_right _ hNβ
          have : 2 * κ * (2 - p) ≤ 4 * κ := by nlinarith
          have : 2 * θ * c = 2 * θ - 2 * θ * thetaB b * (1 - p) / 3 := by rw [hc]; ring
          linarith
        nlinarith

/-- The divisor term: `τ^{1-p} · 2R₀ · T_div · A^R ≤ 2 C (2N b^l)^ε R₀ Y^{-2κ}`. -/
theorem div_term_le (b l N R : ℕ) (hb : 2 ≤ b) (hlR : l * R ≤ N)
    (p lamA δ κ ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlam : 0 ≤ lamA) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hiii : lamA + 2 * ε + 4 * κ ≤ δ * thetaB b * (1 - p) / 3)
    (R0 : ℝ) (hR0 : 1 ≤ R0) (hRY : ((b : ℝ) ^ N) ^ δ ≤ R0)
    (C W A : ℝ) (hC : 0 ≤ C) (hW0 : 0 ≤ W) (hW : W ≤ 2 * N * (b : ℝ) ^ l * ((b : ℝ) ^ N) ^ 2)
    (hA0 : 0 ≤ A) (hA : A ≤ (b : ℝ) ^ ((l : ℝ) * lamA)) :
    (R0 ^ (-thetaB b / 3) * ((b : ℝ) ^ N) ^ (2 * κ)) ^ (1 - p) * (2 * R0 * (C * W ^ ε) * A ^ R) ≤
      2 * C * (2 * N * (b : ℝ) ^ l) ^ ε * R0 * ((b : ℝ) ^ N) ^ (-(2 * κ)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hR00 : 0 < R0 := by linarith
  have hY0 : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  have hY1 : (1 : ℝ) ≤ (b : ℝ) ^ N := one_le_pow₀ hb1
  set β := Real.log b with hβ
  have hβ0 : 0 ≤ β := Real.log_nonneg hb1
  set L := Real.log ((b : ℝ) ^ N) with hLdef
  have hL : L = N * β := by rw [hLdef, Real.log_pow]
  have hL0 : 0 ≤ L := Real.log_nonneg hY1
  set r := Real.log R0 with hr
  have hθb0 := (thetaB_pos b hb).le
  have hrY : δ * L ≤ r := by
    have := Real.log_le_log (by positivity) hRY
    rwa [Real.log_rpow hY0] at this
  -- pieces
  have hWe : W ^ ε ≤ (2 * N * (b : ℝ) ^ l) ^ ε * Real.exp (2 * ε * L) := by
    calc W ^ ε ≤ (2 * N * (b : ℝ) ^ l * ((b : ℝ) ^ N) ^ 2) ^ ε := Real.rpow_le_rpow hW0 hW hε
      _ = (2 * N * (b : ℝ) ^ l) ^ ε * (((b : ℝ) ^ N) ^ 2) ^ ε := Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le, rpow_eq_exp _ _ hY0]; congr 1
  have hAR : A ^ R ≤ Real.exp (lamA * L) := by
    calc A ^ R ≤ ((b : ℝ) ^ ((l : ℝ) * lamA)) ^ R := pow_le_pow_left₀ hA0 hA R
      _ = Real.exp ((l : ℝ) * R * lamA * β) := by
          rw [rpow_eq_exp _ _ hb0, ← Real.exp_natCast_mul]; congr 1; ring
      _ ≤ Real.exp (lamA * L) := by
          apply Real.exp_le_exp.2
          have : (l : ℝ) * R ≤ N := by exact_mod_cast hlR
          have h := mul_le_mul_of_nonneg_right this (mul_nonneg hlam hβ0)
          rw [hL]; nlinarith
  have hτ : (R0 ^ (-thetaB b / 3) * ((b : ℝ) ^ N) ^ (2 * κ)) ^ (1 - p) =
      Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * L)) := by
    rw [rpow_eq_exp _ _ hR00, rpow_eq_exp _ _ hY0, ← Real.exp_add, ← Real.exp_mul]
    congr 1; ring
  have hYk : ((b : ℝ) ^ N) ^ (-(2 * κ)) = Real.exp (-(2 * κ) * L) := rpow_eq_exp _ _ hY0
  rw [hτ, hYk]
  have hexp : (1 - p) * (-thetaB b / 3 * r + 2 * κ * L) + 2 * ε * L + lamA * L ≤ -(2 * κ) * L := by
    have h1 : (1 - p) * thetaB b / 3 * (δ * L) ≤ (1 - p) * thetaB b / 3 * r :=
      mul_le_mul_of_nonneg_left hrY (div_nonneg (mul_nonneg (by linarith) hθb0) (by norm_num))
    have h2 : (1 - p) * (2 * κ * L) ≤ 2 * κ * L := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - p ≤ 1) (by positivity : 0 ≤ 2 * κ * L)
      linarith
    have h3 : (lamA + 2 * ε + 4 * κ) * L ≤ (δ * thetaB b * (1 - p) / 3) * L :=
      mul_le_mul_of_nonneg_right hiii hL0
    nlinarith
  have hE := Real.exp_le_exp.2 hexp
  rw [Real.exp_add, Real.exp_add] at hE
  have hP : 0 ≤ (2 * N * (b : ℝ) ^ l) ^ ε := by positivity
  calc Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * L)) * (2 * R0 * (C * W ^ ε) * A ^ R)
      ≤ Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * L)) *
          (2 * R0 * (C * ((2 * N * (b : ℝ) ^ l) ^ ε * Real.exp (2 * ε * L))) * Real.exp (lamA * L)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply mul_le_mul _ hAR (pow_nonneg hA0 _) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hWe hC
    _ = 2 * C * (2 * N * (b : ℝ) ^ l) ^ ε * R0 *
          (Real.exp ((1 - p) * (-thetaB b / 3 * r + 2 * κ * L)) * Real.exp (2 * ε * L) * Real.exp (lamA * L)) := by
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hE (by positivity)

/-- Divisor count of a filtered modulus set. -/
theorem card_filter_dvd_le_divisors (Qs : Finset ℕ) (_hQ : ∀ q ∈ Qs, 0 < q) (w : ℤ) (hw : w ≠ 0) :
    #(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) ≤ #(w.natAbs.divisors) := by
  apply Finset.card_le_card
  intro q hq
  rw [mem_filter] at hq
  exact Nat.mem_divisors.2 ⟨Int.natCast_dvd.1 hq.2, Int.natAbs_ne_zero.2 hw⟩

set_option maxHeartbeats 4000000 in
/-- **TL¹ asymptotically.** -/
theorem tl1_eventually {b l : ℕ} (M : BlockMaj b l) (hb : 2 ≤ b) (hl : 1 ≤ l)
    (ψ lamA θ δ κ ε : ℝ) (hψ : 0 ≤ ψ) (hlam : 0 ≤ lamA) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hδ : 0 ≤ δ)
    (hκ : 0 < κ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hp0 : 0 ≤ M.p)
    (ht0 : 0 ≤ M.t00) (ht : M.t00 ≤ (b : ℝ) ^ (-((l : ℝ) * ψ))) (hA : M.A ≤ (b : ℝ) ^ ((l : ℝ) * lamA))
    (hii : 2 * θ + 4 * κ ≤ ψ + 2 * θ * thetaB b * (1 - M.p) / 3)
    (hiii : lamA + 2 * ε + 4 * κ ≤ δ * thetaB b * (1 - M.p) / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ δ ≤ R0 → (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ) := by
  classical
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow ε hε0
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl; simp at this; linarith
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  -- the constant
  set K : ℝ := 4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) + 4 * Ce * (b : ℝ) ^ l +
    (16 * b + 18) * (b : ℝ) ^ (1 + thetaB b) with hK
  have hρ0 : (0 : ℝ) ≤ (b : ℝ) ^ (-κ) := by positivity
  have hρ1 : (b : ℝ) ^ (-κ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  obtain ⟨N1, hN1⟩ := eventually_poly_geom K 1 _ hρ0 hρ1 1 one_pos
  -- `θ(2N+1) < N` eventually
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ N ≥ N2, θ * (2 * N + 1) < N := by
    obtain ⟨N2, hN2⟩ := exists_nat_gt (θ / (1 - 2 * θ))
    refine ⟨N2, fun N hN => ?_⟩
    have h1 : θ / (1 - 2 * θ) < N := lt_of_lt_of_le hN2 (by exact_mod_cast hN)
    have h2 : 0 < 1 - 2 * θ := by linarith
    rw [div_lt_iff₀ h2] at h1
    nlinarith
  refine ⟨max (max N1 N2) 2, fun N hN R0 hRY hRx Qs hQs β => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2'' : 2 ≤ N := le_trans (le_max_right _ _) hN
  set Y : ℝ := (b : ℝ) ^ N with hY
  have hY0 : 0 < Y := by positivity
  have hY1 : 1 ≤ Y := one_le_pow₀ hb1.le
  -- R₀ ≥ 1 and R₀ < b^N
  have hR01 : 1 ≤ (R0 : ℝ) := le_trans (Real.one_le_rpow hY1 hδ) hRY
  have hR0n : 1 ≤ R0 := by exact_mod_cast hR01
  have hR0lt : (R0 : ℝ) < (b : ℝ) ^ N := by
    calc (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ := hRx
      _ = (b : ℝ) ^ (θ * (2 * N + 1)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
      _ < (b : ℝ) ^ (N : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hb1 (hN2 N hN2')
      _ = _ := Real.rpow_natCast _ _
  -- parameters
  set j := Nat.log b R0 with hj
  have hbj : (b : ℝ) ^ j ≤ R0 := by exact_mod_cast Nat.pow_log_le_self b (by omega)
  have hbj1 : (R0 : ℝ) < (b : ℝ) ^ (j + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by omega) R0
  have hjN : j < N := by
    have : (b : ℝ) ^ j < (b : ℝ) ^ N := lt_of_le_of_lt hbj hR0lt
    exact (pow_lt_pow_iff_right₀ hb1).1 this
  set m := N - j with hm
  set R := (N - 1) / l with hRdef
  have hlR1 : l * R + 1 ≤ N := by
    have h1 : R * l ≤ N - 1 := Nat.div_mul_le_self (N - 1) l
    have : l * R = R * l := mul_comm _ _
    omega
  have hlR2 : N ≤ l * R + l := by
    have h2 : N - 1 < l * (R + 1) := Nat.lt_mul_div_succ (N - 1) (by omega : 0 < l)
    have : l * (R + 1) = l * R + l := by ring
    omega
  set W : ℝ := (R : ℝ) * (2 * ((b : ℝ) ^ l * (b : ℝ) ^ (2 * N))) with hW
  set τ : ℝ := (R0 : ℝ) ^ (-thetaB b / 3) * Y ^ (2 * κ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hQpos : ∀ q ∈ Qs, 0 < q := fun q hq => by have := (hQs q hq).1; omega
  have hT : ∀ w : ℤ, w ≠ 0 → |w| ≤ (R : ℤ) * (2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N))) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ Ce * W ^ ε := by
    intro w hw hwle
    have h1 := card_filter_dvd_le_divisors Qs hQpos w hw
    have h2 := hCe w.natAbs (Int.natAbs_pos.2 hw)
    have h3 : (w.natAbs : ℝ) ≤ W := by
      have h3' : ((w.natAbs : ℤ) : ℝ) ≤ (((R : ℤ) * (2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N))) : ℤ) : ℝ) := by
        rw [Int.natCast_natAbs]; exact_mod_cast hwle
      calc (w.natAbs : ℝ) = ((w.natAbs : ℤ) : ℝ) := (Int.cast_natCast _).symm
        _ ≤ _ := h3'
        _ = W := by rw [hW]; push_cast; ring
    calc (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ #(w.natAbs.divisors) := by exact_mod_cast h1
      _ ≤ Ce * (w.natAbs : ℝ) ^ ε := h2
      _ ≤ Ce * W ^ ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h3 hε0.le) hCe0
  have hfin := tl1_finite M hb hl N R m hlR1 (by omega) (by omega) R0 hR0n Qs hQs (Ce * W ^ ε)
    (by positivity) hT τ hτ0 β
  have hNm : N - m = j := by omega
  rw [hNm] at hfin
  -- the three terms
  have hsumq : (∑ q ∈ Qs, (q : ℝ)) ≤ 4 * (R0 : ℝ) ^ 2 := by
    have hsub : Qs ⊆ Icc R0 (2 * R0) := fun q hq => mem_Icc.2 ⟨(hQs q hq).1, (hQs q hq).2.1⟩
    have hc : (#Qs : ℝ) ≤ R0 + 1 := by
      have := card_le_card hsub; rw [Nat.card_Icc] at this
      have : #Qs ≤ R0 + 1 := by omega
      exact_mod_cast this
    calc (∑ q ∈ Qs, (q : ℝ)) ≤ ∑ _q ∈ Qs, (2 * (R0 : ℝ)) :=
          Finset.sum_le_sum (fun q hq => by exact_mod_cast (hQs q hq).2.1)
      _ = #Qs * (2 * (R0 : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R0 + 1) * (2 * (R0 : ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ 4 * (R0 : ℝ) ^ 2 := by nlinarith
  have hS1 := small_term_le b l N R hb hlR2 M.p ψ θ κ hp0 M.hp1 hψ hθ0 hκ.le hii (R0 : ℝ) hR01 hRx
    _ _ (Finset.sum_nonneg (fun q _ => by positivity)) hsumq ht0 ht
  have hWle : W ≤ 2 * N * (b : ℝ) ^ l * Y ^ 2 := by
    have hRN : (R : ℝ) ≤ N := by
      have : R ≤ N := le_trans (Nat.div_le_self _ _) (by omega)
      exact_mod_cast this
    rw [hW, hY, ← pow_mul, mul_comm N 2]
    have : (0 : ℝ) ≤ 2 * ((b : ℝ) ^ l * (b : ℝ) ^ (2 * N)) := by positivity
    nlinarith
  have hA0 : 0 ≤ M.A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hS2 := div_term_le b l N R hb (by omega) M.p lamA δ κ ε hp0 M.hp1 hlam hε0.le hκ.le hiii
    (R0 : ℝ) hR01 hRY Ce W M.A hCe0 (by positivity) hWle hA0 hA
  have hS3 := inner_term_le b hb N j hjN.le (R0 : ℝ) hR01 hbj hbj1 Y κ hY0
  -- combine
  have hY6 : Y ^ (-(6 * κ)) ≤ Y ^ (-(2 * κ)) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith only [hκ])
  have hP : (2 * N * (b : ℝ) ^ l) ^ ε ≤ 2 * N * (b : ℝ) ^ l := by
    have : (1 : ℝ) ≤ 2 * N * (b : ℝ) ^ l := by
      have : (1 : ℝ) ≤ (b : ℝ) ^ l := one_le_pow₀ hb1.le
      have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN2''
      nlinarith only [this, h2N]
    calc (2 * N * (b : ℝ) ^ l) ^ ε ≤ (2 * N * (b : ℝ) ^ l) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le this hε1
      _ = _ := Real.rpow_one _
  have hθb := thetaB_le_one b hb
  have hYk : Y ^ (-(2 * κ)) * (K * ((N : ℝ) + 1)) ≤ Y ^ (-κ) := by
    have h1 := hN1 N hN1'
    have e : ((b : ℝ) ^ (-κ)) ^ N = Y ^ (-κ) := by
      rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_natCast ((b : ℝ)), ← Real.rpow_mul hb0.le,
        mul_comm]
    rw [e, pow_one] at h1
    have e2 : Y ^ (-(2 * κ)) = Y ^ (-κ) * Y ^ (-κ) := by
      rw [← Real.rpow_add hY0]; ring_nf
    rw [e2]
    have : Y ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
    have h0 : 0 ≤ Y ^ (-κ) := by positivity
    nlinarith
  have hKN : 4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) + 2 * Ce * (2 * N * (b : ℝ) ^ l) ^ ε +
      (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b) ≤ K * ((N : ℝ) + 1) := by
    rw [hK]
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have e1 : 0 ≤ (b : ℝ) ^ ((l : ℝ) * ψ + θ) := by positivity
    have e2 : 0 ≤ (b : ℝ) ^ (1 + thetaB b) := by positivity
    have e3 : 0 ≤ Ce * (b : ℝ) ^ l := by positivity
    have : 2 * Ce * (2 * N * (b : ℝ) ^ l) ^ ε ≤ 4 * Ce * (b : ℝ) ^ l * N :=
      by nlinarith [mul_le_mul_of_nonneg_left hP hCe0]
    nlinarith
  calc ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β)
      ≤ _ := hfin
    _ = τ ^ (1 - M.p) * ((∑ q ∈ Qs, (q : ℝ)) * M.t00 ^ R) +
        τ ^ (1 - M.p) * (2 * R0 * (Ce * W ^ ε) * M.A ^ R) +
        τ⁻¹ ^ 3 * ((4 * ((4 * b * j * b ^ (2 * j) + 1 : ℕ) : ℝ) + 12 * (R0 : ℝ) ^ 2 + 2) *
          (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ j)) := by ring
    _ ≤ 4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) * R0 * Y ^ (-(2 * κ)) +
        2 * Ce * (2 * N * (b : ℝ) ^ l) ^ ε * R0 * Y ^ (-(2 * κ)) +
        (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b) * R0 * Y ^ (-(2 * κ)) := by
        have h3 : (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b) * R0 * Y ^ (-(6 * κ)) ≤
            (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b) * R0 * Y ^ (-(2 * κ)) :=
          mul_le_mul_of_nonneg_left hY6 (by positivity)
        linarith
    _ = R0 * (Y ^ (-(2 * κ)) * (4 * (b : ℝ) ^ ((l : ℝ) * ψ + θ) + 2 * Ce * (2 * N * (b : ℝ) ^ l) ^ ε +
        (16 * b * N + 18) * (b : ℝ) ^ (1 + thetaB b))) := by ring
    _ ≤ R0 * (Y ^ (-(2 * κ)) * (K * ((N : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hKN (by positivity)
    _ ≤ R0 * Y ^ (-κ) := mul_le_mul_of_nonneg_left hYk (by positivity)

end Palprimes
