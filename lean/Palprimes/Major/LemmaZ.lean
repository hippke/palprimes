import Mathlib

/-! # Lemma Z (dossier §2.13.1)

For `0 < p ≤ 1`, `2M² ≤ p b²` and `0 < t < 1/b`:
`(sin(πbt)/(b sin πt))^p ≤ (sin(πMt)/(M sin πt))²`.
Proof through the Euler product `sin(πx)/(πx) = Π_j (1 − x²/(j+1)²)`: factorwise Bernoulli
`A^p ≤ 1 + p(A − 1)` and an elementary inequality, then a limit. -/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace Palprimes

/-- Partial Euler product. -/
noncomputable def eulP (n : ℕ) (x : ℝ) : ℝ := ∏ j ∈ range n, (1 - x ^ 2 / ((j : ℝ) + 1) ^ 2)

theorem tendsto_eulP (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n => eulP n x) atTop (𝓝 (Real.sin (π * x) / (π * x))) := by
  have h := (Real.tendsto_euler_sin_prod x).div_const (π * x)
  have hpx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  refine h.congr (fun n => ?_)
  unfold eulP
  field_simp

/-- One factor: `((1 − c)/(1 − u))^p ≤ ((1 − a)/(1 − u))²` for `2a ≤ pc`, `0 < u ≤ c < 1`. -/
theorem factor_ineq (p a c u : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu : 0 < u) (huc : u ≤ c) (hc : c < 1)
    (ha0 : 0 ≤ a) (hac : 2 * a ≤ p * c) :
    ((1 - c) / (1 - u)) ^ p ≤ ((1 - a) / (1 - u)) ^ 2 := by
  have hu1 : 0 < 1 - u := by linarith
  have hA : -1 ≤ (1 - c) / (1 - u) - 1 := by
    have : 0 ≤ (1 - c) / (1 - u) := div_nonneg (by linarith) hu1.le
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hA hp0 hp1
  rw [add_sub_cancel] at hb
  refine le_trans hb ?_
  rw [div_pow, le_div_iff₀ (by positivity)]
  have e : (1 + p * ((1 - c) / (1 - u) - 1)) * (1 - u) ^ 2 = (1 - u) ^ 2 - p * (c - u) * (1 - u) := by
    field_simp; ring
  rw [e]
  have h1 : 1 - p * c ≤ (1 - a) ^ 2 := by nlinarith
  have h2 : (1 - u) ^ 2 - p * (c - u) * (1 - u) ≤ 1 - p * c := by
    have : p * c + (1 - p) * u ≤ 2 - p := by nlinarith
    nlinarith
  linarith

/-- **Lemma Z**. -/
theorem lemmaZ (b M : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hM : 1 ≤ M)
    (hMb : 2 * (M : ℝ) ^ 2 ≤ p * (b : ℝ) ^ 2) (t : ℝ) (ht0 : 0 < t) (htb : (b : ℝ) * t < 1) :
    (Real.sin (π * b * t) / (b * Real.sin (π * t))) ^ p ≤
      (Real.sin (π * M * t) / (M * Real.sin (π * t))) ^ 2 := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbM : (M : ℝ) ^ 2 < (b : ℝ) ^ 2 := by nlinarith
  have hb1 : (M : ℝ) < b := by
    have hb0 : (0 : ℝ) ≤ b := by positivity
    nlinarith
  have hb' : (1 : ℝ) < b := lt_of_le_of_lt hM' hb1
  have hMt : (M : ℝ) * t < 1 := lt_trans (mul_lt_mul_of_pos_right hb1 ht0) htb
  have ht1 : t < 1 := by nlinarith
  -- positivity of the sinc values
  have hS : ∀ x : ℝ, 0 < x → x < 1 → 0 < Real.sin (π * x) / (π * x) := by
    intro x hx0 hx1
    apply div_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])) (by positivity)
  have St := hS t ht0 ht1
  have Sb := hS (b * t) (by positivity) htb
  have SM := hS (M * t) (by positivity) hMt
  -- the ratios
  have eb : Real.sin (π * b * t) / (b * Real.sin (π * t)) =
      (Real.sin (π * (b * t)) / (π * (b * t))) / (Real.sin (π * t) / (π * t)) := by
    rw [mul_assoc π]; field_simp
  have eM : Real.sin (π * M * t) / (M * Real.sin (π * t)) =
      (Real.sin (π * (M * t)) / (π * (M * t))) / (Real.sin (π * t) / (π * t)) := by
    rw [mul_assoc π]; field_simp
  rw [eb, eM]
  -- partial products
  have hfac : ∀ n : ℕ, (eulP n (b * t) / eulP n t) ^ p ≤ (eulP n (M * t) / eulP n t) ^ 2 := by
    intro n
    have hpos : ∀ j : ℕ, ∀ x : ℝ, 0 ≤ x → x < 1 → 0 < 1 - x ^ 2 / ((j : ℝ) + 1) ^ 2 := by
      intro j x hx0 hx1
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      rw [sub_pos, div_lt_one (by positivity)]
      nlinarith
    unfold eulP
    rw [← Finset.prod_div_distrib, ← Finset.prod_div_distrib, ← Finset.prod_pow,
      ← Real.finsetProd_rpow _ _ (fun j _ => (div_pos (hpos j _ (by positivity) htb) (hpos j _ ht0.le ht1)).le)]
    apply Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (div_pos (hpos j _ (by positivity) htb) (hpos j _ ht0.le ht1)).le p)
    intro j _
    have hj : (0 : ℝ) < ((j : ℝ) + 1) ^ 2 := by positivity
    set u := t ^ 2 / ((j : ℝ) + 1) ^ 2 with hu
    have hu0 : 0 < u := by positivity
    have e1 : (b * t) ^ 2 / ((j : ℝ) + 1) ^ 2 = (b : ℝ) ^ 2 * u := by rw [hu]; ring
    have e2 : (M * t) ^ 2 / ((j : ℝ) + 1) ^ 2 = (M : ℝ) ^ 2 * u := by rw [hu]; ring
    rw [e1, e2]
    have hc1 : (b : ℝ) ^ 2 * u < 1 := by
      have := hpos j (b * t) (by positivity) htb; rw [e1] at this; linarith
    apply factor_ineq p _ _ u hp0.le hp1 hu0
      (by nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (b : ℝ) ^ 2 by nlinarith) hu0.le]) hc1 (by positivity)
    nlinarith
  have hl1 : Tendsto (fun n => (eulP n (b * t) / eulP n t) ^ p) atTop
      (𝓝 (((Real.sin (π * (b * t)) / (π * (b * t))) / (Real.sin (π * t) / (π * t))) ^ p)) := by
    apply Tendsto.rpow_const _ (Or.inr hp0.le)
    exact (tendsto_eulP _ (by positivity)).div (tendsto_eulP _ ht0.ne') St.ne'
  have hl2 : Tendsto (fun n => (eulP n (M * t) / eulP n t) ^ 2) atTop
      (𝓝 (((Real.sin (π * (M * t)) / (π * (M * t))) / (Real.sin (π * t) / (π * t))) ^ 2)) := by
    apply Tendsto.pow
    exact (tendsto_eulP _ (by positivity)).div (tendsto_eulP _ ht0.ne') St.ne'
  exact le_of_tendsto_of_tendsto' hl1 hl2 hfac

end Palprimes
