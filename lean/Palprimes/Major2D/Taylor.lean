import Mathlib

/-! # Taylor bound for `e^{ix}` on the whole real line

`‖e^{ix} − Σ_{k<n} (ix)^k/k!‖ ≤ |x|^n/n!` for every real `x` (`exp_I_taylor`), and its real and imaginary
parts for `n = 4`: `(cos x − 1 + x²/2)² + (sin x − x + x³/6)² ≤ (x⁴/24)²` (`cos_sin_taylor4`). -/

set_option linter.style.longLine false

open Complex Finset

namespace Palprimes

/-- `g_n(z) = e^{iz} − Σ_{k<n} (iz)^k/k!`. -/
noncomputable def expRem (n : ℕ) (z : ℂ) : ℂ := cexp (I * z) - ∑ k ∈ range n, (I * z) ^ k / (k.factorial : ℂ)

theorem hasDerivAt_expPart (n : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => ∑ k ∈ range (n + 1), (I * z) ^ k / (k.factorial : ℂ))
      (I * ∑ k ∈ range n, (I * z) ^ k / (k.factorial : ℂ)) z := by
  induction n with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      range_zero, sum_empty, mul_zero]
    exact hasDerivAt_const z 1
  | succ n ih =>
    have h1 : HasDerivAt (fun z : ℂ => (I * z) ^ (n + 1) / ((n + 1).factorial : ℂ))
        (I * ((I * z) ^ n / (n.factorial : ℂ))) z := by
      have hl : HasDerivAt (fun z : ℂ => I * z) I z := by
        simpa using (hasDerivAt_id z).const_mul I
      have hp := (hl.pow (n + 1)).div_const ((n + 1).factorial : ℂ)
      convert hp using 1
      have hf : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [hf]
      field_simp
      push_cast
      ring
    have := ih.add h1
    convert this using 1
    · funext w; simp only [Pi.add_apply]; rw [sum_range_succ]
    · rw [sum_range_succ, mul_add]

theorem hasDerivAt_expRem (n : ℕ) (z : ℂ) : HasDerivAt (expRem (n + 1)) (I * expRem n z) z := by
  have he : HasDerivAt (fun z : ℂ => cexp (I * z)) (cexp (I * z) * I) z := by
    have hl : HasDerivAt (fun z : ℂ => I * z) I z := by
      simpa using (hasDerivAt_id z).const_mul I
    exact (Complex.hasDerivAt_exp (I * z)).comp z hl
  have := he.sub (hasDerivAt_expPart n z)
  unfold expRem
  convert this using 1
  ring

theorem expRem_zero_succ (n : ℕ) : expRem (n + 1) 0 = 0 := by
  unfold expRem
  rw [sum_range_succ']
  simp

theorem expRem_conj (n : ℕ) (x : ℝ) : expRem n (-x : ℝ) = starRingEnd ℂ (expRem n x) := by
  unfold expRem
  rw [map_sub, map_sum, ← Complex.exp_conj]
  congr 1
  · congr 1; simp [Complex.conj_ofReal]
  · apply sum_congr rfl; intro k _
    rw [map_div₀, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast]
    push_cast; ring

theorem expRem_bound_nonneg (n : ℕ) : ∀ x : ℝ, 0 ≤ x → ‖expRem n x‖ ≤ x ^ n / n.factorial := by
  induction n with
  | zero =>
    intro x _
    unfold expRem
    simp only [range_zero, sum_empty, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [show (I * (x : ℂ)) = (x : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I]
  | succ n ih =>
    intro x hx
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => expRem (n + 1) t) (I * expRem n t) t :=
      fun t => (hasDerivAt_expRem n t).comp_ofReal
    have hf : ContinuousOn (fun t : ℝ => expRem (n + 1) t) (Set.Icc 0 x) :=
      fun t _ => (hd t).continuousAt.continuousWithinAt
    have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ (n + 1) / ((n + 1).factorial : ℝ)) (t ^ n / n.factorial) t := by
      intro t
      have := ((hasDerivAt_id t).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      convert this using 1
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      · funext w; simp
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      simp only [id_eq, mul_one]
      push_cast
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t : ℝ => expRem (n + 1) t)
      (a := 0) (b := x) hf (fun t _ => (hd t).hasDerivWithinAt)
      (B := fun t : ℝ => t ^ (n + 1) / ((n + 1).factorial : ℝ)) (by simp [expRem_zero_succ]) hB
      (fun t ht => by
        rw [norm_mul, Complex.norm_I, one_mul]
        exact ih t ht.1)
    exact key ⟨hx, le_rfl⟩

theorem exp_I_taylor (n : ℕ) (x : ℝ) : ‖expRem n x‖ ≤ |x| ^ n / n.factorial := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact expRem_bound_nonneg n x hx
  · have h := expRem_bound_nonneg n (-x) (by linarith)
    rw [abs_of_nonpos hx]
    rw [expRem_conj, Complex.norm_conj] at h
    exact h

/-- The real form for `n = 4`. -/
theorem cos_sin_taylor4 (x : ℝ) :
    (Real.cos x - (1 - x ^ 2 / 2)) ^ 2 + (Real.sin x - (x - x ^ 3 / 6)) ^ 2 ≤ (x ^ 4 / 24) ^ 2 := by
  have h := exp_I_taylor 4 x
  have he : expRem 4 x = ((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - (x - x ^ 3 / 6) : ℝ) : ℂ) * I := by
    unfold expRem
    simp only [sum_range_succ, range_zero, sum_empty, Nat.factorial]
    rw [show I * (x : ℂ) = (x : ℂ) * I by ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [he] at h
  have hn : ‖((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - (x - x ^ 3 / 6) : ℝ) : ℂ) * I‖ ^ 2 =
      (Real.cos x - (1 - x ^ 2 / 2)) ^ 2 + (Real.sin x - (x - x ^ 3 / 6)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [← hn]
  have h0 : 0 ≤ ‖((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - (x - x ^ 3 / 6) : ℝ) : ℂ) * I‖ := norm_nonneg _
  have h4 : |x| ^ 4 / (Nat.factorial 4 : ℝ) = x ^ 4 / 24 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs]; norm_num [Nat.factorial]; ring
  rw [h4] at h
  exact pow_le_pow_left₀ h0 h 2

end Palprimes
