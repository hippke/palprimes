import Omega3.Items.M02_L

/-! # M02 helpers (copied from S08, renamed), part E: error estimates (Steps 2, 3 and the prime-mass bound). -/

namespace Omega3

open Finset Palprimes

set_option linter.style.longLine false

lemma m02_gS_prime (b q : ℕ) (hq : q.Prime) (hqB : Nat.Coprime q (bigB b)) : gS b q = 1 / ((q : ℝ) - 1) := by
  unfold gS
  rw [if_pos ⟨hq.squarefree, hqB⟩, Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le]
  simp

lemma m02_gS_le (b q : ℕ) (hq : q.Prime) (Y : ℝ) (hY : 1 < Y) (hqY : Y ≤ q) : gS b q ≤ 1 / (Y - 1) := by
  unfold gS
  split_ifs with h
  · rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le]
    simp only [Nat.cast_one]
    apply one_div_le_one_div_of_le (by linarith); linarith
  · apply div_nonneg zero_le_one; linarith

lemma m02_q_gS (b q : ℕ) (hq : q.Prime) (hqB : Nat.Coprime q (bigB b)) : (q : ℝ) * gS b q = 1 + gS b q := by
  rw [m02_gS_prime b q hq hqB]
  have : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have h : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp; ring

/-- `|q A_q − G(z/q)| ≤ 3T G(z)`. -/
lemma m02_err_q (b : ℕ) (z : ℝ) (hz : 0 < z) (q : ℕ) (hq : q.Prime) (hqB : Nat.Coprime q (bigB b)) (T : ℝ)
    (hT : gS b q ≤ T) (hT1 : T ≤ 1) :
    |(q : ℝ) * m02A b z q - GS b (z / q)| ≤ 3 * T * GS b z := by
  have h := m02_A_approx b z hz q hq.squarefree hqB
  rw [Nat.Prime.primeFactors hq, Finset.sum_singleton, m02_q_gS b q hq hqB] at h
  have hg0 := m02_gS_nonneg b q
  have hG := m02_GS_nonneg b z
  refine le_trans h ?_
  apply mul_le_mul_of_nonneg_right _ hG
  nlinarith

/-- `|pq A_{pq} − G(z/(pq))| ≤ 11T G(z)`. -/
lemma m02_err_pq (b : ℕ) (z : ℝ) (hz : 0 < z) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpB : Nat.Coprime p (bigB b)) (hqB : Nat.Coprime q (bigB b)) (T : ℝ)
    (hTp : gS b p ≤ T) (hTq : gS b q ≤ T) (hT1 : T ≤ 1) :
    |((p * q : ℕ) : ℝ) * m02A b z (p * q) - GS b (z / ((p * q : ℕ) : ℝ))| ≤ 11 * T * GS b z := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hsq : Squarefree (p * q) := Nat.squarefree_mul_iff.2 ⟨hcop, hp.squarefree, hq.squarefree⟩
  have hpqB : Nat.Coprime (p * q) (bigB b) := Nat.coprime_mul_iff_left.2 ⟨hpB, hqB⟩
  have h := m02_A_approx b z hz (p * q) hsq hpqB
  have hpf : (p * q).primeFactors = {p, q} := by
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq]; rfl
  have hgm : gS b (p * q) = gS b p * gS b q := by
    rw [m02_gS_mul b p q hp.squarefree hpB, if_pos hcop.symm]
  have hc : ((p * q : ℕ) : ℝ) * gS b (p * q) = (1 + gS b p) * (1 + gS b q) := by
    rw [hgm, ← m02_q_gS b p hp hpB, ← m02_q_gS b q hq hqB]; push_cast; ring
  rw [hpf, Finset.sum_pair hpq, hc] at h
  have hg0 := m02_gS_nonneg b p
  have hg1 := m02_gS_nonneg b q
  have hG := m02_GS_nonneg b z
  refine le_trans h ?_
  apply mul_le_mul_of_nonneg_right _ hG
  have h1 : (1 + gS b p) * (1 + gS b q) ≤ 4 := by nlinarith
  have h2 : (1 + gS b p) * (1 + gS b q) * (gS b p + gS b q) ≤ 4 * (2 * T) := by
    apply mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  nlinarith

/-- Ratio: `|d A_d/G − max(1 − log d/L, 0)| ≤ err + 2C/G`. -/
lemma m02_ratio (b : ℕ) (C : ℝ) (hC : ∀ w : ℝ, 1 ≤ w → |GS b w - m02beta b * Real.log w| ≤ C)
    (z : ℝ) (hz : 1 < z) (hG : 1 ≤ GS b z) (d : ℕ) (hd : 1 ≤ d) (err : ℝ)
    (hA : |(d : ℝ) * m02A b z d - GS b (z / d)| ≤ err * GS b z) :
    |(d : ℝ) * m02A b z d / GS b z - max (1 - Real.log d / Real.log z) 0| ≤ err + 2 * C / GS b z := by
  set G := GS b z with hGdef
  have hG0 : 0 < G := by linarith
  have hL : 0 < Real.log z := Real.log_pos hz
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 1 le_rfl)
  have hzC := hC z hz.le
  have key : |GS b (z / d) - G * max (1 - Real.log d / Real.log z) 0| ≤ 2 * C := by
    rcases le_or_gt (d : ℝ) z with hdz | hdz
    · have hw : 1 ≤ z / d := by rw [le_div_iff₀ hd0]; linarith
      have hlw : Real.log (z / d) = Real.log z - Real.log d := Real.log_div (by linarith) hd0.ne'
      have hld : Real.log d ≤ Real.log z := Real.log_le_log hd0 hdz
      have ht : 0 ≤ 1 - Real.log d / Real.log z := by
        rw [sub_nonneg, div_le_one hL]; exact hld
      rw [max_eq_left ht]
      have hwC := hC (z / d) hw
      have hld0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
      have ht1 : 1 - Real.log d / Real.log z ≤ 1 := by
        have : 0 ≤ Real.log d / Real.log z := div_nonneg hld0 hL.le
        linarith
      have e : GS b (z / d) - G * (1 - Real.log d / Real.log z) =
          (GS b (z / d) - m02beta b * Real.log (z / d)) -
            (1 - Real.log d / Real.log z) * (G - m02beta b * Real.log z) := by
        rw [hlw]; field_simp; ring
      rw [e]
      calc _ ≤ |GS b (z / d) - m02beta b * Real.log (z / d)| +
            |(1 - Real.log d / Real.log z) * (G - m02beta b * Real.log z)| := abs_sub _ _
        _ ≤ C + 1 * C := by
            rw [abs_mul, abs_of_nonneg ht]
            exact add_le_add hwC (mul_le_mul ht1 hzC (abs_nonneg _) zero_le_one)
        _ = 2 * C := by ring
    · have hw : z / d ≤ 1 := by rw [div_le_one hd0]; exact hdz.le
      rw [m02_GS_le_one b hw]
      have hld : Real.log z < Real.log d := Real.log_lt_log (by linarith) hdz
      have : 1 - Real.log d / Real.log z ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ hL]; linarith
      rw [max_eq_right this]; simp; linarith
  have e : (d : ℝ) * m02A b z d / G - max (1 - Real.log d / Real.log z) 0 =
      ((d : ℝ) * m02A b z d - GS b (z / d)) / G + (GS b (z / d) - G * max (1 - Real.log d / Real.log z) 0) / G := by
    field_simp; ring
  rw [e]
  calc _ ≤ |((d : ℝ) * m02A b z d - GS b (z / d)) / G| + |(GS b (z / d) - G * max (1 - Real.log d / Real.log z) 0) / G| :=
        abs_add_le _ _
    _ ≤ err + 2 * C / G := by
        rw [abs_div, abs_div, abs_of_pos hG0]
        apply add_le_add
        · rw [div_le_iff₀ hG0]; exact hA
        · exact div_le_div_of_nonneg_right key hG0.le

/-- Prime mass: `Σ_{p < z} |η̂(u_p)|/p ≤ M(log(1/u₀) + 1)` for `log z` large. -/
lemma m02_mass (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) : ∃ K : ℝ, ∀ z : ℝ, 1 < z → K ≤ Real.log z →
    ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)| ≤ m02Mv e * (Real.log (1 / m02u0 e) + 1) := by
  classical
  obtain ⟨C2, hC2, hM2⟩ := m02_mertens2
  set u0 := m02u0 e with hu0
  have hu0p : 0 < u0 := m02_u0_pos e he
  have hu01 : u0 ≤ 1 := by
    unfold m02u0 at hu0
    have : ∀ l : List (ℚ × ℚ), (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 ≤ 1 := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.foldr_cons]; exact le_trans (min_le_right _ _) ih
    rw [hu0]; exact this e
  refine ⟨max (Real.log 4 / u0) (C2 / u0), fun z hz hK => ?_⟩
  have hL : 0 < Real.log z := Real.log_pos hz
  have hz0 : 0 < z := by linarith
  have h4 : Real.log 4 ≤ u0 * Real.log z := by
    have := le_trans (le_max_left _ _) hK; rw [div_le_iff₀ hu0p] at this; linarith
  have hC2L : C2 ≤ u0 * Real.log z := by
    have := le_trans (le_max_right _ _) hK; rw [div_le_iff₀ hu0p] at this; linarith
  set S := (m02Pz z).filter (fun p => u0 ≤ m02u z p ∧ m02u z p < 1) with hS
  have hmem := m02_mem_set z hz u0 1 le_rfl
  have hA4 : 4 ≤ z ^ u0 := by
    rw [Real.rpow_def_of_pos hz0, ← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.2 (by linarith)
  have hAT : z ^ u0 ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le hu01
  have m2 := hM2 S (z ^ u0) (z ^ (1 : ℝ)) hA4 hAT (fun p hp => (hmem p).1 hp) (fun p h1 h2 h3 => (hmem p).2 ⟨h1, h2, h3⟩)
  rw [Real.log_rpow hz0, Real.log_rpow hz0, one_mul, Real.log_mul hu0p.ne' hL.ne'] at m2
  rw [abs_le] at m2
  have hSb : ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (1 / u0) + 1 := by
    have : C2 / (u0 * Real.log z) ≤ 1 := by rw [div_le_one (by positivity)]; exact hC2L
    rw [Real.log_div one_ne_zero hu0p.ne', Real.log_one]
    linarith
  calc ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)| ≤ ∑ p ∈ S, (1 / (p : ℝ)) * m02Mv e := by
        rw [hS, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with h
        · exact mul_le_mul_of_nonneg_left (m02_eval_abs e _) (by positivity)
        · have hlt : m02u z p < u0 := by
            by_contra hc; push_neg at hc; exact h ⟨hc, m02_u_lt_one z hz p hp⟩
          rw [m02_eval_zero e _ hlt]; simp
    _ = m02Mv e * ∑ p ∈ S, (1 : ℝ) / p := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ m02Mv e * (Real.log (1 / u0) + 1) := mul_le_mul_of_nonneg_left hSb (m02_Mv_nonneg e)

end Omega3
