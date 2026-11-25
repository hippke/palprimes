import Omega3.Statements
import Omega3.Items.S07_Base

/-!
# S07: Lemma 4 (i) above `x_n` and Lemma 4 (ii′) for odd `ν ≥ 3` (plan in `S07_PLAN.md`)
-/

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-- The real inequality of the case `ν(δ) = 1`. -/
lemma S07_nu1 (x t xn : ℝ) (hB : kSq * (1 - xn) ^ 2 ≤ 4 * (UU - xn)) (hx1 : xn ≤ x) (hxU : x < UU)
    (hx3 : 1 / 3 ≤ x) (ht0 : 0 < t) (h2t : 2 * t + x < 1) :
    Wf t ≤ (UU - x) * (2 * t / (1 - x)) ^ 2 := by
  have hU : UU = 1 - 2 * mm := by unfold UU mm; norm_num
  have hm : (0 : ℝ) < mm := by unfold mm; norm_num
  set s := 1 - x with hs
  have hs2 : 2 * mm < s := by rw [hU] at hxU; linarith
  have hspos : 0 < s := by linarith
  have hUx : UU - x = s - 2 * mm := by rw [hU]; ring
  rw [hUx]
  have hR : (s - 2 * mm) * (2 * t / s) ^ 2 = (s - 2 * mm) * (4 * t ^ 2) / s ^ 2 := by
    rw [div_pow]; ring
  rw [hR, le_div_iff₀ (by positivity)]
  by_cases htm : t ≤ mm
  · rw [S07_W_zero t htm]
    have : 0 ≤ (s - 2 * mm) * (4 * t ^ 2) := mul_nonneg (by linarith) (by positivity)
    linarith
  · push Not at htm
    by_cases h4 : 4 * mm ≤ s
    · have hW := S07_W_sq t ht0.le (by linarith)
      -- k² s² ≤ 4 (s − 2m) from BandOK and monotonicity of (s − 2m)/s² on [4m, ∞)
      set sn := 1 - xn with hsn
      have hssn : s ≤ sn := by linarith
      have hBn : kSq * sn ^ 2 ≤ 4 * (sn - 2 * mm) := by
        have : UU - xn = sn - 2 * mm := by rw [hU]; ring
        rw [← this]; exact hB
      have hmono : (sn - 2 * mm) * s ^ 2 ≤ (s - 2 * mm) * sn ^ 2 := by
        have e : (s - 2 * mm) * sn ^ 2 - (sn - 2 * mm) * s ^ 2 = (sn - s) * (s * sn - 2 * mm * (s + sn)) := by ring
        have h1 : 0 ≤ sn - s := by linarith
        have h2 : 0 ≤ s * sn - 2 * mm * (s + sn) := by nlinarith
        nlinarith [mul_nonneg h1 h2]
      have hsn0 : 0 < sn := by linarith
      have hk : kSq * s ^ 2 ≤ 4 * (s - 2 * mm) := by
        have h1 : kSq * s ^ 2 * sn ^ 2 ≤ 4 * (s - 2 * mm) * sn ^ 2 := by
          have := mul_le_mul_of_nonneg_left hBn (sq_nonneg s)
          nlinarith
        exact le_of_mul_le_mul_right h1 (by positivity)
      have := mul_le_mul_of_nonneg_left hk (sq_nonneg t)
      calc Wf t * s ^ 2 ≤ kSq * t ^ 2 * s ^ 2 := by gcongr
        _ ≤ (s - 2 * mm) * (4 * t ^ 2) := by nlinarith
    · push Not at h4
      have hW := S07_W_lin t htm
      have hA : 0 ≤ s - 2 * t := by linarith
      have hB' : 0 ≤ 4 * t - s := by linarith
      have hC : 0 ≤ t - mm := by linarith
      have h1 := mul_nonneg (mul_nonneg hC hA) hB'
      have h2 := mul_nonneg hB' (mul_nonneg (sq_nonneg t) hC)
      have h3 := mul_nonneg hA (mul_nonneg hm.le (sq_nonneg t))
      have hQ : 2 * t * ((t - mm) * s ^ 2 - 4 * t ^ 2 * s + 8 * mm * t ^ 2) ≤ 0 := by
        have e : 2 * t * ((t - mm) * s ^ 2 - 4 * t ^ 2 * s + 8 * mm * t ^ 2) =
            -(2 * t) * ((t - mm) * (s - 2 * t) * (4 * t - s)) - 4 * ((4 * t - s) * (t ^ 2 * (t - mm))) -
              8 * ((s - 2 * t) * (mm * t ^ 2)) := by ring
        rw [e]
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) h1
        linarith
      have hQ' : (t - mm) * s ^ 2 ≤ (s - 2 * mm) * (4 * t ^ 2) := by
        have : (t - mm) * s ^ 2 - 4 * t ^ 2 * s + 8 * mm * t ^ 2 ≤ 0 := by
          by_contra hc
          push Not at hc
          have := mul_pos (by linarith : (0 : ℝ) < 2 * t) hc
          linarith
        nlinarith
      calc Wf t * s ^ 2 ≤ (t - mm) * s ^ 2 := by gcongr
        _ ≤ (s - 2 * mm) * (4 * t ^ 2) := hQ'

theorem itemS07 : ItemS07 := by
  classical
  intro B hB y δ q hy hδ hnb hq hqδ
  obtain ⟨hdvd, h1, hcb, hodd, hω⟩ := S07_mem y δ hδ
  have hPne : primorialLt (y ^ UU) ≠ 0 := by
    unfold primorialLt
    exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hPne (zero_dvd_iff.1 hdvd)
  obtain ⟨hsq, hpz⟩ := S07_primorial (y ^ UU) δ hdvd hδ0
  obtain ⟨hc1, hc0⟩ := S07_chi y mm δ h1 hcb
  have hyle := S07_y_le y δ hsq h1 hc1 hc0
  have hy0 : 0 < y := by linarith
  set L := Real.log y with hL
  have hL0 : 0 < L := Real.log_pos hy
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlq : 0 < Real.log q := Real.log_pos hq1
  set t := Real.log q / L with ht
  set x := Real.log δ / L with hx
  have ht0 : 0 < t := div_pos hlq hL0
  have h2t : 2 * t + x < 1 := by
    have h := Real.log_lt_log (by positivity) hqδ
    rw [Real.log_mul (by positivity) hδpos.ne', Real.log_pow] at h
    have e : 2 * (Real.log q / L) + Real.log δ / L = (2 * Real.log q + Real.log δ) / L := by ring
    rw [ht, hx, e, div_lt_one hL0]
    push_cast at h; linarith
  have hR : 2 * Real.log q / Real.log (y / δ) = 2 * t / (1 - x) := by
    rw [Real.log_div hy0.ne' hδpos.ne', ← hL, ht, hx]
    have : L - Real.log δ ≠ 0 := by
      have : Real.log δ / L < 1 := by linarith
      rw [div_lt_one hL0] at this; linarith
    field_simp
  rw [hR]
  have hwq : wy y q = Wf t := rfl
  rw [hwq]
  have hp0 : δ.minFac.Prime := Nat.minFac_prime h1
  have hp0mem : δ.minFac ∈ δ.primeFactors := Nat.mem_primeFactors.2 ⟨hp0, Nat.minFac_dvd δ, hδ0⟩
  set l : ℕ → ℝ := fun p => Real.log p / L with hl
  have hlpos : ∀ p ∈ δ.primeFactors, 0 < l p := by
    intro p hp
    have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_pos (Real.log_pos this) hL0
  have hxsum : x = ∑ p ∈ δ.primeFactors, l p := by
    have hprod : ((∏ p ∈ δ.primeFactors, p : ℕ) : ℝ) = (δ : ℝ) := by
      rw [Nat.prod_primeFactors_of_squarefree hsq]
    rw [hx, ← hprod, Nat.cast_prod, Real.log_prod (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity), Finset.sum_div]
  -- y ≤ δ p(δ)² in logarithms
  have hC1 : 1 ≤ x + 2 * l δ.minFac := by
    have h := Real.log_le_log hy0 hyle
    rw [Real.log_mul hδpos.ne' (by have := hp0.pos; positivity), Real.log_pow] at h
    have e : Real.log δ / L + 2 * (Real.log δ.minFac / L) = (Real.log δ + 2 * Real.log δ.minFac) / L := by ring
    rw [hx, hl]
    simp only
    rw [e, le_div_iff₀ hL0]
    push_cast at h; linarith
  have hω' : ω δ = δ.primeFactors.card := ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors
  have hphi : phiW W1 (wy y) δ = W1 - ∑ p ∈ δ.primeFactors, Wf (l p) := rfl
  by_cases hc : δ.primeFactors.card = 1
  · -- ν(δ) = 1: δ = p prime
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
    have hpδ : δ = p := by
      have := Nat.prod_primeFactors_of_squarefree hsq
      rw [hp] at this; simpa using this.symm
    have hpmem : p ∈ δ.primeFactors := by rw [hp]; simp
    have hpp : δ.Prime := by rw [hpδ]; exact Nat.prime_of_mem_primeFactors hpmem
    have hxl : x = l δ := by rw [hxsum, hp, Finset.sum_singleton, hpδ]
    have hmf : δ.minFac = δ := Nat.Prime.minFac_eq hpp
    have hphi1 : phiW W1 (wy y) δ = W1 - Wf x := by
      rw [hphi, hp, Finset.sum_singleton, hxl, hpδ]
    have hx3 : 1 / 3 ≤ x := by
      rw [hmf, ← hxl] at hC1; linarith
    have hxU : x < UU := by
      have h := hpz δ (by rw [hpδ] at hpmem ⊢; exact hpmem)
      have h' := Real.log_lt_log hδpos h
      rw [Real.log_rpow hy0] at h'
      rw [hx, div_lt_iff₀ hL0]; linarith
    -- not in a band: x ≥ x_n
    obtain ⟨hlen, -, hhead, -, -, -, -, hBk⟩ := hB
    have hxn : (B.xn : ℝ) ≤ x := by
      by_contra hlt
      push Not at hlt
      have hne : B.xs ≠ [] := by intro h; rw [h] at hhead; simp at hhead
      have hh0 : B.xs.headD 0 = 1 / 3 := by
        cases hxs : B.xs with
        | nil => exact absurd hxs hne
        | cons a r => rw [hxs] at hhead; simp at hhead; simp [hhead]
      obtain ⟨i, hi, hlo, hhi⟩ := S07_find B.xs x hne (by rw [hh0]; push_cast; exact hx3) hlt
      apply hnb
      refine ⟨i, hpp, by omega, ?_, ?_⟩
      · have hδeq : (δ : ℝ) = y ^ x := by
          have e : L * (Real.log δ / L) = Real.log δ := by field_simp
          rw [hx, Real.rpow_def_of_pos hy0, ← hL, e, Real.exp_log hδpos]
        rw [hδeq]
        exact Real.rpow_le_rpow_of_exponent_le hy.le hlo
      · have hδeq : (δ : ℝ) = y ^ x := by
          have e : L * (Real.log δ / L) = Real.log δ := by field_simp
          rw [hx, Real.rpow_def_of_pos hy0, ← hL, e, Real.exp_log hδpos]
        rw [hδeq]
        exact Real.rpow_lt_rpow_of_exponent_lt hy hhi
    rw [hphi1, S07_W_eq x hx3 hxU.le]
    have : W1 - (x - mm) = UU - x := by unfold W1 mm UU; ring
    rw [this]
    exact S07_nu1 x t B.xn hBk hxn hxU hx3 ht0 h2t
  · -- ν(δ) ≥ 3
    have hc3 : 3 ≤ δ.primeFactors.card := by
      rw [hω'] at hodd
      obtain ⟨k, hk⟩ := hodd
      have : δ.primeFactors.card ≠ 0 := by
        intro h0; rw [h0] at hk; omega
      omega
    -- all l_p ≤ 1/3
    obtain ⟨p', hp'mem, hp'ne⟩ : ∃ p' ∈ δ.primeFactors, p' ≠ δ.minFac := by
      by_contra hcon
      push Not at hcon
      have : δ.primeFactors ⊆ {δ.minFac} := fun p hp => by rw [Finset.mem_singleton]; exact hcon p hp
      have := Finset.card_le_card this
      simp at this; omega
    have hmin_le : ∀ p ∈ δ.primeFactors, δ.minFac ≤ p := fun p hp =>
      Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp)
    have hcube : ∀ p ∈ δ.primeFactors, (p : ℝ) ^ 3 ≤ y := by
      intro p hp
      by_cases hpe : p = δ.minFac
      · have h1' := S07_cube y δ hδ0 h1 hc1 p' hp'mem hp'ne
        have : (p : ℝ) ≤ p' := by rw [hpe]; exact_mod_cast hmin_le p' hp'mem
        have h0 : (0 : ℝ) ≤ p := by positivity
        have : (p : ℝ) ^ 3 ≤ (p' : ℝ) ^ 3 := by gcongr
        linarith
      · exact (S07_cube y δ hδ0 h1 hc1 p hp hpe).le
    have hl3 : ∀ p ∈ δ.primeFactors, l p ≤ 1 / 3 := by
      intro p hp
      have hp1 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have h := Real.log_le_log (by positivity) (hcube p hp)
      rw [Real.log_pow] at h
      rw [hl]; simp only
      rw [div_le_iff₀ hL0]; push_cast at h; linarith
    have hx1 : x < 1 := by linarith
    have hW1 : W1 = 1 - 3 * mm := by unfold W1 mm; norm_num
    by_cases htm : t ≤ mm
    · rw [S07_W_zero t htm]
      apply mul_nonneg _ (sq_nonneg _)
      rw [hphi]
      have h := Finset.sum_le_sum (fun p hp => S07_W_prop (l p) (hlpos p hp).le (hl3 p hp))
      rw [← Finset.mul_sum, ← hxsum] at h
      have hm : (0 : ℝ) ≤ 1 - 3 * mm := by unfold mm; norm_num
      have : (1 - 3 * mm) * x ≤ 1 - 3 * mm := by nlinarith
      linarith
    · push Not at htm
      have hl0 : t < l δ.minFac := by linarith
      have hlarge : ∀ p ∈ δ.primeFactors, mm < l p := by
        intro p hp
        have : l δ.minFac ≤ l p := by
          rw [hl]; simp only
          apply div_le_div_of_nonneg_right _ hL0.le
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast hmin_le p hp
        linarith
      have hsumW : ∑ p ∈ δ.primeFactors, Wf (l p) ≤ x - 3 * mm := by
        have h := Finset.sum_le_sum (fun p hp => S07_W_lin (l p) (hlarge p hp))
        rw [Finset.sum_sub_distrib, Finset.sum_const, ← hxsum, nsmul_eq_mul] at h
        have : (3 : ℝ) ≤ δ.primeFactors.card := by exact_mod_cast hc3
        have hm : (0 : ℝ) < mm := by unfold mm; norm_num
        nlinarith
      have hφ : 1 - x ≤ phiW W1 (wy y) δ := by rw [hphi, hW1]; linarith
      have hνl : 3 * l δ.minFac ≤ x := by
        have h := Finset.card_nsmul_le_sum δ.primeFactors l (l δ.minFac) (fun p hp => by
          rw [hl]; simp only
          apply div_le_div_of_nonneg_right _ hL0.le
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast hmin_le p hp)
        rw [← hxsum, nsmul_eq_mul] at h
        have : (3 : ℝ) ≤ δ.primeFactors.card := by exact_mod_cast hc3
        have hl0' : 0 ≤ l δ.minFac := (hlpos _ hp0mem).le
        nlinarith
      have hx35 : 1 - x ≤ 2 / 5 := by linarith
      have h1x : 0 < 1 - x := by linarith
      have hW := S07_W_sq t ht0.le (by linarith)
      have hk : kSq ≤ 10 := by unfold kSq; norm_num
      have e : phiW W1 (wy y) δ * (2 * t / (1 - x)) ^ 2 = phiW W1 (wy y) δ * (4 * t ^ 2) / (1 - x) ^ 2 := by
        rw [div_pow]; ring
      rw [e, le_div_iff₀ (by positivity)]
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      calc Wf t * (1 - x) ^ 2 ≤ kSq * t ^ 2 * (1 - x) ^ 2 := by gcongr
        _ ≤ 10 * t ^ 2 * (1 - x) ^ 2 := by gcongr
        _ ≤ 4 * t ^ 2 * (1 - x) := by
            have : 10 * (1 - x) ^ 2 ≤ 4 * (1 - x) := by nlinarith
            nlinarith
        _ ≤ phiW W1 (wy y) δ * (4 * t ^ 2) := by nlinarith

end Omega3
