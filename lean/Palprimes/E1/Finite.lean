import Palprimes.E1.Boundary
import Palprimes.E1.PrimeSum1
import Palprimes.E1.Cont

/-! # E1, Part B.3: finite-depth asymptotics (blueprint §3.3)

For `D` the level, `w` the sifting limit and `s = log D / log w`:

**Lemma B.3.** For every depth `k` and every `ε > 0` there is `D₁` such that for all `D ≥ D₁`:
* `|B⁺_k(D, w) − V(w) β⁺_k(s)| ≤ ε V(w)` for all `2 ≤ w ≤ D` (`finite_depth_plus`);
* `|B⁻_k(D, w) − V(w) β⁻_k(s)| ≤ ε V(w)` for all `2 ≤ w ≤ D^{1/2}` (`finite_depth_minus`, trivial for `k = 0`).

Proof by induction in the order `B⁺_0, B⁻_1, B⁺_1, B⁻_2, …`:
* `B⁺_0` (`finite_plus_zero`): `B⁺_0 = V(D^{1/3}) − V(w) − E` for `w > D^{1/3}` (`sum_cube_gt_eq`, `E` the one-prime
  correction at `p = D^{1/3}`, `E ≤ V(D^{1/3})/D^{1/3}`), then `VB_cube_ratio`; `B⁺_0 = 0 = β⁺_0` for `w ≤ D^{1/3}`.
* `B⁻_{k+1}` from `B⁺_k` (`finite_minus_succ`): A.4 `B⁻_{k+1}(D,w) = Σ_{p<w} g(p) B⁺_k(D/p, p)`, the induction hypothesis
  at the inner level `D/p ≥ D^{1/2}` (so the inner `D₁` is squared, blueprint §7 item 17), the error vanishes for
  `s_p ≥ 2k+3` and the rest has mass `≤ (2k+4) V(w)` (`mass_sp_lt_le`); main term by `primeSum1_all`.
* `B⁺_{k+1}` from `B⁻_{k+1}` (`finite_plus_succ`): A.4 with `p³ ≤ D`, inner level `D/p ≥ D^{2/3} ≥ D^{1/2}`,
  `p ≤ (D/p)^{1/2}`; main term by `primeSum1_cube`.
Outside the range `s ≤ S₁` of B.2 both sides vanish (A.5, B.1).

Exported for the assembly (E12, blueprint §6): `finite_depth_plus`, `finite_depth_minus`, and the summed forms
`finite_depth_sum_plus`, `finite_depth_sum_minus` (`|Σ_{k<K} B^±_k − V(w) Σ_{k<K} β^±_k(s)| ≤ ε V(w)`). -/

set_option linter.style.longLine false

open Finset Real MeasureTheory

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

/-! ## Small helpers -/

/-- `x ≤ y^{1/2} → x² ≤ y` (`x, y ≥ 0`). -/
theorem sq_le_of_le_rpow_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ (1 / 2 : ℝ)) : x ^ 2 ≤ y := by
  rw [← Real.sqrt_eq_rpow] at h
  calc x ^ 2 ≤ (√y) ^ 2 := pow_le_pow_left₀ hx h 2
    _ = y := Real.sq_sqrt hy

/-- `x² ≤ y → x ≤ y^{1/2}`. -/
theorem le_rpow_half_of_sq_le {x y : ℝ} (h : x ^ 2 ≤ y) : x ≤ y ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le h

/-- Inner level: if `p² ≤ D` and `E² ≤ D` then `E ≤ D/p` (`D/p ≥ D^{1/2}`). -/
theorem le_div_of_sq_le {D p E : ℝ} (hp : 0 < p) (hpD : p ^ 2 ≤ D) (hE : E ^ 2 ≤ D) : E ≤ D / p := by
  rw [le_div_iff₀ hp]
  by_contra h
  push Not at h
  have hD0 : 0 ≤ D := le_trans (sq_nonneg p) hpD
  have h1 : E ^ 2 * p ^ 2 ≤ D * D := mul_le_mul hE hpD (sq_nonneg p) hD0
  have h2 : 0 < (E * p - D) * (E * p + D) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- `|Σ f − Σ h| ≤ Σ c` from pointwise `|f − h| ≤ c`. -/
theorem abs_sum_sub_le {S : Finset ℕ} (f h c : ℕ → ℝ) (hb : ∀ p ∈ S, |f p - h p| ≤ c p) :
    |∑ p ∈ S, f p - ∑ p ∈ S, h p| ≤ ∑ p ∈ S, c p := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb)

/-- `|a − V·0| ≤ ε V` for `a = 0`. -/
private theorem zero_case {V ε : ℝ} (hV : 0 < V) (hε : 0 < ε) : |(0 : ℝ) - V * 0| ≤ ε * V := by
  simp only [mul_zero, sub_zero, abs_zero]; positivity

/-! ## Depth 0 -/

/-- **B.3 for `B⁺_0`**: `|B⁺_0(D,w) − V(w) β⁺_0(s)| ≤ ε V(w)` for `D ≥ D₁`, `2 ≤ w ≤ D`. -/
theorem finite_plus_zero (b : ℕ) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |BP b 0 D w - VB b w * betaP 0 (Real.log D / Real.log w)| ≤ ε * VB b w := by
  obtain ⟨D₁, hD₁, hrat⟩ := VB_cube_ratio b hb (δ := ε / 2) (by positivity)
  set T : ℝ := 2 * (3 + ε / 2) / ε with hT
  have hT0 : 0 < T := by positivity
  have hTε : ε / 2 * T = 3 + ε / 2 := by rw [hT]; field_simp
  refine ⟨max D₁ (T ^ 3), fun D hD w hw2 hwD => ?_⟩
  have hD1 : 1 < D := lt_of_lt_of_le hD₁ (le_trans (le_max_left _ _) hD)
  have hD0 : 0 ≤ D := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hV := VB_pos' b w
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlD : 0 < Real.log D := Real.log_pos hD1
  set c := D ^ (1 / 3 : ℝ) with hc
  have hTc : T ≤ c := (cube_le_iff hD0 hT0.le).1 (le_trans (le_max_right _ _) hD)
  rcases le_or_gt w c with hwc | hcw
  · have hw3 : w ^ 3 ≤ D := (cube_le_iff hD0 hw0).2 hwc
    rw [BP_eq_zero_of_pow_le b 0 (by simpa using hw3)]
    have hs : 2 * ((0 : ℕ) : ℝ) + 3 ≤ Real.log D / Real.log w := by
      rw [le_div_iff₀ hlw]
      have := Real.log_le_log (by positivity) hw3
      rw [Real.log_pow] at this
      push_cast at this ⊢; linarith
    rw [betaP_eq_zero 0 hs]
    exact zero_case hV hε
  · have hD3 : D < w ^ 3 := (lt_cube_iff hD0 hw0).2 hcw
    have hs3 : Real.log D / Real.log w ≤ 3 := by
      rw [div_le_iff₀ hlw]
      have := Real.log_lt_log (by linarith) hD3
      rw [Real.log_pow] at this
      push_cast at this; linarith
    have hs1 : 1 ≤ Real.log D / Real.log w := by
      rw [le_div_iff₀ hlw]; linarith [Real.log_le_log (by linarith) hwD]
    have hs0 : 0 < Real.log D / Real.log w := by linarith
    rw [betaP_zero_of_le_three hs0 hs3, BP_zero_eq, sum_cube_gt_eq b w hD0, min_eq_right hcw.le]
    obtain ⟨hE0, hE1⟩ := pointSum_gV_le b w (c := c) (Real.rpow_nonneg hD0 _)
    have key := abs_le.1 (hrat D (le_trans (le_max_left _ _) hD) w hcw.le hwD)
    generalize hEdef : ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), gB b p * VB b p = E at hE0 hE1 ⊢
    set s := Real.log D / Real.log w with hs_def
    have hc0 : 0 < c := lt_of_lt_of_le hT0 hTc
    have h3s : 3 / s ≤ 3 := div_le_self (by norm_num) hs1
    have hVc : VB b c ≤ (3 + ε / 2) * VB b w := by nlinarith [key.2]
    have hEc : E * c ≤ VB b c := by rwa [le_div_iff₀ hc0] at hE1
    have hE2 : E ≤ ε / 2 * VB b w := by
      by_contra hcon
      push Not at hcon
      have : ε / 2 * VB b w * T ≤ E * c := by
        apply mul_le_mul hcon.le hTc hT0.le hE0
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith [key.1, key.2]

/-! ## Induction steps -/

/-- **B.3 step `B⁺_k → B⁻_{k+1}`** (`s ≥ 2`, i.e. `w ≤ D^{1/2}`). -/
theorem finite_minus_succ (b : ℕ) (hb : 2 ≤ b) (k : ℕ)
    (ih : ∀ ε : ℝ, 0 < ε → ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |BP b k D w - VB b w * betaP k (Real.log D / Real.log w)| ≤ ε * VB b w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D ^ (1 / 2 : ℝ) →
      |BM b (k + 1) D w - VB b w * betaM (k + 1) (Real.log D / Real.log w)| ≤ ε * VB b w := by
  set M : ℝ := 2 * (k : ℝ) + 3 with hM
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hM1 : 1 < M := by linarith
  set ε' : ℝ := ε / (2 * (M + 1)) with hε'_def
  have hε' : 0 < ε' := div_pos hε (by linarith)
  have hε'M : ε' * (M + 1) = ε / 2 := by rw [hε'_def]; field_simp
  obtain ⟨E, hE⟩ := ih ε' hε'
  obtain ⟨D₂, hD₂, hmass⟩ := mass_sp_lt_le b hb (M := M) (σ₀ := 2) (S₁ := M + 1)
    (by linarith) (by norm_num) (by linarith)
  have hcont : ContinuousOn (betaP k) (Set.Icc 1 M) :=
    fun x hx => (continuousAt_betaP k (by linarith [hx.1])).continuousWithinAt
  have hzero : ∀ u, M < u → betaP k u = 0 := fun u hu => betaP_eq_zero k (by linarith)
  obtain ⟨D₃, hD₃, hps⟩ := primeSum1_all b hb (M := M) (S₁ := M + 1) hM1 (by linarith) hcont hzero
    (ε := ε / 2) (by positivity)
  refine ⟨max (max D₂ D₃) (E ^ 2), fun D hD w hw2 hwD => ?_⟩
  have hD2 : D₂ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD3 : D₃ ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hDE : E ^ 2 ≤ D := le_trans (le_max_right _ _) hD
  have hD1 : 1 < D := lt_of_lt_of_le hD₂ hD2
  have hD0 : 0 < D := by linarith
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hV := VB_pos' b w
  have hw_sq : w ^ 2 ≤ D := sq_le_of_le_rpow_half (by linarith) hD0.le hwD
  have hs2 : 2 ≤ Real.log D / Real.log w := by
    rw [le_div_iff₀ hlw]
    have := Real.log_le_log (by positivity) hw_sq
    rw [Real.log_pow] at this; push_cast at this; linarith
  by_cases hsS : Real.log D / Real.log w ≤ M + 1
  · obtain ⟨hlo, -⟩ := rpow_bounds_of_s hD1 hw1 (σ₀ := 2) (S₁ := M + 1) (by norm_num) hs2 hsS
    have hmass' := hmass D hD2 w hlo hwD
    have hps' := hps D hD3 w hlo hwD
    rw [BM_succ_eq, betaM_succ]
    have herr : |∑ p ∈ primesBelow w, gB b p * BP b k (D / p) p -
        ∑ p ∈ primesBelow w, gB b p * VB b p * betaP k (Real.log D / Real.log p - 1)| ≤
        ε' * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M),
          gB b p * VB b p := by
      rw [mul_sum, sum_filter]
      apply abs_sum_sub_le
      intro p hp
      rw [mem_primesBelow] at hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hp1 : (1 : ℝ) < p := by linarith
      have hpD : (p : ℝ) ^ 2 ≤ D := le_trans (pow_le_pow_left₀ hp0.le hp.2.le 2) hw_sq
      have hDp0 : 0 < D / p := div_pos hD0 hp0
      have hsp := log_div_div_log hD0 hp1
      split_ifs with hlt
      · have hin : (p : ℝ) ≤ D / p := by rw [le_div_iff₀ hp0]; nlinarith
        have h := hE (D / p) (le_div_of_sq_le hp0 hpD hDE) p hp2 hin
        rw [hsp] at h
        rw [show gB b p * BP b k (D / p) p - gB b p * VB b p * betaP k (Real.log D / Real.log p - 1) =
            gB b p * (BP b k (D / p) p - VB b p * betaP k (Real.log D / Real.log p - 1)) by ring,
          abs_mul, abs_of_nonneg (gB_nonneg b p)]
        calc gB b p * |BP b k (D / p) p - VB b p * betaP k (Real.log D / Real.log p - 1)|
            ≤ gB b p * (ε' * VB b p) := mul_le_mul_of_nonneg_left h (gB_nonneg b p)
          _ = ε' * (gB b p * VB b p) := by ring
      · push Not at hlt
        rw [BP_eq_zero_of_s b k hDp0 hp1 (by rw [hsp]; exact hlt), betaP_eq_zero k hlt]
        simp
    have hmass'' : ε' * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M),
        gB b p * VB b p ≤ ε / 2 * VB b w := by
      calc _ ≤ ε' * ((M + 1) * VB b w) := mul_le_mul_of_nonneg_left hmass' hε'.le
        _ = ε / 2 * VB b w := by rw [← mul_assoc, hε'M]
    calc _ ≤ |∑ p ∈ primesBelow w, gB b p * BP b k (D / p) p -
            ∑ p ∈ primesBelow w, gB b p * VB b p * betaP k (Real.log D / Real.log p - 1)| +
          |∑ p ∈ primesBelow w, gB b p * VB b p * betaP k (Real.log D / Real.log p - 1) -
            VB b w * ((Real.log D / Real.log w)⁻¹ *
              ∫ u in Set.Ioi (Real.log D / Real.log w - 1), betaP k u)| := abs_sub_le _ _ _
      _ ≤ ε / 2 * VB b w + ε / 2 * VB b w := add_le_add (herr.trans hmass'') hps'
      _ = ε * VB b w := by ring
  · push Not at hsS
    rw [BM_eq_zero_of_s b (k + 1) hD0 hw1 (by push_cast; linarith),
      betaM_eq_zero (k + 1) (by push_cast; linarith)]
    exact zero_case hV hε

/-- **B.3 step `B⁻_{k+1} → B⁺_{k+1}`** (`2 ≤ w ≤ D`). -/
theorem finite_plus_succ (b : ℕ) (hb : 2 ≤ b) (k : ℕ)
    (ih : ∀ ε : ℝ, 0 < ε → ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D ^ (1 / 2 : ℝ) →
      |BM b (k + 1) D w - VB b w * betaM (k + 1) (Real.log D / Real.log w)| ≤ ε * VB b w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |BP b (k + 1) D w - VB b w * betaP (k + 1) (Real.log D / Real.log w)| ≤ ε * VB b w := by
  set M : ℝ := 2 * (k : ℝ) + 4 with hM
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hM2 : 2 < M := by linarith
  set ε' : ℝ := ε / (2 * (M + 1)) with hε'_def
  have hε' : 0 < ε' := div_pos hε (by linarith)
  have hε'M : ε' * (M + 1) = ε / 2 := by rw [hε'_def]; field_simp
  obtain ⟨E, hE⟩ := ih ε' hε'
  obtain ⟨D₂, hD₂, hmass⟩ := mass_sp_lt_le b hb (M := M) (σ₀ := 1) (S₁ := M + 1)
    (by linarith) le_rfl (by linarith)
  have hcont : ContinuousOn (betaM (k + 1)) (Set.Icc 2 M) :=
    fun x hx => (continuousAt_betaM (k + 1) (by linarith [hx.1])).continuousWithinAt
  have hzero : ∀ u, M < u → betaM (k + 1) u = 0 :=
    fun u hu => betaM_eq_zero (k + 1) (by push_cast; linarith)
  obtain ⟨D₃, hD₃, hps⟩ := primeSum1_cube b hb (M := M) (σ₀ := 1) (S₁ := M + 1) hM2 le_rfl (by linarith)
    hcont hzero (ε := ε / 2) (by positivity)
  refine ⟨max (max D₂ D₃) (E ^ 2), fun D hD w hw2 hwD => ?_⟩
  have hD2 : D₂ ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hD
  have hD3 : D₃ ≤ D := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hD
  have hDE : E ^ 2 ≤ D := le_trans (le_max_right _ _) hD
  have hD1 : 1 < D := lt_of_lt_of_le hD₂ hD2
  have hD0 : 0 < D := by linarith
  have hw1 : 1 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw1
  have hV := VB_pos' b w
  have hs1 : 1 ≤ Real.log D / Real.log w := by
    rw [le_div_iff₀ hlw]; linarith [Real.log_le_log (by linarith) hwD]
  by_cases hsS : Real.log D / Real.log w ≤ M + 1
  · obtain ⟨hlo, hhi⟩ := rpow_bounds_of_s hD1 hw1 (σ₀ := 1) (S₁ := M + 1) (by norm_num) hs1 hsS
    have hmass' := hmass D hD2 w hlo hhi
    have hps' := hps D hD3 w hlo hhi
    rw [BP_succ_eq, betaP_succ]
    have herr : |∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), gB b p * BM b (k + 1) (D / p) p -
        ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
          gB b p * VB b p * betaM (k + 1) (Real.log D / Real.log p - 1)| ≤
        ε' * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M),
          gB b p * VB b p := by
      set c : ℕ → ℝ := fun p => if Real.log D / Real.log p - 1 < M then ε' * (gB b p * VB b p) else 0
        with hc_def
      have herr1 : |∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), gB b p * BM b (k + 1) (D / p) p -
          ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
            gB b p * VB b p * betaM (k + 1) (Real.log D / Real.log p - 1)| ≤
          ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), c p := by
        apply abs_sum_sub_le
        intro p hp
        rw [hc_def]
        dsimp only
        rw [mem_filter, mem_primesBelow] at hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.1.two_le
        have hp0 : (0 : ℝ) < p := by linarith
        have hp1 : (1 : ℝ) < p := by linarith
        have hp3 : (p : ℝ) ^ 3 ≤ D := hp.2
        have hp23 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := pow_le_pow_right₀ hp1.le (by norm_num)
        have hpD : (p : ℝ) ^ 2 ≤ D := le_trans hp23 hp3
        have hDp0 : 0 < D / p := div_pos hD0 hp0
        have hsp := log_div_div_log hD0 hp1
        split_ifs with hlt
        · have hin : (p : ℝ) ≤ (D / p) ^ (1 / 2 : ℝ) :=
            le_rpow_half_of_sq_le (by rw [le_div_iff₀ hp0]; nlinarith)
          have h := hE (D / p) (le_div_of_sq_le hp0 hpD hDE) p hp2 hin
          rw [hsp] at h
          rw [show gB b p * BM b (k + 1) (D / p) p -
                gB b p * VB b p * betaM (k + 1) (Real.log D / Real.log p - 1) =
              gB b p * (BM b (k + 1) (D / p) p - VB b p * betaM (k + 1) (Real.log D / Real.log p - 1)) by ring,
            abs_mul, abs_of_nonneg (gB_nonneg b p)]
          calc gB b p * |BM b (k + 1) (D / p) p - VB b p * betaM (k + 1) (Real.log D / Real.log p - 1)|
              ≤ gB b p * (ε' * VB b p) := mul_le_mul_of_nonneg_left h (gB_nonneg b p)
            _ = ε' * (gB b p * VB b p) := by ring
        · push Not at hlt
          rw [BM_eq_zero_of_s b (k + 1) hDp0 hp1 (by rw [hsp]; push_cast; linarith),
            betaM_eq_zero (k + 1) (by push_cast; linarith)]
          simp
      have herr2 : ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), c p ≤
          ε' * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M),
            gB b p * VB b p := by
        have hc0 : ∀ p : ℕ, 0 ≤ c p := by
          intro p
          rw [hc_def]
          dsimp only
          split_ifs
          · exact mul_nonneg hε'.le (mul_nonneg (gB_nonneg b p) (VB_pos' b p).le)
          · exact le_rfl
        calc ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), c p
            ≤ ∑ p ∈ primesBelow w, c p :=
              Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hc0 p)
          _ = _ := by rw [hc_def, mul_sum, sum_filter]
      exact herr1.trans herr2
    have hmass'' : ε' * ∑ p ∈ (primesBelow w).filter (fun p : ℕ => Real.log D / Real.log p - 1 < M),
        gB b p * VB b p ≤ ε / 2 * VB b w := by
      calc _ ≤ ε' * ((M + 1) * VB b w) := mul_le_mul_of_nonneg_left hmass' hε'.le
        _ = ε / 2 * VB b w := by rw [← mul_assoc, hε'M]
    calc _ ≤ |∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), gB b p * BM b (k + 1) (D / p) p -
            ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
              gB b p * VB b p * betaM (k + 1) (Real.log D / Real.log p - 1)| +
          |∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
              gB b p * VB b p * betaM (k + 1) (Real.log D / Real.log p - 1) -
            VB b w * ((Real.log D / Real.log w)⁻¹ *
              ∫ u in Set.Ioi (max (Real.log D / Real.log w - 1) 2), betaM (k + 1) u)| := abs_sub_le _ _ _
      _ ≤ ε / 2 * VB b w + ε / 2 * VB b w := add_le_add (herr.trans hmass'') hps'
      _ = ε * VB b w := by ring
  · push Not at hsS
    rw [BP_eq_zero_of_s b (k + 1) hD0 hw1 (by push_cast; linarith),
      betaP_eq_zero (k + 1) (by push_cast; linarith)]
    exact zero_case hV hε

/-! ## Lemma B.3 -/

/-- **Lemma B.3, joint induction**: at depth `k`, the `B⁺_k` statement and the `B⁻_{k+1}` statement. -/
theorem finite_depth (b : ℕ) (hb : 2 ≤ b) (k : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |BP b k D w - VB b w * betaP k (Real.log D / Real.log w)| ≤ ε * VB b w) ∧
    (∀ ε : ℝ, 0 < ε → ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D ^ (1 / 2 : ℝ) →
      |BM b (k + 1) D w - VB b w * betaM (k + 1) (Real.log D / Real.log w)| ≤ ε * VB b w) := by
  induction k with
  | zero =>
    have h0 := fun ε (hε : (0 : ℝ) < ε) => finite_plus_zero b hb hε
    exact ⟨h0, fun ε hε => finite_minus_succ b hb 0 h0 hε⟩
  | succ k ih =>
    have hp := fun ε (hε : (0 : ℝ) < ε) => finite_plus_succ b hb k ih.2 hε
    exact ⟨hp, fun ε hε => finite_minus_succ b hb (k + 1) hp hε⟩

/-- **Lemma B.3 (+)**: for every `k` and `ε > 0` there is `D₁` with
`|B⁺_k(D,w) − V(w) β⁺_k(log D / log w)| ≤ ε V(w)` for all `D ≥ D₁` and `2 ≤ w ≤ D`. -/
theorem finite_depth_plus (b : ℕ) (hb : 2 ≤ b) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |BP b k D w - VB b w * betaP k (Real.log D / Real.log w)| ≤ ε * VB b w :=
  (finite_depth b hb k).1 ε hε

/-- **Lemma B.3 (−)**: for every `k` and `ε > 0` there is `D₁` with
`|B⁻_k(D,w) − V(w) β⁻_k(log D / log w)| ≤ ε V(w)` for all `D ≥ D₁` and `2 ≤ w ≤ D^{1/2}`
(`k = 0` is trivial: `B⁻_0 = 0 = β⁻_0`). -/
theorem finite_depth_minus (b : ℕ) (hb : 2 ≤ b) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D ^ (1 / 2 : ℝ) →
      |BM b k D w - VB b w * betaM k (Real.log D / Real.log w)| ≤ ε * VB b w := by
  cases k with
  | zero =>
    refine ⟨0, fun D _ w _ _ => ?_⟩
    rw [BM_zero, betaM_zero]
    exact zero_case (VB_pos' b w) hε
  | succ k => exact (finite_depth b hb k).2 ε hε

/-- **B.3 summed over depths `k < K` (+)**, the form used in the assembly (§6). -/
theorem finite_depth_sum_plus (b : ℕ) (hb : 2 ≤ b) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D →
      |∑ k ∈ range K, BP b k D w - VB b w * ∑ k ∈ range K, betaP k (Real.log D / Real.log w)| ≤
        ε * VB b w := by
  induction K generalizing ε with
  | zero => exact ⟨0, fun D _ w _ _ => by simpa using zero_case (VB_pos' b w) hε⟩
  | succ K ih =>
    obtain ⟨D₁, h₁⟩ := ih (ε := ε / 2) (by positivity)
    obtain ⟨D₂, h₂⟩ := finite_depth_plus b hb K (ε := ε / 2) (by positivity)
    refine ⟨max D₁ D₂, fun D hD w hw2 hwD => ?_⟩
    have a1 := h₁ D (le_trans (le_max_left _ _) hD) w hw2 hwD
    have a2 := h₂ D (le_trans (le_max_right _ _) hD) w hw2 hwD
    rw [sum_range_succ, sum_range_succ, mul_add]
    calc _ = |(∑ k ∈ range K, BP b k D w - VB b w * ∑ k ∈ range K, betaP k (Real.log D / Real.log w)) +
          (BP b K D w - VB b w * betaP K (Real.log D / Real.log w))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 * VB b w + ε / 2 * VB b w := add_le_add a1 a2
      _ = ε * VB b w := by ring

/-- **B.3 summed over depths `k < K` (−)**, the form used in the assembly (§6). -/
theorem finite_depth_sum_minus (b : ℕ) (hb : 2 ≤ b) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D₁ : ℝ, ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, 2 ≤ w → w ≤ D ^ (1 / 2 : ℝ) →
      |∑ k ∈ range K, BM b k D w - VB b w * ∑ k ∈ range K, betaM k (Real.log D / Real.log w)| ≤
        ε * VB b w := by
  induction K generalizing ε with
  | zero => exact ⟨0, fun D _ w _ _ => by simpa using zero_case (VB_pos' b w) hε⟩
  | succ K ih =>
    obtain ⟨D₁, h₁⟩ := ih (ε := ε / 2) (by positivity)
    obtain ⟨D₂, h₂⟩ := finite_depth_minus b hb K (ε := ε / 2) (by positivity)
    refine ⟨max D₁ D₂, fun D hD w hw2 hwD => ?_⟩
    have a1 := h₁ D (le_trans (le_max_left _ _) hD) w hw2 hwD
    have a2 := h₂ D (le_trans (le_max_right _ _) hD) w hw2 hwD
    rw [sum_range_succ, sum_range_succ, mul_add]
    calc _ = |(∑ k ∈ range K, BM b k D w - VB b w * ∑ k ∈ range K, betaM k (Real.log D / Real.log w)) +
          (BM b K D w - VB b w * betaM K (Real.log D / Real.log w))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 * VB b w + ε / 2 * VB b w := add_le_add a1 a2
      _ = ε * VB b w := by ring

end Palprimes.E1
