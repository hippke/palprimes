import Omega3.Statements
import Omega3.Items.S08_E

/-! # Item S08: Lemma A part 3, `λ₁ + λ_q = g_η(u) + o(1)` uniformly in primes `x^{u_lo} ≤ q < √x`.
Proof plan in `Omega3/Items/S08_PLAN.md`. -/

namespace Omega3

open Finset Palprimes
open scoped ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma s08_lam1 (b : ℕ) (e : StepFn) (x : ℝ) (hG : 0 < GS b (Real.sqrt x)) : lamA b e x 1 = 1 := by
  classical
  set z := Real.sqrt x with hzdef
  unfold lamA
  rw [← hzdef, if_pos (Nat.coprime_one_left _)]
  have hfil : (ltSet z).filter (fun k => 1 ∣ k) = ltSet z := Finset.filter_true_of_mem (fun k _ => one_dvd k)
  rw [hfil]
  have e1 : ∀ k ∈ ltSet z, (μ (k / 1) : ℝ) * ykA b e x k = gS b k * (nuA b e x - etaK b e x k) := by
    intro k _
    unfold ykA
    rw [Nat.div_one, ← mul_assoc, ← mul_assoc]
    by_cases hg : Squarefree k ∧ Nat.Coprime k (bigB b)
    · have : (μ k : ℝ) * (μ k : ℝ) = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg.1
        have h2 : ((μ k : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast this
        nlinarith
      rw [this, one_mul]
    · unfold gS; rw [if_neg hg]; ring
  rw [Nat.cast_one, one_mul, Finset.sum_congr rfl e1]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hnu : nuA b e x = (1 + ∑ k ∈ ltSet z, gS b k * etaK b e x k) / GS b z := rfl
  rw [hnu]
  show GS b z * ((1 + ∑ k ∈ ltSet z, gS b k * etaK b e x k) / GS b z) - _ = 1
  field_simp
  ring

lemma s08_u0_le_one (e : StepFn) : s08u0 e ≤ 1 := by
  unfold s08u0
  have : ∀ l : List (ℚ × ℚ), (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 ≤ 1 := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.foldr_cons]; exact le_trans (min_le_right _ _) ih
  exact this e

set_option maxHeartbeats 4000000 in
/-- S08 for one step function. -/
theorem s08_single (b : ℕ) (hb : 2 ≤ b) (e : StepFn) (he : StepOK e) (ulo ε : ℝ) (hulo : 0 < ulo) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ q : ℕ, q.Prime → x ^ ulo ≤ (q : ℝ) → (q : ℝ) < Real.sqrt x →
      |lamA b e x 1 + lamA b e x q - gEta e (Real.log q / Real.log (Real.sqrt x))| ≤ ε := by
  classical
  have he' : ∀ pr ∈ e, (0 : ℚ) < pr.1 := fun pr h => (he.2 pr h).1
  set M := s08Mv e with hMdef
  set u0 := s08u0 e with hu0def
  have hM0 : 0 ≤ M := s08_Mv_nonneg e
  have hu0 : 0 < u0 := s08_u0_pos e he'
  have hu01 : u0 ≤ 1 := s08_u0_le_one e
  obtain ⟨CG, hCG0, hCG⟩ := s08_G_asymp b hb
  set β := s08beta b with hβdef
  have hβ : 0 < β := s08_beta_pos b
  set Kp := Real.log (1 / u0) + 1 with hKpdef
  have hKp : 0 ≤ Kp := by
    have : 0 ≤ Real.log (1 / u0) := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
    linarith
  set A1 := Ahat e 1 with hA1
  set Q := 2 + |A1| + 3 * (M * Kp) + 2 * M with hQdef
  have hMK : 0 ≤ M * Kp := mul_nonneg hM0 hKp
  have hQ : 2 ≤ Q := by have := abs_nonneg A1; linarith
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set ε' := ε₁ / 4 with hε'
  obtain ⟨KPS, hKPS⟩ := s08_PS e he' ε' (by positivity)
  obtain ⟨Km, hKm⟩ := s08_mass e he'
  set c := min u0 (2 * ulo) with hc
  have hc0 : 0 < c := lt_min hu0 (by linarith)
  set Y0 : ℝ := (bigB b : ℝ) + 2 + 44 * Q / ε₁ with hY0
  have hY0p : 0 < Y0 := by positivity
  set GC : ℝ := max 1 (8 * Q * CG / ε₁) with hGC
  set K : ℝ := max (max KPS Km) (max (Real.log Y0 / c) (max ((GC + CG) / β) 1)) with hK
  refine ⟨Real.exp (2 * K), ?_⟩
  intro x hx q hq hqx hqz
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set z := Real.sqrt x with hzdef
  set L := Real.log z with hLdef
  have hlogx : Real.log x = 2 * L := by rw [hLdef, hzdef, Real.log_sqrt hx0.le]; ring
  have hLK : K ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rw [Real.log_exp] at this; linarith
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hLK
  have hz0 : 0 < z := Real.sqrt_pos.2 hx0
  have hz1 : 1 < z := by
    have : 0 < Real.log z := by linarith
    exact (Real.log_pos_iff hz0.le).1 this
  have hLPS : KPS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLK
  have hLm : Km ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLK
  have hLY : Real.log Y0 / c ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLK
  have hLG : (GC + CG) / β ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hLK
  -- `G`
  set G := GS b z with hGdef
  have hGz := hCG z hz1.le
  rw [abs_le] at hGz
  have hGlow : β * L - CG ≤ G := by linarith [hGz.1]
  have hGGC : GC ≤ G := by
    rw [div_le_iff₀ hβ] at hLG; linarith
  have hG1 : 1 ≤ G := le_trans (le_max_left _ _) hGGC
  have hG0 : 0 < G := by linarith
  have hGC2 : 2 * CG / G ≤ ε₁ / (4 * Q) := by
    rw [div_le_div_iff₀ hG0 (by positivity)]
    have : 8 * Q * CG / ε₁ ≤ G := le_trans (le_max_right _ _) hGGC
    rw [div_le_iff₀ hε₁0] at this
    linarith
  -- `Y = exp(cL)` and `T = 1/(Y − 1)`
  set Y := Real.exp (c * L) with hYdef
  have hYY0 : Y0 ≤ Y := by
    rw [div_le_iff₀ hc0] at hLY
    rw [hYdef, ← Real.exp_log hY0p]
    exact Real.exp_le_exp.2 (by linarith)
  have hY2 : (bigB b : ℝ) + 2 ≤ Y := by
    have : 0 ≤ 44 * Q / ε₁ := by positivity
    linarith
  have hY1 : 1 < Y := by have := (Nat.cast_nonneg (bigB b) : (0 : ℝ) ≤ _); linarith
  set T := 1 / (Y - 1) with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; apply div_nonneg zero_le_one; linarith
  have hT : 11 * T ≤ ε₁ / (4 * Q) := by
    rw [hTdef]
    have h1 : 44 * Q / ε₁ ≤ Y - 1 := by have := (Nat.cast_nonneg (bigB b) : (0 : ℝ) ≤ _); linarith
    have h2 : 0 < 44 * Q / ε₁ := by positivity
    rw [div_le_iff₀ hε₁0] at h1
    rw [mul_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hT1 : T ≤ 1 := by
    rw [hTdef, div_le_one (by linarith)]; linarith
  have hbig : ∀ p : ℕ, p.Prime → Y ≤ p → Nat.Coprime p (bigB b) ∧ gS b p ≤ T := by
    intro p hp hpY
    refine ⟨?_, s08_gS_le b p hp Y hY1 hpY⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hB0 : 0 < bigB b := Nat.pos_of_ne_zero (s08_bigB_ne_zero b hb)
    have := Nat.le_of_dvd hB0 hdvd
    have : (p : ℝ) ≤ bigB b := by exact_mod_cast this
    linarith
  -- `q`
  have hqY : Y ≤ q := by
    refine le_trans ?_ hqx
    rw [Real.rpow_def_of_pos hx0, hlogx, hYdef]
    apply Real.exp_le_exp.2
    have : c ≤ 2 * ulo := min_le_right _ _
    have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ L)
    linarith
  obtain ⟨hqB, hTq⟩ := hbig q hq hqY
  have hqPz : q ∈ s08Pz z := by
    unfold s08Pz; rw [Finset.mem_filter, s08_mem_ltSet]; exact ⟨⟨hq.one_lt.le, hqz⟩, hq⟩
  set u := s08u z q with hudef
  have hu1 : u < 1 := s08_u_lt_one z hz1 q hqPz
  have hu0' : 0 < u := by
    rw [hudef]; unfold s08u
    exact div_pos (Real.log_pos (by exact_mod_cast hq.one_lt)) (by linarith)
  have hpY : ∀ p ∈ s08Pz z, StepFn.eval e (s08u z p) ≠ 0 → Y ≤ p := by
    intro p hp hne
    have h1 : u0 ≤ s08u z p := by
      by_contra hcon; push_neg at hcon; exact hne (s08_eval_zero e _ hcon)
    unfold s08u at h1
    rw [le_div_iff₀ (by linarith)] at h1
    have hp0 : (0 : ℝ) < p := by
      unfold s08Pz at hp; rw [Finset.mem_filter] at hp; exact_mod_cast hp.2.pos
    rw [hYdef, ← Real.exp_log hp0]
    apply Real.exp_le_exp.2
    have : c ≤ u0 := min_le_left _ _
    have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ L)
    linarith
  -- `δ`
  set δ := 11 * T + 2 * CG / G with hδdef
  have hδ : Q * δ ≤ ε₁ / 2 := by
    have : δ ≤ ε₁ / (4 * Q) + ε₁ / (4 * Q) := by linarith
    have e2 : Q * (ε₁ / (4 * Q) + ε₁ / (4 * Q)) = ε₁ / 2 := by field_simp; ring
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ Q)
    linarith
  have hδ0 : 0 ≤ δ := by have : 0 ≤ 2 * CG / G := by positivity
                         linarith
  have hδ1 : δ ≤ 1 := by
    have : Q * δ ≤ 1 / 2 := by linarith
    have := mul_le_mul_of_nonneg_right hQ hδ0
    linarith
  -- ratios
  have hRq : |(q : ℝ) * s08A b z q / G - (1 - u)| ≤ δ := by
    have h := s08_ratio b CG hCG z hz1 hG1 q hq.one_lt.le (3 * T) (s08_err_q b z hz0 q hq hqB T hTq hT1)
    have hm : max (1 - Real.log q / Real.log z) 0 = 1 - u := by
      rw [max_eq_left (by have : Real.log q / Real.log z = u := rfl; linarith)]; rfl
    rw [hm] at h
    have : 3 * T ≤ 11 * T := by linarith
    linarith
  have hRp : ∀ p ∈ s08Pz z, StepFn.eval e (s08u z p) ≠ 0 →
      |(p : ℝ) * s08A b z p / G - max (1 - s08u z p) 0| ≤ δ := by
    intro p hp hne
    have hpp : p.Prime := by unfold s08Pz at hp; exact (Finset.mem_filter.1 hp).2
    obtain ⟨hpB, hTp⟩ := hbig p hpp (hpY p hp hne)
    have h := s08_ratio b CG hCG z hz1 hG1 p hpp.one_lt.le (3 * T) (s08_err_q b z hz0 p hpp hpB T hTp hT1)
    have : 3 * T ≤ 11 * T := by linarith
    unfold s08u; linarith
  have hRpq : ∀ p ∈ (s08Pz z).erase q, StepFn.eval e (s08u z p) ≠ 0 →
      |((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0| ≤ δ := by
    intro p hp hne
    rw [Finset.mem_erase] at hp
    have hpp : p.Prime := by unfold s08Pz at hp; exact (Finset.mem_filter.1 hp.2).2
    obtain ⟨hpB, hTp⟩ := hbig p hpp (hpY p hp.2 hne)
    have h := s08_ratio b CG hCG z hz1 hG1 (p * q) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hpp.ne_zero hq.ne_zero))
      (11 * T) (s08_err_pq b z hz0 p q hpp hq hp.1 hpB hqB T hTp hTq hT1)
    have hl : 1 - Real.log ((p * q : ℕ) : ℝ) / Real.log z = 1 - u - s08u z p := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hq.ne_zero), add_div]
      unfold s08u at hudef ⊢; rw [hudef]; ring
    rw [hl] at h
    push_cast at h
    linarith
  -- prime sums
  set S : ℝ → ℝ := fun s => ∑ p ∈ s08Pz z, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) * max (s - s08u z p) 0 with hSdef
  have hS1 : |S 1 - A1| ≤ ε' := hKPS z hz1 hLPS 1 zero_le_one le_rfl
  have hSu : |S (1 - u) - Ahat e (1 - u)| ≤ ε' := hKPS z hz1 hLPS (1 - u) (by linarith) (by linarith)
  have hmass := hKm z hz1 hLm
  -- `H`
  set H := ∑ p ∈ s08Pz z, etaQ b e x p * s08A b z p with hHdef
  have hetaQ : ∀ p : ℕ, etaQ b e x p = StepFn.eval e (s08u z p) / G := fun p => rfl
  have hHS : |H - S 1| ≤ M * Kp * δ := by
    have e1 : H - S 1 = ∑ p ∈ s08Pz z, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
        ((p : ℝ) * s08A b z p / G - max (1 - s08u z p) 0) := by
      rw [hHdef, hSdef]; simp only; rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by
        unfold s08Pz at hp; exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
      rw [hetaQ]; field_simp
    rw [e1]
    calc _ ≤ ∑ p ∈ s08Pz z, |(1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
          ((p : ℝ) * s08A b z p / G - max (1 - s08u z p) 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s08Pz z, (1 / (p : ℝ)) * |StepFn.eval e (s08u z p)| * δ := by
          apply Finset.sum_le_sum; intro p hp
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p)]
          by_cases hne : StepFn.eval e (s08u z p) = 0
          · rw [hne]; simp
          · exact mul_le_mul_of_nonneg_left (hRp p hp hne) (by positivity)
      _ = (∑ p ∈ s08Pz z, (1 / (p : ℝ)) * |StepFn.eval e (s08u z p)|) * δ := by rw [Finset.sum_mul]
      _ ≤ M * Kp * δ := mul_le_mul_of_nonneg_right hmass hδ0
  -- `W`
  set W := ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * ((q : ℝ) * s08A b z (p * q)) with hWdef
  have hWS : |W - S (1 - u)| ≤ M * Kp * δ + M * δ := by
    have hsplit : S (1 - u) = (1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0 +
        ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) * max (1 - u - s08u z p) 0 := by
      rw [hSdef]; simp only; rw [← Finset.add_sum_erase _ _ hqPz]
    have e1 : W - S (1 - u) = ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
        (((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0) -
          (1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0 := by
      rw [hsplit, hWdef]
      have : ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * ((q : ℝ) * s08A b z (p * q)) =
          ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) * (((p : ℝ) * q) * s08A b z (p * q) / G) := by
        apply Finset.sum_congr rfl; intro p hp
        have hp0 : (p : ℝ) ≠ 0 := by
          rw [Finset.mem_erase] at hp
          unfold s08Pz at hp; exact_mod_cast (Finset.mem_filter.1 hp.2).2.ne_zero
        rw [hetaQ]; field_simp
      rw [this]
      have : ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
          (((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0) =
          ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) * (((p : ℝ) * q) * s08A b z (p * q) / G) -
          ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) * max (1 - u - s08u z p) 0 := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring
      rw [this]; ring
    rw [e1]
    have hA : |∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
        (((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0)| ≤ M * Kp * δ := by
      calc _ ≤ ∑ p ∈ (s08Pz z).erase q, |(1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
            (((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * |StepFn.eval e (s08u z p)| * δ := by
            apply Finset.sum_le_sum; intro p hp
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p)]
            by_cases hne : StepFn.eval e (s08u z p) = 0
            · rw [hne]; simp
            · exact mul_le_mul_of_nonneg_left (hRpq p hp hne) (by positivity)
        _ = (∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * |StepFn.eval e (s08u z p)|) * δ := by rw [Finset.sum_mul]
        _ ≤ (∑ p ∈ s08Pz z, (1 / (p : ℝ)) * |StepFn.eval e (s08u z p)|) * δ := by
            apply mul_le_mul_of_nonneg_right _ hδ0
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun p _ _ => by positivity)
        _ ≤ M * Kp * δ := mul_le_mul_of_nonneg_right hmass hδ0
    have hB : |(1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0| ≤ M * δ := by
      have hq1 : 1 / (q : ℝ) ≤ T := by
        refine le_trans ?_ hTq
        rw [s08_gS_prime b q hq hqB]
        have : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
        apply one_div_le_one_div_of_le (by linarith); linarith
      have hm1 : max (1 - u - u) 0 ≤ 1 := max_le (by linarith) zero_le_one
      have hm0 : 0 ≤ max (1 - u - u) 0 := le_max_right _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q), abs_of_nonneg hm0]
      have h1 := s08_eval_abs e u
      have : T ≤ δ := by have : 0 ≤ 2 * CG / G := by positivity
                         linarith
      calc 1 / (q : ℝ) * |StepFn.eval e u| * max (1 - u - u) 0 ≤ T * M * 1 := by
            apply mul_le_mul (mul_le_mul hq1 h1 (abs_nonneg _) hT0) hm1 hm0 (by positivity)
        _ ≤ M * δ := by
            have := mul_le_mul_of_nonneg_left this hM0
            linarith
    calc _ ≤ |∑ p ∈ (s08Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (s08u z p) *
          (((p : ℝ) * q) * s08A b z (p * q) / G - max (1 - u - s08u z p) 0)| +
          |(1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0| := abs_sub _ _
      _ ≤ _ := add_le_add hA hB
  -- the exact formula for `λ₁ + λ_q`
  set R := (q : ℝ) * s08A b z q / G with hRdef
  have hlam1 := s08_lam1 b e x hG0
  have hlamq := s08_lamq b e x q hq hqB
  rw [← hzdef] at hlamq
  rw [← Finset.add_sum_erase _ _ hqPz, s08_A2_self] at hlamq
  have hA2 : ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * s08A2 b z p q =
      ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * s08A b z (p * q) := by
    apply Finset.sum_congr rfl; intro p hp
    rw [Finset.mem_erase] at hp
    have hpp : p.Prime := by unfold s08Pz at hp; exact (Finset.mem_filter.1 hp.2).2
    rw [s08_A2_ne b z p q hpp hq hp.1]
  rw [hA2] at hlamq
  have hnu : nuA b e x = (1 + H) / G := by
    unfold nuA; rw [← hzdef, s08_H b e x, ← hzdef]
  have hform : lamA b e x 1 + lamA b e x q = 1 - (1 + H) * R + StepFn.eval e u * R + W := by
    rw [hlam1, hlamq, hnu, hRdef, hWdef, hetaQ q]
    have : ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * ((q : ℝ) * s08A b z (p * q)) =
        (q : ℝ) * ∑ p ∈ (s08Pz z).erase q, etaQ b e x p * s08A b z (p * q) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [this]
    field_simp
    ring
  have hgE : gEta e (Real.log q / Real.log (Real.sqrt x)) =
      1 - (1 + A1) * (1 - u) + Ahat e (1 - u) + StepFn.eval e u * (1 - u) := rfl
  rw [hform, hgE]
  -- final estimate
  have hRu := hRq
  have hH : |H - A1| ≤ M * Kp * δ + ε' := by
    calc |H - A1| ≤ |H - S 1| + |S 1 - A1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hHS hS1
  have hW : |W - Ahat e (1 - u)| ≤ M * Kp * δ + M * δ + ε' := by
    calc |W - Ahat e (1 - u)| ≤ |W - S (1 - u)| + |S (1 - u) - Ahat e (1 - u)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hWS hSu
  have hHabs : |H| ≤ |A1| + M * Kp * δ + ε' := by
    have := abs_sub_abs_le_abs_sub H A1; linarith
  have hε'1 : ε' ≤ 1 := by rw [hε']; linarith
  have hηu := s08_eval_abs e u
  have e3 : 1 - (1 + H) * R + StepFn.eval e u * R + W - (1 - (1 + A1) * (1 - u) + Ahat e (1 - u) + StepFn.eval e u * (1 - u)) =
      -((1 + H) * (R - (1 - u))) - (H - A1) * (1 - u) + StepFn.eval e u * (R - (1 - u)) + (W - Ahat e (1 - u)) := by ring
  rw [e3]
  have hu1' : 0 ≤ 1 - u := by linarith
  have hu1'' : 1 - u ≤ 1 := by linarith
  have t1 : |(1 + H) * (R - (1 - u))| ≤ (1 + |A1| + M * Kp * δ + ε') * δ := by
    rw [abs_mul]
    apply mul_le_mul _ hRu (abs_nonneg _) (by positivity)
    calc |1 + H| ≤ |(1 : ℝ)| + |H| := abs_add_le _ _
      _ ≤ _ := by rw [abs_one]; linarith
  have t2 : |(H - A1) * (1 - u)| ≤ M * Kp * δ + ε' := by
    rw [abs_mul, abs_of_nonneg hu1']
    calc |H - A1| * (1 - u) ≤ |H - A1| * 1 := mul_le_mul_of_nonneg_left hu1'' (abs_nonneg _)
      _ ≤ _ := by linarith
  have t3 : |StepFn.eval e u * (R - (1 - u))| ≤ M * δ := by
    rw [abs_mul]; exact mul_le_mul hηu hRu (abs_nonneg _) hM0
  have hMKδ : M * Kp * δ ≤ M * Kp := mul_le_of_le_one_right hMK hδ1
  calc _ ≤ |-((1 + H) * (R - (1 - u)))| + |(H - A1) * (1 - u)| + |StepFn.eval e u * (R - (1 - u))| +
        |W - Ahat e (1 - u)| := by
        have h1 := abs_add_le (-((1 + H) * (R - (1 - u))) - (H - A1) * (1 - u) + StepFn.eval e u * (R - (1 - u)))
          (W - Ahat e (1 - u))
        have h2 := abs_add_le (-((1 + H) * (R - (1 - u))) - (H - A1) * (1 - u)) (StepFn.eval e u * (R - (1 - u)))
        have h3 := abs_sub (-((1 + H) * (R - (1 - u)))) ((H - A1) * (1 - u))
        linarith
    _ ≤ (1 + |A1| + M * Kp * δ + ε') * δ + (M * Kp * δ + ε') + M * δ + (M * Kp * δ + M * δ + ε') := by
        rw [abs_neg]; linarith
    _ ≤ Q * δ + 2 * ε' := by
        have : (1 + |A1| + M * Kp * δ + ε') * δ ≤ (2 + |A1| + M * Kp) * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ0; linarith
        rw [hQdef]; linarith
    _ ≤ ε := by rw [hε']; linarith

theorem itemS08 : ItemS08 := by
  intro b hb etas hetas ulo ε hulo hε
  have key : ∀ l : List StepFn, (∀ e ∈ l, StepOK e) → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ e ∈ l, ∀ q : ℕ, q.Prime →
      x ^ ulo ≤ (q : ℝ) → (q : ℝ) < Real.sqrt x →
        |lamA b e x 1 + lamA b e x q - gEta e (Real.log q / Real.log (Real.sqrt x))| ≤ ε := by
    intro l
    induction l with
    | nil => intro _; exact ⟨0, fun x _ e he => absurd he (List.not_mem_nil)⟩
    | cons e l ih =>
      intro hl
      obtain ⟨x1, hx1⟩ := ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
      obtain ⟨x2, hx2⟩ := s08_single b hb e (hl e List.mem_cons_self) ulo ε hulo hε
      refine ⟨max x1 x2, fun x hx e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | h
      · exact hx2 x (le_trans (le_max_right _ _) hx)
      · exact hx1 x (le_trans (le_max_left _ _) hx) e' h
  exact key etas hetas

end Omega3
