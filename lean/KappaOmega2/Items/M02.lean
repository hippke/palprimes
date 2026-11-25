import KappaOmega2.Statements
import KappaOmega2.Items.M02_I

/-! # Item M02: Lemma A part 2, `Q(Λ^η) ≤ (c_η + ε)/G(√x)`. Proof plan in `KappaOmega2/Items/M02_PLAN.md`. -/

namespace KappaOmega2

open Finset Palprimes

set_option linter.style.longLine false

lemma m02_u0_le_one (e : StepFn) : m02u0 e ≤ 1 := by
  unfold m02u0
  have : ∀ l : List (ℚ × ℚ), (l.map (fun pr => (pr.1 : ℝ))).foldr min 1 ≤ 1 := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.foldr_cons]; exact le_trans (min_le_right _ _) ih
  exact this e

/-- The list with squared values. -/
def m02sq (e : StepFn) : StepFn := e.map (fun pr => (pr.1, pr.2 ^ 2))

lemma m02_eval_sq (e : StepFn) (u : ℝ) : StepFn.eval (m02sq e) u = StepFn.eval e u ^ 2 := by
  unfold StepFn.eval m02sq
  have key : ∀ (l : List (ℚ × ℚ)) (acc : ℝ),
      List.foldl (fun (acc : ℝ) (pr : ℚ × ℚ) => if (pr.1 : ℝ) ≤ u then ((pr.2 : ℚ) : ℝ) else acc) (acc ^ 2)
        (l.map (fun pr : ℚ × ℚ => (pr.1, pr.2 ^ 2))) =
      (List.foldl (fun (acc : ℝ) (pr : ℚ × ℚ) => if (pr.1 : ℝ) ≤ u then ((pr.2 : ℚ) : ℝ) else acc) acc l) ^ 2 := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [← ih]
      congr 1
      split_ifs <;> push_cast <;> ring
  have h := key e 0
  simpa using h

lemma m02_sq_pos (e : StepFn) (he : ∀ pr ∈ e, (0 : ℚ) < pr.1) : ∀ pr ∈ m02sq e, (0 : ℚ) < pr.1 := by
  intro pr hpr
  unfold m02sq at hpr
  obtain ⟨pr', hpr', rfl⟩ := List.mem_map.1 hpr
  exact he pr' hpr'

lemma m02_coef (M P Aa W : ℝ) (hM : 0 ≤ M) (hP : 0 ≤ P) (hA : 0 ≤ Aa) (hWd : W = (M + 1) * (P + 1) * (2 * Aa + P + 2)) :
    1 ≤ W ∧ M * P ≤ W ∧ P * P ≤ W ∧ P * M ≤ W ∧ P * (2 * Aa + P + 1) ≤ W ∧ P ≤ W ∧ 2 * Aa + P + 1 ≤ W := by
  have h1 : 1 ≤ (M + 1) * (P + 1) := by nlinarith
  have h2 : 1 ≤ 2 * Aa + P + 2 := by linarith
  have hW : (M + 1) * (P + 1) ≤ W := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (M + 1) * (P + 1)); rw [hWd]; linarith
  have hMP : M * P ≤ (M + 1) * (P + 1) := by nlinarith
  have hPP : P * (2 * Aa + P + 1) ≤ W := by
    have h3 : P ≤ (M + 1) * (P + 1) := by nlinarith
    have := mul_le_mul h3 (by linarith : 2 * Aa + P + 1 ≤ 2 * Aa + P + 2) (by linarith) (by positivity)
    rw [hWd]; linarith
  have hP2 : P * P ≤ W := by
    have : P * P ≤ P * (2 * Aa + P + 1) := mul_le_mul_of_nonneg_left (by linarith) hP
    linarith
  have hA2 : 2 * Aa + P + 1 ≤ W := by
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 2 * Aa + P + 2)
    rw [hWd]; linarith
  refine ⟨by linarith, by linarith, hP2, by linarith [mul_comm P M], hPP, by nlinarith, hA2⟩

set_option maxHeartbeats 8000000 in
/-- M02 for one step function. -/
theorem m02_single (b : ℕ) (hb : 2 ≤ b) (e : StepFn) (he : StepOK e) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, Qform b x (lamA b e x) ≤ (cEta e + ε) / GS b (Real.sqrt x) := by
  classical
  have he' : ∀ pr ∈ e, (0 : ℚ) < pr.1 := fun pr h => (he.2 pr h).1
  set M := m02Mv e with hMdef
  set u0 := m02u0 e with hu0def
  have hM0 : 0 ≤ M := m02_Mv_nonneg e
  have hu0 : 0 < u0 := m02_u0_pos e he'
  have hu01 : u0 ≤ 1 := m02_u0_le_one e
  obtain ⟨CG, hCG0, hCG⟩ := m02_G_asymp b hb
  set β := m02beta b with hβdef
  have hβ : 0 < β := m02_beta_pos b
  set Kp := Real.log (1 / u0) + 1 with hKpdef
  have hKp : 0 ≤ Kp := by
    have : 0 ≤ Real.log (1 / u0) := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
    linarith
  set P := M * Kp with hPdef
  have hP : 0 ≤ P := mul_nonneg hM0 hKp
  set A1 := Ahat e 1 with hA1
  set Aa := |A1| with hAa
  have hAa0 : 0 ≤ Aa := abs_nonneg _
  set W := (M + 1) * (P + 1) * (2 * Aa + P + 2) with hWdef
  obtain ⟨hW1, c1, c2, c3, c4, c5, c6⟩ := m02_coef M P Aa W hM0 hP hAa0 hWdef
  have hW0 : 0 < W := by linarith
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set ε' := ε₁ / (8 * W) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'W : W * ε' = ε₁ / 8 := by rw [hε']; field_simp
  have hε'1 : ε' ≤ 1 := by
    rw [hε', div_le_one (by positivity)]; linarith
  obtain ⟨KPS, hKPS⟩ := m02_PS e he' ε' hε'0
  obtain ⟨KPS2, hKPS2⟩ := m02_PS (m02sq e) (m02_sq_pos e he') ε' hε'0
  have hcontA : ContinuousOn (fun u => Ahat e (1 - u)) (Set.Icc 0 1) := by
    apply (m02_Ahat_cont e he').comp (continuousOn_const.sub continuousOn_id)
    intro u hu
    have h1 : (0 : ℝ) ≤ u := hu.1
    have h2 : u ≤ 1 := hu.2
    exact ⟨show (0 : ℝ) ≤ 1 - u by linarith, show 1 - u ≤ (1 : ℝ) by linarith⟩
  obtain ⟨KRS, hKRS⟩ := m02_RS e he' (fun u => Ahat e (1 - u)) hcontA ε' hε'0
  obtain ⟨Km, hKm⟩ := m02_mass e he'
  set Q := 16 * W with hQdef
  have hQ : 0 < Q := by positivity
  set Y0 : ℝ := (bigB b : ℝ) + 2 + 11 * Q / ε₁ with hY0
  have hY0p : 0 < Y0 := by positivity
  set GC : ℝ := max 1 (2 * Q * CG / ε₁) with hGC
  set K : ℝ := max (max (max KPS KPS2) (max KRS Km)) (max (Real.log Y0 / u0) (max ((GC + CG) / β) 1)) with hK
  refine ⟨Real.exp (2 * K), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set z := Real.sqrt x with hzdef
  set L := Real.log z with hLdef
  have hlogx : Real.log x = 2 * L := by rw [hLdef, hzdef, Real.log_sqrt hx0.le]; ring
  have hLK : K ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rw [Real.log_exp] at this; linarith
  have hK1 : max (max KPS KPS2) (max KRS Km) ≤ L := le_trans (le_max_left _ _) hLK
  have hK2 : max (Real.log Y0 / u0) (max ((GC + CG) / β) 1) ≤ L := le_trans (le_max_right _ _) hLK
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK2
  have hz0 : 0 < z := Real.sqrt_pos.2 hx0
  have hz1 : 1 < z := (Real.log_pos_iff hz0.le).1 (by linarith)
  have hLPS : KPS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK1
  have hLPS2 : KPS2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK1
  have hLRS : KRS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK1
  have hLm : Km ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK1
  have hLY : Real.log Y0 / u0 ≤ L := le_trans (le_max_left _ _) hK2
  have hLG : (GC + CG) / β ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK2
  -- `G`
  set G := GS b z with hGdef
  have hGz := hCG z hz1.le
  rw [abs_le] at hGz
  have hGGC : GC ≤ G := by
    rw [div_le_iff₀ hβ] at hLG; linarith [hGz.1]
  have hG1 : 1 ≤ G := le_trans (le_max_left _ _) hGGC
  have hG0 : 0 < G := by linarith
  have hGC2 : 2 * CG / G ≤ ε₁ / Q := by
    rw [div_le_div_iff₀ hG0 hQ]
    have : 2 * Q * CG / ε₁ ≤ G := le_trans (le_max_right _ _) hGGC
    rw [div_le_iff₀ hε₁0] at this
    linarith
  -- `Y = z^{u₀}` and `T`
  set Y := Real.exp (u0 * L) with hYdef
  have hYY0 : Y0 ≤ Y := by
    rw [div_le_iff₀ hu0] at hLY
    rw [hYdef, ← Real.exp_log hY0p]
    exact Real.exp_le_exp.2 (by linarith)
  have hY2 : (bigB b : ℝ) + 2 ≤ Y := by
    have : 0 ≤ 11 * Q / ε₁ := by positivity
    linarith
  have hY1 : 1 < Y := by have := (Nat.cast_nonneg (bigB b) : (0 : ℝ) ≤ _); linarith
  set T := 1 / (Y - 1) with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; apply div_nonneg zero_le_one; linarith
  have hT : 11 * T ≤ ε₁ / Q := by
    rw [hTdef]
    have h1 : 11 * Q / ε₁ ≤ Y - 1 := by have := (Nat.cast_nonneg (bigB b) : (0 : ℝ) ≤ _); linarith
    have h2 : 0 < 11 * Q / ε₁ := by positivity
    rw [div_le_iff₀ hε₁0] at h1
    rw [mul_one_div, div_le_div_iff₀ (by linarith) hQ]
    linarith
  have hT1 : T ≤ 1 := by rw [hTdef, div_le_one (by linarith)]; linarith
  have hbig : ∀ p : ℕ, p.Prime → Y ≤ p → Nat.Coprime p (bigB b) ∧ gS b p ≤ T := by
    intro p hp hpY
    refine ⟨?_, m02_gS_le b p hp Y hY1 hpY⟩
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hB0 : 0 < bigB b := Nat.pos_of_ne_zero (m02_bigB_ne_zero b hb)
    have := Nat.le_of_dvd hB0 hdvd
    have : (p : ℝ) ≤ bigB b := by exact_mod_cast this
    linarith
  have hpY : ∀ p ∈ m02Pz z, StepFn.eval e (m02u z p) ≠ 0 → Y ≤ p := by
    intro p hp hne
    have h1 : u0 ≤ m02u z p := by
      by_contra hcon; push_neg at hcon; exact hne (m02_eval_zero e _ hcon)
    unfold m02u at h1
    rw [le_div_iff₀ (by linarith)] at h1
    have hp0 : (0 : ℝ) < p := by
      unfold m02Pz at hp; rw [Finset.mem_filter] at hp; exact_mod_cast hp.2.pos
    rw [hYdef, ← Real.exp_log hp0]
    exact Real.exp_le_exp.2 (by linarith)
  have hPprime : ∀ p ∈ m02Pz z, p.Prime := fun p hp => by unfold m02Pz at hp; exact (Finset.mem_filter.1 hp).2
  have hPne : ∀ p ∈ m02Pz z, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (hPprime p hp).ne_zero
  -- `δ`
  set δ := 11 * T + 2 * CG / G with hδdef
  have hδQ : δ ≤ 2 * ε₁ / Q := by
    have : δ ≤ ε₁ / Q + ε₁ / Q := by linarith
    linarith [show ε₁ / Q + ε₁ / Q = 2 * ε₁ / Q by ring]
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ 2 * CG / G := by positivity
    linarith
  have hWδ : W * δ ≤ ε₁ / 8 := by
    have := mul_le_mul_of_nonneg_left hδQ hW0.le
    have e2 : W * (2 * ε₁ / Q) = ε₁ / 8 := by rw [hQdef]; field_simp; ring
    linarith
  have hδ1 : δ ≤ 1 := by
    have : W * δ ≤ 1 / 8 := by linarith
    have := mul_le_mul_of_nonneg_right hW1 hδ0
    linarith
  -- ratios
  have hRp : ∀ p ∈ m02Pz z, StepFn.eval e (m02u z p) ≠ 0 →
      |(p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0| ≤ δ := by
    intro p hp hne
    obtain ⟨hpB, hTp⟩ := hbig p (hPprime p hp) (hpY p hp hne)
    have h := m02_ratio b CG hCG z hz1 hG1 p (hPprime p hp).one_lt.le (3 * T)
      (m02_err_q b z hz0 p (hPprime p hp) hpB T hTp hT1)
    have : 3 * T ≤ 11 * T := by linarith
    unfold m02u; linarith
  have hRpq : ∀ q ∈ m02Pz z, StepFn.eval e (m02u z q) ≠ 0 → ∀ p ∈ (m02Pz z).erase q, StepFn.eval e (m02u z p) ≠ 0 →
      |((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - m02u z q - m02u z p) 0| ≤ δ := by
    intro q hq hneq p hp hne
    rw [Finset.mem_erase] at hp
    have hpp := hPprime p hp.2
    have hqq := hPprime q hq
    obtain ⟨hpB, hTp⟩ := hbig p hpp (hpY p hp.2 hne)
    obtain ⟨hqB, hTq⟩ := hbig q hqq (hpY q hq hneq)
    have h := m02_ratio b CG hCG z hz1 hG1 (p * q) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hpp.ne_zero hqq.ne_zero))
      (11 * T) (m02_err_pq b z hz0 p q hpp hqq hp.1 hpB hqB T hTp hTq hT1)
    have hl : 1 - Real.log ((p * q : ℕ) : ℝ) / Real.log z = 1 - m02u z q - m02u z p := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hqq.ne_zero), add_div]
      unfold m02u; ring
    rw [hl] at h
    push_cast at h
    linarith
  -- prime sums
  set S : ℝ → ℝ := fun s => ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * max (s - m02u z p) 0 with hSdef
  have hmass := hKm z hz1 hLm
  have hetaQ : ∀ p : ℕ, etaQ b e x p = StepFn.eval e (m02u z p) / G := fun p => rfl
  -- `W_q` against `S(1 − u_q)`
  have hWS : ∀ q ∈ m02Pz z, StepFn.eval e (m02u z q) ≠ 0 →
      |∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * (((p : ℝ) * q) * m02A b z (p * q) / G) -
        S (1 - m02u z q)| ≤ P * δ + M * δ := by
    intro q hq hneq
    set u := m02u z q with hudef
    have hu1 := m02_u_lt_one z hz1 q hq
    obtain ⟨hqB, hTq⟩ := hbig q (hPprime q hq) (hpY q hq hneq)
    have hsplit : S (1 - u) = (1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0 +
        ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * max (1 - u - m02u z p) 0 := by
      rw [hSdef]; simp only; rw [← Finset.add_sum_erase _ _ hq]
    have e1 : ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * (((p : ℝ) * q) * m02A b z (p * q) / G) -
        S (1 - u) = ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
          (((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - u - m02u z p) 0) -
          (1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0 := by
      rw [hsplit]
      have : ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
          (((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - u - m02u z p) 0) =
          ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * (((p : ℝ) * q) * m02A b z (p * q) / G) -
          ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * max (1 - u - m02u z p) 0 := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring
      rw [this]; ring
    rw [e1]
    have hA : |∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
        (((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - u - m02u z p) 0)| ≤ P * δ := by
      calc _ ≤ ∑ p ∈ (m02Pz z).erase q, |(1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
            (((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - u - m02u z p) 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)| * δ := by
            apply Finset.sum_le_sum; intro p hp
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p)]
            by_cases hne : StepFn.eval e (m02u z p) = 0
            · rw [hne]; simp
            · exact mul_le_mul_of_nonneg_left (hRpq q hq hneq p hp hne) (by positivity)
        _ = (∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)|) * δ := by rw [Finset.sum_mul]
        _ ≤ (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)|) * δ := by
            apply mul_le_mul_of_nonneg_right _ hδ0
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun p _ _ => by positivity)
        _ ≤ P * δ := mul_le_mul_of_nonneg_right hmass hδ0
    have hB : |(1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0| ≤ M * δ := by
      have hq1 : 1 / (q : ℝ) ≤ T := by
        refine le_trans ?_ hTq
        rw [m02_gS_prime b q (hPprime q hq) hqB]
        have : (1 : ℝ) < q := by exact_mod_cast (hPprime q hq).one_lt
        apply one_div_le_one_div_of_le (by linarith); linarith
      have hu0' : 0 < u := by
        rw [hudef]; unfold m02u
        exact div_pos (Real.log_pos (by exact_mod_cast (hPprime q hq).one_lt)) (by linarith)
      have hm1 : max (1 - u - u) 0 ≤ 1 := max_le (by linarith) zero_le_one
      have hm0 : 0 ≤ max (1 - u - u) 0 := le_max_right _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q), abs_of_nonneg hm0]
      have h1 := m02_eval_abs e u
      have hTδ : T ≤ δ := by
        have : 0 ≤ 2 * CG / G := by positivity
        linarith
      calc 1 / (q : ℝ) * |StepFn.eval e u| * max (1 - u - u) 0 ≤ T * M * 1 :=
            mul_le_mul (mul_le_mul hq1 h1 (abs_nonneg _) hT0) hm1 hm0 (by positivity)
        _ ≤ M * δ := by
            have := mul_le_mul_of_nonneg_left hTδ hM0
            linarith
    calc _ ≤ |∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
          (((p : ℝ) * q) * m02A b z (p * q) / G - max (1 - u - m02u z p) 0)| +
          |(1 / (q : ℝ)) * StepFn.eval e u * max (1 - u - u) 0| := abs_sub _ _
      _ ≤ _ := add_le_add hA hB
  -- the exact formula `Q G = 1 − H² + T₁ + T₂`
  set H := ∑ p ∈ m02Pz z, etaQ b e x p * m02A b z p with hHdef
  set T1 := ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) ^ 2 * ((p : ℝ) * m02A b z p / G) with hT1def
  set Wf : ℕ → ℝ := fun q => ∑ p ∈ (m02Pz z).erase q, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
      (((p : ℝ) * q) * m02A b z (p * q) / G) with hWfdef
  set T2 := ∑ q ∈ m02Pz z, (1 / (q : ℝ)) * StepFn.eval e (m02u z q) * Wf q with hT2def
  have hQG := m02_QG b e x hG0
  rw [← hzdef, m02_H b e x, ← hzdef] at hQG
  have hB0 : G * ∑ k ∈ ltSet z, gS b k * etaK b e x k ^ 2 = T1 + T2 := by
    have h1 : ∑ k ∈ ltSet z, gS b k * etaK b e x k ^ 2 =
        ∑ p ∈ m02Pz z, ∑ p' ∈ m02Pz z, etaQ b e x p * etaQ b e x p' * m02A2 b z p' p := by
      rw [← m02_B0 b z (etaQ b e x)]; rfl
    rw [h1, Finset.mul_sum, hT1def, hT2def, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hq, m02_A2_self, hWfdef]
    simp only
    rw [Finset.mul_sum]
    have hq0 := hPne q hq
    congr 1
    · rw [hetaQ q]; field_simp
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_erase] at hp
      rw [m02_A2_ne b z p q (hPprime p hp.2) (hPprime q hq) hp.1, hetaQ q, hetaQ p]
      have hp0 := hPne p hp.2
      field_simp
  rw [hB0] at hQG
  -- estimates
  have hS1 : |S 1 - A1| ≤ ε' := hKPS z hz1 hLPS 1 zero_le_one le_rfl
  have hHS : |H - S 1| ≤ P * δ := by
    have e1 : H - S 1 = ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
        ((p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0) := by
      rw [hHdef, hSdef]; simp only; rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro p hp
      have hp0 := hPne p hp
      rw [hetaQ]; field_simp
    rw [e1]
    calc _ ≤ ∑ p ∈ m02Pz z, |(1 / (p : ℝ)) * StepFn.eval e (m02u z p) *
          ((p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)| * δ := by
          apply Finset.sum_le_sum; intro p hp
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p)]
          by_cases hne : StepFn.eval e (m02u z p) = 0
          · rw [hne]; simp
          · exact mul_le_mul_of_nonneg_left (hRp p hp hne) (by positivity)
      _ = (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)|) * δ := by rw [Finset.sum_mul]
      _ ≤ P * δ := mul_le_mul_of_nonneg_right hmass hδ0
  have hH : |H - A1| ≤ P * δ + ε' := by
    calc |H - A1| ≤ |H - S 1| + |S 1 - A1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hHS hS1
  -- `T₁`
  set J1 := ∫ u in (0 : ℝ)..1, StepFn.eval e u ^ 2 * (1 - u) / u with hJ1
  have hT1J : |T1 - J1| ≤ M * P * δ + ε' := by
    have hPS2 := hKPS2 z hz1 hLPS2 1 zero_le_one le_rfl
    simp only [m02_eval_sq] at hPS2
    set S2 := ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) ^ 2 * max (1 - m02u z p) 0
    have hA : |T1 - S2| ≤ M * P * δ := by
      have e1 : T1 - S2 = ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) ^ 2 *
          ((p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0) := by
        rw [hT1def, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring
      rw [e1]
      calc _ ≤ ∑ p ∈ m02Pz z, |(1 / (p : ℝ)) * StepFn.eval e (m02u z p) ^ 2 *
            ((p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ m02Pz z, M * ((1 / (p : ℝ)) * |StepFn.eval e (m02u z p)|) * δ := by
            apply Finset.sum_le_sum; intro p hp
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p), abs_pow]
            by_cases hne : StepFn.eval e (m02u z p) = 0
            · rw [hne]; simp
            · have h1 := hRp p hp hne
              have h2 := m02_eval_abs e (m02u z p)
              have h3 : 0 ≤ |StepFn.eval e (m02u z p)| := abs_nonneg _
              have hpp : (0 : ℝ) ≤ 1 / p := by positivity
              calc 1 / (p : ℝ) * |StepFn.eval e (m02u z p)| ^ 2 * |(p : ℝ) * m02A b z p / G - max (1 - m02u z p) 0|
                  ≤ 1 / (p : ℝ) * (M * |StepFn.eval e (m02u z p)|) * δ := by
                    apply mul_le_mul _ h1 (abs_nonneg _) (by positivity)
                    apply mul_le_mul_of_nonneg_left _ hpp
                    rw [sq]; exact mul_le_mul_of_nonneg_right h2 h3
                _ = M * (1 / (p : ℝ) * |StepFn.eval e (m02u z p)|) * δ := by ring
        _ = M * (∑ p ∈ m02Pz z, (1 / (p : ℝ)) * |StepFn.eval e (m02u z p)|) * δ := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ ≤ M * P * δ := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hM0) hδ0
    have hB : |S2 - J1| ≤ ε' := by
      have hI : ∫ v in (0 : ℝ)..1, StepFn.eval e v ^ 2 * (1 - v) / v = J1 := rfl
      rw [← hI]; exact hPS2
    calc |T1 - J1| ≤ |T1 - S2| + |S2 - J1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hA hB
  -- `T₂`
  set J2 := ∫ u in (0 : ℝ)..1, StepFn.eval e u * Ahat e (1 - u) / u with hJ2
  have hT2J : |T2 - J2| ≤ P * (P * δ + M * δ + ε') + ε' := by
    have hRS := hKRS z hz1 hLRS
    set R2 := ∑ p ∈ m02Pz z, (1 / (p : ℝ)) * StepFn.eval e (m02u z p) * Ahat e (1 - m02u z p)
    have hA : |T2 - R2| ≤ P * (P * δ + M * δ + ε') := by
      have e1 : T2 - R2 = ∑ q ∈ m02Pz z, (1 / (q : ℝ)) * StepFn.eval e (m02u z q) * (Wf q - Ahat e (1 - m02u z q)) := by
        rw [hT2def, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; ring
      rw [e1]
      calc _ ≤ ∑ q ∈ m02Pz z, |(1 / (q : ℝ)) * StepFn.eval e (m02u z q) * (Wf q - Ahat e (1 - m02u z q))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ m02Pz z, (1 / (q : ℝ)) * |StepFn.eval e (m02u z q)| * (P * δ + M * δ + ε') := by
            apply Finset.sum_le_sum; intro q hq
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / q)]
            by_cases hne : StepFn.eval e (m02u z q) = 0
            · rw [hne]; simp
            · apply mul_le_mul_of_nonneg_left _ (by positivity)
              have h1 := hWS q hq hne
              have hu1 := m02_u_lt_one z hz1 q hq
              have hu0' : 0 ≤ m02u z q := by
                unfold m02u; exact div_nonneg (Real.log_natCast_nonneg _) (by linarith)
              have h2 := hKPS z hz1 hLPS (1 - m02u z q) (by linarith) (by linarith)
              have h3 : Wf q - Ahat e (1 - m02u z q) =
                  (Wf q - S (1 - m02u z q)) + (S (1 - m02u z q) - Ahat e (1 - m02u z q)) := by ring
              rw [h3]
              have h4 : |S (1 - m02u z q) - Ahat e (1 - m02u z q)| ≤ ε' := h2
              calc _ ≤ |Wf q - S (1 - m02u z q)| + |S (1 - m02u z q) - Ahat e (1 - m02u z q)| := abs_add_le _ _
                _ ≤ (P * δ + M * δ) + ε' := add_le_add h1 h4
                _ = _ := by ring
        _ = (∑ q ∈ m02Pz z, (1 / (q : ℝ)) * |StepFn.eval e (m02u z q)|) * (P * δ + M * δ + ε') := by rw [Finset.sum_mul]
        _ ≤ P * (P * δ + M * δ + ε') := mul_le_mul_of_nonneg_right hmass (by positivity)
    calc |T2 - J2| ≤ |T2 - R2| + |R2 - J2| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hA hRS
  -- conclusion
  have hcE := m02_cEta e he'
  rw [← hJ1, ← hJ2, ← hA1] at hcE
  have hHH : |H ^ 2 - A1 ^ 2| ≤ (P * δ + ε') * (2 * Aa + P + 1) := by
    have : H ^ 2 - A1 ^ 2 = (H - A1) * (H + A1) := by ring
    rw [this, abs_mul]
    apply mul_le_mul hH _ (abs_nonneg _) (by positivity)
    have : |H + A1| ≤ |H - A1| + 2 * |A1| := by
      have := abs_add_le (H - A1) (2 * A1)
      rw [show H - A1 + 2 * A1 = H + A1 by ring, abs_mul, abs_two] at this; exact this
    have hPδ : P * δ ≤ P := mul_le_of_le_one_right hP hδ1
    linarith
  have hfin : Qform b x (lamA b e x) * G ≤ cEta e + ε₁ := by
    rw [hQG, hcE]
    have h1 := (abs_le.1 hT1J).2
    have h2 := (abs_le.1 hT2J).2
    have h3 := (abs_le.1 hHH).1
    have d1 := mul_le_mul_of_nonneg_right c1 hδ0
    have d2 := mul_le_mul_of_nonneg_right c2 hδ0
    have d3 := mul_le_mul_of_nonneg_right c3 hδ0
    have d4 := mul_le_mul_of_nonneg_right c4 hδ0
    have d5 := mul_le_mul_of_nonneg_right c5 hε'0.le
    have d6 := mul_le_mul_of_nonneg_right c6 hε'0.le
    have hε'8 : ε' ≤ ε₁ / 8 := by have := mul_le_mul_of_nonneg_right hW1 hε'0.le; linarith
    have e3 : (P * δ + ε') * (2 * Aa + P + 1) = P * (2 * Aa + P + 1) * δ + (2 * Aa + P + 1) * ε' := by ring
    have e2 : P * (P * δ + M * δ + ε') = P * P * δ + P * M * δ + P * ε' := by ring
    rw [e3] at h3
    rw [e2] at h2
    linarith
  have hfin' : Qform b x (lamA b e x) * G ≤ cEta e + ε := by linarith
  rw [le_div_iff₀ hG0]; exact hfin'

theorem itemM02 : ItemM02 := by
  intro b hb etas hetas ε hε
  have key : ∀ l : List StepFn, (∀ e ∈ l, StepOK e) → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ e ∈ l,
      Qform b x (lamA b e x) ≤ (cEta e + ε) / GS b (Real.sqrt x) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨0, fun x _ e he => absurd he (List.not_mem_nil)⟩
    | cons e l ih =>
      intro hl
      obtain ⟨x1, hx1⟩ := ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
      obtain ⟨x2, hx2⟩ := m02_single b hb e (hl e List.mem_cons_self) ε hε
      refine ⟨max x1 x2, fun x hx e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | h
      · exact hx2 x (le_trans (le_max_right _ _) hx)
      · exact hx1 x (le_trans (le_max_left _ _) hx) e' h
  exact key etas hetas

end KappaOmega2
