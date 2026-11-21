import Palprimes.Sieve.Bounds

/-! # Per-interval bounds and the final sieve inequality (M13) -/

open Finset Real

namespace Palprimes

/-- `Z_c(x) = ⌈x^{1/20}⌉`. -/
noncomputable def Zc (x : ℝ) : ℕ := ⌈x ^ ((1 : ℝ) / 20)⌉₊

theorem tendsto_Zc : Filter.Tendsto Zc Filter.atTop Filter.atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop (by norm_num))

theorem Zc_le (x : ℝ) (hx : 1 ≤ x) : (Zc x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 20) := by
  have h1 : 1 ≤ x ^ ((1 : ℝ) / 20) := Real.one_le_rpow hx (by norm_num)
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 20))
  unfold Zc; linarith

theorem Zc_sub_one_le (x : ℝ) (hx : 1 ≤ x) : (Zc x : ℝ) - 1 ≤ x ^ ((1 : ℝ) / 20) := by
  have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 20))
  unfold Zc; linarith

theorem ge_Zc_of_le (x : ℝ) (p : ℕ) (h : x ^ ((1 : ℝ) / 20) ≤ p) : Zc x ≤ p := Nat.ceil_le.2 h

/-- Eventually `c ≤ x^e` for `e > 0`. -/
theorem eventually_le_rpow (c e : ℝ) (he : 0 < e) : ∀ᶠ x : ℝ in Filter.atTop, c ≤ x ^ e :=
  (tendsto_rpow_atTop he).eventually (Filter.eventually_ge_atTop c)

/-- **Richert interval.** -/
theorem richert_interval (B : ℕ) (a b v m : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 23 / 100)
    (hv : 0 ≤ v) (hvb : v / 10 < 6 / 25 - b) (hm : 0 < m)
    (Hm : ∀ᶠ t : ℕ in Filter.atTop, ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      m ≤ (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ a < p → (p : ℝ) ≤ x ^ b →
      (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) /
          (p * selS (PB B (Zc x)) (x ^ ((6 : ℝ) / 25) / p)) ≤
        ((1 - a / (23 / 100)) / m) * (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p := by
  have H1 := tendsto_Zc.eventually Hm
  have H2 := eventually_le_rpow ((4 : ℝ) ^ v) (6 / 25 - b - v / 10) (by linarith)
  filter_upwards [H1, H2, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx p hp hpa hpb
  have hL : 0 < Real.log x := Real.log_pos hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set V := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  set S := selS (PB B (Zc x)) (x ^ ((6 : ℝ) / 25) / p)
  -- the level condition
  have hy : (((Zc x : ℕ) : ℝ) ^ v) ^ 2 ≤ x ^ ((6 : ℝ) / 25) / p := by
    have hz := Zc_le x hx.le
    have h0 : (0 : ℝ) ≤ (Zc x : ℝ) := Nat.cast_nonneg _
    calc (((Zc x : ℕ) : ℝ) ^ v) ^ 2 ≤ ((2 * x ^ ((1 : ℝ) / 20)) ^ v) ^ 2 :=
          pow_le_pow_left₀ (Real.rpow_nonneg h0 _) (Real.rpow_le_rpow h0 hz hv) 2
      _ = (4 : ℝ) ^ v * x ^ (v / 10) := by
          have hx0 : 0 < x := by linarith
          apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
          rw [Real.log_pow, Real.log_rpow (by positivity), Real.log_mul (by norm_num) (by positivity),
            Real.log_rpow hx0, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
            Real.log_rpow hx0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast; ring
      _ ≤ x ^ (6 / 25 - b - v / 10) * x ^ (v / 10) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = x ^ ((6 : ℝ) / 25) / x ^ b := by
          rw [← Real.rpow_add (by linarith), ← Real.rpow_sub (by linarith)]; congr 1; ring
      _ ≤ x ^ ((6 : ℝ) / 25) / p := div_le_div_of_nonneg_left (by positivity) hp0 hpb
  have hmS := h1 _ hy
  have hV := V_PB_pos B (Zc x)
  have hS : 0 < S := by
    by_contra hneg; push_neg at hneg
    have : V * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hV.le hneg
    linarith
  have hw : 1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100)) ≤ 1 - a / (23 / 100) := by
    have hlp : a * Real.log x < Real.log p := by
      rw [← Real.log_rpow (by linarith)]; exact Real.log_lt_log (by positivity) hpa
    rw [Real.log_rpow (by linarith)]
    have : a / (23 / 100) ≤ Real.log p / (23 / 100 * Real.log x) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  have hwa : 0 ≤ 1 - a / (23 / 100) := by
    have : a / (23 / 100) ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
    linarith
  have hinv : 1 / S ≤ V / m := by
    rw [div_le_div_iff₀ hS hm]; linarith
  calc (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) / (p * S)
      ≤ (1 - a / (23 / 100)) / (p * S) := div_le_div_of_nonneg_right hw (by positivity)
    _ = (1 - a / (23 / 100)) * (1 / S) / p := by field_simp
    _ ≤ (1 - a / (23 / 100)) * (V / m) / p := by
        apply div_le_div_of_nonneg_right _ hp0.le
        exact mul_le_mul_of_nonneg_left hinv hwa
    _ = _ := by ring

/-- The ratio `V(p)/V(Z_c)` for `x^a < p`, from two-sided Mertens 3. -/
theorem ratio_eventually (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (a θ : ℝ) (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, x ^ a < p →
      (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) ≤
        (1 / (20 * θ ^ 3 * a)) * (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) := by
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 (mertens_two_sided C₃ hC₃ B hB θ hθ0 hθ1)
  have H1 := eventually_le_rpow ((T₁ : ℝ) + 3) a ha
  have H2 := tendsto_Zc.eventually (Filter.eventually_ge_atTop (T₁ + 3))
  have H3 := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (Real.log 2 / ((1 - θ) * a)))
  filter_upwards [H1, H2, H3, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 hx p hp
  set e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  have hβ := betaB_pos B
  have hL : 0 < Real.log x := Real.log_pos hx
  have hpT : T₁ + 3 ≤ p := by
    have : ((T₁ + 3 : ℕ) : ℝ) < p := by push_cast; linarith
    exact_mod_cast this.le
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (le_trans (by omega) hpT)
  have hZ3 : (3 : ℝ) ≤ Zc x := by exact_mod_cast (le_trans (by omega) h2)
  have hMp := hT₁ p (by omega)
  have hMZ := hT₁ (Zc x) (by omega)
  set Vp := ∏ q ∈ PB B p, (1 - 1 / (q : ℝ))
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  have hlp1 : 0 < Real.log ((p : ℝ) - 1) := Real.log_pos (by linarith)
  have hlZ1 : 0 < Real.log ((Zc x : ℝ) - 1) := Real.log_pos (by linarith)
  -- `log(Z_c − 1) ≤ L/20`, `log(p − 1) ≥ θ a L`
  have hZlog : Real.log ((Zc x : ℝ) - 1) ≤ Real.log x / 20 := by
    have := Real.log_le_log (by linarith) (Zc_sub_one_le x hx.le)
    rw [Real.log_rpow (by linarith)] at this; linarith
  have hplog : θ * a * Real.log x ≤ Real.log ((p : ℝ) - 1) := by
    have h1' : Real.log ((p : ℝ) / 2) ≤ Real.log ((p : ℝ) - 1) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1'
    have h2' : a * Real.log x < Real.log p := by
      rw [← Real.log_rpow (by linarith)]; exact Real.log_lt_log (by positivity) hp
    have h3' : Real.log 2 ≤ (1 - θ) * a * Real.log x := by
      rw [div_le_iff₀ (by nlinarith)] at h3; linarith
    nlinarith
  -- `V(p) ≤ V(Z_c) log(Z_c − 1)/(θ² log(p − 1))`
  have hVp : Vp * betaB B * Real.log ((p : ℝ) - 1) ≤ e / θ := hMp.2
  have hVZ : θ * e ≤ VZ * betaB B * Real.log ((Zc x : ℝ) - 1) := hMZ.1
  have hVpZ : Vp ≤ VZ * Real.log ((Zc x : ℝ) - 1) / (θ ^ 2 * Real.log ((p : ℝ) - 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have hk1 : Vp * betaB B * Real.log ((p : ℝ) - 1) * θ ^ 2 ≤ θ * e := by
      have := mul_le_mul_of_nonneg_right hVp (by positivity : (0 : ℝ) ≤ θ ^ 2)
      calc _ ≤ e / θ * θ ^ 2 := this
        _ = θ * e := by field_simp
    have hk2 : θ * e ≤ VZ * Real.log ((Zc x : ℝ) - 1) * betaB B := by linarith
    have : Vp * (θ ^ 2 * Real.log ((p : ℝ) - 1)) * betaB B ≤ VZ * Real.log ((Zc x : ℝ) - 1) * betaB B := by
      nlinarith
    exact le_of_mul_le_mul_right this hβ
  have hVZ0 : 0 < VZ := V_PB_pos B (Zc x)
  have hfin : Vp ≤ (1 / (20 * θ ^ 3 * a)) * VZ := by
    refine le_trans hVpZ ?_
    rw [div_le_iff₀ (by positivity)]
    have : VZ * Real.log ((Zc x : ℝ) - 1) ≤ VZ * (Real.log x / 20) := mul_le_mul_of_nonneg_left hZlog hVZ0.le
    have h4 : 1 / (20 * θ ^ 3 * a) * VZ * (θ ^ 2 * (θ * a * Real.log x)) = VZ * (Real.log x / 20) := by
      field_simp
    have h5 : 1 / (20 * θ ^ 3 * a) * VZ * (θ ^ 2 * (θ * a * Real.log x)) ≤
        1 / (20 * θ ^ 3 * a) * VZ * (θ ^ 2 * Real.log ((p : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hplog (by positivity)
    linarith
  exact hfin

/-- The level condition `p^{2v} ≤ x^{6/25}/p` for `p ≤ x^b`, `(2v + 1) b ≤ 6/25`. -/
theorem level_cond (x : ℝ) (hx : 1 ≤ x) (p : ℕ) (hp : 1 ≤ p) (b v : ℝ) (hv : 0 ≤ v)
    (hpb : (p : ℝ) ≤ x ^ b) (hb : 0 ≤ b) (hvb : (2 * v + 1) * b ≤ 6 / 25) :
    (((p : ℕ) : ℝ) ^ v) ^ 2 ≤ x ^ ((6 : ℝ) / 25) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hp0]
  have e : (((p : ℕ) : ℝ) ^ v) ^ 2 * p = (p : ℝ) ^ (2 * v + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.rpow_add hp0, Real.rpow_one]; push_cast; ring_nf
  rw [e]
  calc (p : ℝ) ^ (2 * v + 1) ≤ (x ^ b) ^ (2 * v + 1) := Real.rpow_le_rpow hp0.le hpb (by linarith)
    _ = x ^ (b * (2 * v + 1)) := by rw [← Real.rpow_mul (by linarith)]
    _ ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- **Buchstab interval.** -/
theorem buchstab_interval (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (a b v m θ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hv : 0 ≤ v)
    (hvb : (2 * v + 1) * b ≤ 6 / 25) (hm : 0 < m) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (Hm : ∀ᶠ t : ℕ in Filter.atTop, ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      m ≤ (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → x ^ a < p → (p : ℝ) ≤ x ^ b →
      1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p ≤
        ((1 / (20 * θ ^ 3 * a)) * (1 / m - 1)) * (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 Hm
  have H1 := eventually_le_rpow (T₀ : ℝ) a ha
  filter_upwards [H1, ratio_eventually C₃ hC₃ B hB a θ ha hθ0 hθ1,
    Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx p hp hpa hpb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpT : T₀ ≤ p := by exact_mod_cast (le_trans h1 hpa.le)
  set Vp := ∏ q ∈ PB B p, (1 - 1 / (q : ℝ))
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  set S := selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)
  have hb0 : 0 ≤ b := by linarith
  have hy := level_cond x hx.le p hp.pos b v hv hpb hb0 hvb
  have hmS := hT₀ p hpT _ hy
  have hVp := V_PB_pos B p
  have hS1 := V_mul_selS_le_one B p (x ^ ((6 : ℝ) / 25) / p)
  have hS : 0 < S := by
    by_contra hneg; push_neg at hneg
    have : Vp * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hVp.le hneg
    linarith
  have hm1 : 0 ≤ 1 / m - 1 := by
    have : m ≤ 1 := le_trans hmS hS1
    rw [sub_nonneg, le_div_iff₀ hm]; linarith
  have hF : 1 / (Vp * S) ≤ 1 / m := one_div_le_one_div_of_le hm hmS
  have hratio := h2 p hpa
  have e : 1 / (p * S) - Vp / p = Vp * (1 / (Vp * S) - 1) / p := by
    have h1 : Vp ≠ 0 := hVp.ne'; have h2 : S ≠ 0 := hS.ne'; have h3 : (p : ℝ) ≠ 0 := hp0.ne'; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hp0.le
  calc Vp * (1 / (Vp * S) - 1) ≤ Vp * (1 / m - 1) := mul_le_mul_of_nonneg_left (by linarith) hVp.le
    _ ≤ (1 / (20 * θ ^ 3 * a)) * VZ * (1 / m - 1) := mul_le_mul_of_nonneg_right hratio hm1
    _ = _ := by ring

/-- `W(x) = ⌊log x / 8⌋` (start of the Buchstab range). -/
noncomputable def Wc (x : ℝ) : ℕ := ⌊Real.log x / 8⌋₊

theorem tendsto_Wc : Filter.Tendsto Wc Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by norm_num))

theorem mul_exp_neg_le (α s : ℝ) (hα : 0 < α) : s * Real.exp (-(α * s)) ≤ 1 / (α * Real.exp 1) := by
  have h := Real.add_one_le_exp (α * s - 1)
  rw [Real.exp_sub] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 0 < Real.exp (α * s) := Real.exp_pos _
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  rw [sub_add_cancel, le_div_iff₀ he] at h
  calc s * (Real.exp (α * s))⁻¹ * (α * Real.exp 1) = (α * s * Real.exp 1) * (Real.exp (α * s))⁻¹ := by ring
    _ ≤ Real.exp (α * s) * (Real.exp (α * s))⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    _ = 1 := by field_simp

/-- `s² e^{−0.12 s} ≤ 1/25` for `s ≥ 200`. -/
theorem sq_exp_small (s : ℝ) (hs : 200 ≤ s) : s ^ 2 * Real.exp (-(3 / 25 * s)) ≤ 1 / 25 := by
  have h1 := mul_exp_neg_le (3 / 100) s (by norm_num)
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h1' : s * Real.exp (-(3 / 100 * s)) ≤ 1000 / 81 := by
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h12 : (4147 : ℝ) ≤ Real.exp 12 := by
    have := Real.pow_div_factorial_le_exp (12 : ℝ) (by norm_num) 6
    norm_num [Nat.factorial] at this; linarith
  have h2 : Real.exp (-(3 / 50 * s)) ≤ 1 / 4147 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    calc (4147 : ℝ) ≤ Real.exp 12 := h12
      _ ≤ Real.exp (3 / 50 * s) := Real.exp_le_exp.2 (by linarith)
  have e : s ^ 2 * Real.exp (-(3 / 25 * s)) =
      (s * Real.exp (-(3 / 100 * s))) ^ 2 * Real.exp (-(3 / 50 * s)) := by
    rw [mul_pow, ← Real.exp_natCast_mul]; rw [mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
  rw [e]
  have h0 : 0 ≤ s * Real.exp (-(3 / 100 * s)) := by positivity
  calc (s * Real.exp (-(3 / 100 * s))) ^ 2 * Real.exp (-(3 / 50 * s)) ≤ (1000 / 81) ^ 2 * (1 / 4147) :=
        mul_le_mul (pow_le_pow_left₀ h0 h1' 2) h2 (by positivity) (by positivity)
    _ ≤ 1 / 25 := by norm_num

theorem exp_two02_le : Real.exp (2 * (1 + 1 / 100)) ≤ 8 := by
  have h1 : Real.exp (2 * (1 + 1 / 100)) = Real.exp 1 ^ 2 * Real.exp (1 / 50) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.exp (1 / 50) ≤ 50 / 49 := by
    have := Real.add_one_le_exp (-(1 / 50 : ℝ))
    rw [Real.exp_neg] at this
    have hp : 0 < Real.exp (1 / 50) := Real.exp_pos _
    rw [le_inv_comm₀ (by norm_num) hp] at this
    linarith [this]
  rw [h1]
  have : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 2
  nlinarith [Real.exp_pos (1 / 50 : ℝ)]

theorem log_three_ge_one : 1 ≤ Real.log 3 := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num)))

/-- `τ = 3^{−v} e^{2(1 + 1/100)} ≤ 16 e^{−3s/25}` for `v = 3s/25 − 1/2 ≥ 0`. -/
theorem tau_tail_le (s v : ℝ) (hv : v = 3 / 25 * s - 1 / 2) (hv0 : 0 ≤ v) :
    (3 : ℝ) ^ (-v) * Real.exp (((3 : ℝ) - 1) * (1 + 1 / 100)) ≤ 16 * Real.exp (-(3 / 25 * s)) := by
  have h3v : (3 : ℝ) ^ (-v) ≤ 2 * Real.exp (-(3 / 25 * s)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h1' : Real.log 3 * -v ≤ -v := by nlinarith [log_three_ge_one]
    have hh : Real.exp (1 / 2) ≤ 2 := by
      have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    calc Real.exp (Real.log 3 * -v) ≤ Real.exp (-v) := Real.exp_le_exp.2 h1'
      _ = Real.exp (1 / 2) * Real.exp (-(3 / 25 * s)) := by rw [← Real.exp_add, hv]; congr 1; ring
      _ ≤ 2 * Real.exp (-(3 / 25 * s)) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
  have h8 : Real.exp (((3 : ℝ) - 1) * (1 + 1 / 100)) ≤ 8 := by
    have := exp_two02_le; norm_num at this ⊢; linarith
  calc (3 : ℝ) ^ (-v) * Real.exp (((3 : ℝ) - 1) * (1 + 1 / 100)) ≤ (2 * Real.exp (-(3 / 25 * s))) * 8 :=
        mul_le_mul h3v h8 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Pointwise algebra of the tail. -/
theorem tail_pointwise (Vp VZ S s : ℝ) (hVp : 0 < Vp) (hVZ : 0 < VZ) (hs : 200 ≤ s)
    (hVS : 1 - 16 * Real.exp (-(3 / 25 * s)) ≤ Vp * S)
    (hratio : Vp ≤ VZ * s / (20 * (99 / 100) ^ 3)) :
    Vp * (1 / (Vp * S) - 1) ≤ 1 / 10 * (1 / s) * VZ := by
  set E := Real.exp (-(3 / 25 * s)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hτ' : 16 * E ≤ 1 / 2 := by
    have : E ≤ Real.exp (-24) := Real.exp_le_exp.2 (by linarith)
    have h24 : Real.exp (-24) ≤ 1 / 32 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by norm_num)
      have := Real.pow_div_factorial_le_exp (24 : ℝ) (by norm_num) 2
      norm_num [Nat.factorial] at this; linarith
    linarith
  have hVS0 : 0 < Vp * S := by linarith
  have hF : 1 / (Vp * S) - 1 ≤ 2 * (16 * E) := by
    rw [div_sub_one hVS0.ne', div_le_iff₀ hVS0]; nlinarith
  have hsq := sq_exp_small s hs
  have hs0 : 0 < s := by linarith
  have hsE : s * E ≤ (1 / 25) / s := by rw [le_div_iff₀ hs0]; nlinarith
  calc Vp * (1 / (Vp * S) - 1) ≤ Vp * (2 * (16 * E)) := mul_le_mul_of_nonneg_left hF hVp.le
    _ ≤ VZ * s / (20 * (99 / 100) ^ 3) * (2 * (16 * E)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = VZ * (32 / (20 * (99 / 100) ^ 3)) * (s * E) := by ring
    _ ≤ VZ * (32 / (20 * (99 / 100) ^ 3)) * ((1 / 25) / s) := mul_le_mul_of_nonneg_left hsE (by positivity)
    _ ≤ _ := by
        have h0 : 0 ≤ VZ * (1 / s) := by positivity
        have : VZ * (32 / (20 * (99 / 100) ^ 3)) * ((1 / 25) / s) =
            (32 / (20 * (99 / 100) ^ 3) * (1 / 25)) * (VZ * (1 / s)) := by ring
        rw [this]
        have hc : (32 / (20 * (99 / 100) ^ 3) * (1 / 25) : ℝ) ≤ 1 / 10 := by norm_num
        nlinarith

/-- The Mertens ratio in the tail: `V(p) ≤ V(Z_c) s / (20 θ³)`. -/
theorem ratio_tail (e β Vp VZ lp lp1 lZ1 L : ℝ) (he : 0 < e) (hβ : 0 < β) (hVZ : 0 < VZ)
    (hlp : 0 < lp) (hL : 0 < L)
    (hMp : Vp * β * lp1 ≤ e / (99 / 100)) (hMZ : 99 / 100 * e ≤ VZ * β * lZ1)
    (hlp1 : 99 / 100 * lp ≤ lp1) (hZ : lZ1 ≤ L / 20) (hVp : 0 < Vp) :
    Vp ≤ VZ * (L / lp) / (20 * (99 / 100) ^ 3) := by
  have k1 : Vp * β * (99 / 100 * lp) ≤ e / (99 / 100) :=
    le_trans (mul_le_mul_of_nonneg_left hlp1 (by positivity)) hMp
  have k2 : 99 / 100 * e ≤ VZ * β * (L / 20) :=
    le_trans hMZ (mul_le_mul_of_nonneg_left hZ (by positivity))
  rw [le_div_iff₀ (by norm_num), mul_div_assoc', le_div_iff₀ hlp]
  have k1' : Vp * β * lp * (99 / 100) ^ 2 ≤ e := by
    have := mul_le_mul_of_nonneg_right k1 (by norm_num : (0 : ℝ) ≤ 99 / 100)
    calc Vp * β * lp * (99 / 100) ^ 2 = Vp * β * (99 / 100 * lp) * (99 / 100) := by ring
      _ ≤ e / (99 / 100) * (99 / 100) := this
      _ = e := by field_simp
  have : Vp * (20 * (99 / 100) ^ 3) * lp * β ≤ VZ * L * β := by nlinarith
  exact le_of_mul_le_mul_right this hβ

/-- **Buchstab tail** `W ≤ p ≤ x^{1/200}`. -/
theorem buchstab_tail (c₁ : ℝ)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p : ℕ, p.Prime → Wc x ≤ p → (p : ℝ) ≤ x ^ ((1 : ℝ) / 200) →
      1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p ≤
        (1 / 10) * (Real.log p / Real.log x) * (∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) / p := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (rankin_unif c₁ hc₁ B (1 / 100) (by norm_num))
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 (mertens_two_sided C₃ hC₃ B hB (99 / 100) (by norm_num) (by norm_num))
  have H1 := tendsto_Wc.eventually (Filter.eventually_ge_atTop (T₀ + T₁ + ⌈Real.exp 70⌉₊ + 3))
  have H2 := tendsto_Zc.eventually (Filter.eventually_ge_atTop (T₁ + 3))
  filter_upwards [H1, H2, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx p hp hpW hpx
  set e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  have hβ := betaB_pos B
  have hL : 0 < Real.log x := Real.log_pos hx
  have hpbig : T₀ + T₁ + ⌈Real.exp 70⌉₊ + 3 ≤ p := le_trans h1 hpW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (le_trans (by omega) hpbig)
  have hpe : Real.exp 70 ≤ p := by
    have : (⌈Real.exp 70⌉₊ : ℝ) ≤ p := by exact_mod_cast (le_trans (by omega) hpbig)
    exact le_trans (Nat.le_ceil _) this
  have hlogp : 70 ≤ Real.log p := by
    rw [← Real.log_exp 70]; exact Real.log_le_log (Real.exp_pos _) hpe
  have hZ3 : (3 : ℝ) ≤ Zc x := by exact_mod_cast (le_trans (by omega) h2)
  set Vp := ∏ q ∈ PB B p, (1 - 1 / (q : ℝ))
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  set S := selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)
  have hVp := V_PB_pos B p
  have hVZ := V_PB_pos B (Zc x)
  -- `s = log x / log p ≥ 200`
  have hlpx : Real.log p ≤ Real.log x / 200 := by
    have := Real.log_le_log hp0 hpx
    rw [Real.log_rpow (by linarith)] at this; linarith
  set s := Real.log x / Real.log p
  have hlp0 : 0 < Real.log p := by linarith
  have hs : 200 ≤ s := by rw [le_div_iff₀ hlp0]; linarith
  -- Rankin with `k = 3`
  set v := Real.log (x ^ ((6 : ℝ) / 25) / p) / (2 * Real.log p)
  have hlogy : Real.log (x ^ ((6 : ℝ) / 25) / p) = 6 / 25 * Real.log x - Real.log p := by
    rw [Real.log_div (by positivity) hp0.ne', Real.log_rpow (by linarith)]
  have hv : v = 3 / 25 * s - 1 / 2 := by
    simp only [v, s]; rw [hlogy]; field_simp; ring
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hy : (((p : ℕ) : ℝ) ^ v) ^ 2 ≤ x ^ ((6 : ℝ) / 25) / p := by
    apply le_of_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    rw [show v * ((2 : ℕ) : ℝ) = Real.log (x ^ ((6 : ℝ) / 25) / p) / Real.log p by
      simp only [v]; push_cast; field_simp]
    rw [Real.rpow_def_of_pos hp0, mul_div_cancel₀ _ hlp0.ne', Real.exp_log (by positivity)]
  have hR := hT₀ p (by omega) 3 (by norm_num) v hv0 _ hy
  have hτ := tau_tail_le s v hv hv0
  have hVS : 1 - 16 * Real.exp (-(3 / 25 * s)) ≤ Vp * S := by
    have : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [this] at hR; linarith
  have hMp := (hT₁ p (by omega)).2
  have hMZ := (hT₁ (Zc x) (by omega)).1
  have hlp1 : 99 / 100 * Real.log p ≤ Real.log ((p : ℝ) - 1) := by
    have h1' : Real.log ((p : ℝ) / 2) ≤ Real.log ((p : ℝ) - 1) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1'
    linarith [Real.log_two_lt_d9]
  have hZlog : Real.log ((Zc x : ℝ) - 1) ≤ Real.log x / 20 := by
    have := Real.log_le_log (by linarith) (Zc_sub_one_le x hx.le)
    rw [Real.log_rpow (by linarith)] at this; linarith
  have hratio := ratio_tail e (betaB B) Vp VZ (Real.log p) (Real.log ((p : ℝ) - 1))
    (Real.log ((Zc x : ℝ) - 1)) (Real.log x) he hβ hVZ hlp0 hL hMp hMZ hlp1 hZlog hVp
  have hpt := tail_pointwise Vp VZ S s hVp hVZ hs hVS hratio
  have hS : 0 < S := by
    by_contra hneg; push_neg at hneg
    have : Vp * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hVp.le hneg
    have : (0 : ℝ) < 1 - 16 * Real.exp (-(3 / 25 * s)) := by
      have : Real.exp (-(3 / 25 * s)) ≤ Real.exp (-24) := Real.exp_le_exp.2 (by linarith)
      have h24 : Real.exp (-24) ≤ 1 / 32 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have := Real.pow_div_factorial_le_exp (24 : ℝ) (by norm_num) 2
        norm_num [Nat.factorial] at this; linarith
      linarith
    linarith
  have e2 : 1 / (p * S) - Vp / p = Vp * (1 / (Vp * S) - 1) / p := by
    have h1 : Vp ≠ 0 := hVp.ne'; have h2 : S ≠ 0 := hS.ne'; have h3 : (p : ℝ) ≠ 0 := hp0.ne'
    field_simp
  rw [e2]
  apply div_le_div_of_nonneg_right _ hp0.le
  have e3 : 1 / 10 * (1 / s) * VZ = 1 / 10 * (Real.log p / Real.log x) * VZ := by
    simp only [s]; field_simp
  rw [← e3]; exact hpt

end Palprimes
