import Palprimes.TL1.Asymp

/-! # Level of distribution `θ` from TL¹

`level_explicit_gen` is `level_explicit` with the Farey total as a hypothesis. `farey_split` bounds
the Farey total up to `D ≤ x^θ`: below `x^{6/25}` by `farey_total_le`, above by TL¹ on dyadic blocks. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- `inner_le` with an abstract Farey total. -/
theorem inner_le_gen (b : ℕ) (hb : 2 ≤ b) (N D : ℕ) (hN : 1 ≤ N) (Kt : ℝ)
    (hF : ∀ k : ℤ, ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) ≤ Kt)
    (r h1 : ℕ) (hr : r ∈ (bigB b).divisors) :
    ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
          ∑ h2 ∈ Ico 1 q, ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ ≤
      (∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * Kt) := by
  classical
  have hrB : r ∣ bigB b := Nat.dvd_of_mem_divisors hr
  have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (h1 : ℝ) / r = (k : ℝ) / (bigB b : ℝ) :=
    ⟨_, div_eq_k b r h1 hb hrB hr0⟩
  have hreg := regroup D (bigB b) (fun t => ‖Ssum b N ((h1 : ℝ) / r + t)‖) (fun t => norm_nonneg _)
  refine le_trans hreg ?_
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k := by
    apply Finset.sum_nonneg; intro i _; positivity
  apply mul_le_mul_of_nonneg_left _ hH0
  have hb0 : (0 : ℝ) ≤ (b : ℝ) ^ (N + 1) := by positivity
  calc _ ≤ ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, (b : ℝ) ^ (N + 1) * Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) := by
        apply Finset.sum_le_sum; intro q _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro h _
        have e : (h1 : ℝ) / r + (h : ℝ) / q = (h : ℝ) / q + (k : ℝ) / (bigB b : ℝ) := by
          rw [hk, add_comm]
        show ‖Ssum b N ((h1 : ℝ) / r + (h : ℝ) / q)‖ ≤ _
        rw [e]
        exact Ssum_le b N hb hN _
    _ = (b : ℝ) ^ (N + 1) * ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
        rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF k) hb0

/-- `level_explicit` with an abstract Farey total. -/
theorem level_explicit_gen (b : ℕ) (hb : 2 ≤ b) (N D : ℕ) (hN : 1 ≤ N) (Kt : ℝ)
    (hF : ∀ k : ℤ, ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) ≤ Kt) :
    ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
          |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| ≤
      (∑ r ∈ (bigB b).divisors, (r : ℝ)) *
        ((∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * Kt)) := by
  classical
  set Q1 := (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b))
  set R := (∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * Kt)
  calc _ ≤ ∑ q ∈ Q1, ∑ r ∈ (bigB b).divisors, ∑ h1 ∈ range r,
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
          ∑ h2 ∈ Ico 1 q, ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
        apply Finset.sum_le_sum; intro q hq
        have hq0 : 0 < q := by simp only [Q1, mem_filter, mem_Icc] at hq; omega
        have h := level_err_le b N q hb hq0
        have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q := by positivity
        refine le_trans (mul_le_mul_of_nonneg_left h h3) (le_of_eq ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro h1 _
        ring
    _ = ∑ r ∈ (bigB b).divisors, ∑ h1 ∈ range r, ∑ q ∈ Q1,
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
          ∑ h2 ∈ Ico 1 q, ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r _
        rw [Finset.sum_comm]
    _ ≤ ∑ r ∈ (bigB b).divisors, ∑ h1 ∈ range r, R := by
        apply Finset.sum_le_sum; intro r hr
        apply Finset.sum_le_sum; intro h1 _
        exact inner_le_gen b hb N D hN Kt hF r h1 hr
    _ = _ := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem dvd_bigB (b : ℕ) (_hb : 1 ≤ b) : b ∣ bigB b := by
  unfold bigB
  have : b ^ 3 - b = b * (b ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ']
  rw [this]; exact Dvd.intro _ rfl

/-- **The Farey total above `D₁`**: TL¹ on dyadic blocks. -/
theorem farey_high (b : ℕ) (hb : 2 ≤ b) (N D D1 : ℕ) (θ κ δw Cw : ℝ) (hδw0 : 0 ≤ δw) (hCw0 : 0 ≤ Cw)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ δw)
    (hD : (D : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ)
    (hD1 : 2 * ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ D1 + 1)
    (hTL : ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 → (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ))
    (k : ℤ) :
    ∑ q ∈ ((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter (fun q => D1 < q),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) ≤
      (Nat.log 2 D : ℝ) * (Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw * ((b : ℝ) ^ N) ^ (-κ)) := by
  classical
  set A := ((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter (fun q => D1 < q) with hA
  have hmaps : ∀ q ∈ A, Nat.log 2 q ∈ Icc 1 (Nat.log 2 D) := by
    intro q hq
    simp only [hA, mem_filter, mem_Icc] at hq
    rw [mem_Icc]
    exact ⟨Nat.log_pos (by norm_num) hq.1.1.1, Nat.log_mono_right hq.1.1.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS0 : ∀ q, 0 ≤ ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) :=
    fun q => Finset.sum_nonneg (fun _ _ => Fprod_nonneg _ _ _)
  calc _ ≤ ∑ _i ∈ Icc 1 (Nat.log 2 D), Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw * ((b : ℝ) ^ N) ^ (-κ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [mem_Icc] at hi
        set Qs := A.filter (fun q => Nat.log 2 q = i) with hQs
        have hQ : ∀ q ∈ Qs, 2 ^ i ≤ q ∧ q ≤ 2 * 2 ^ i ∧ Nat.Coprime q b ∧ D1 < q ∧ q ≤ D := by
          intro q hq
          simp only [hQs, hA, mem_filter, mem_Icc] at hq
          obtain ⟨⟨⟨⟨h2, hqD⟩, hcop⟩, hD1q⟩, hlog⟩ := hq
          refine ⟨?_, ?_, Nat.Coprime.coprime_dvd_right (dvd_bigB b (by omega)) hcop, hD1q, hqD⟩
          · rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
          · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
            rw [hlog, pow_succ] at this; omega
        by_cases hne : Qs.Nonempty
        · obtain ⟨q0, hq0⟩ := hne
          have hR0 : (2 : ℝ) ^ i ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ := by
            have : (2 : ℝ) ^ i ≤ q0 := by exact_mod_cast (hQ q0 hq0).1
            have h2 : (q0 : ℝ) ≤ D := by exact_mod_cast (hQ q0 hq0).2.2.2.2
            linarith
          have hRY : ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by
            have h1 : ((D1 : ℝ) + 1) ≤ q0 := by exact_mod_cast (hQ q0 hq0).2.2.2.1
            have h2 : (q0 : ℝ) ≤ 2 * 2 ^ i := by exact_mod_cast (hQ q0 hq0).2.1
            push_cast; linarith
          have hTi := hTL (2 ^ i) hRY (by push_cast; exact hR0) Qs
            (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.1, (hQ q hq).2.2.1⟩) (k / (bigB b : ℝ))
          have hw : ∀ q ∈ Qs, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤
              Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw / 2 ^ i := by
            intro q hq
            have hq1 : 1 ≤ q := le_trans Nat.one_le_two_pow (hQ q hq).1
            have hqi : (2 : ℝ) ^ i ≤ q := by exact_mod_cast (hQ q hq).1
            have hq2 : (q : ℝ) ≤ 2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ := by
              have : (q : ℝ) ≤ 2 * 2 ^ i := by exact_mod_cast (hQ q hq).2.1
              linarith
            have hpos : (0 : ℝ) < 2 ^ i := by positivity
            calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤ Cw * (q : ℝ) ^ δw / q :=
                  div_le_div_of_nonneg_right (hCw q hq1) (by positivity)
              _ ≤ Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw / 2 ^ i := by
                  apply div_le_div₀ (by positivity) _ hpos hqi
                  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hq2 hδw0) hCw0
          calc ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
                ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ))
              ≤ ∑ q ∈ Qs, Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw / 2 ^ i *
                ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) :=
                Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hw q hq) (hS0 q))
            _ = Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw / 2 ^ i *
                ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) := by
                rw [Finset.mul_sum]
            _ ≤ Cw * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ δw / 2 ^ i * (((2 ^ i : ℕ) : ℝ) * ((b : ℝ) ^ N) ^ (-κ)) :=
                mul_le_mul_of_nonneg_left hTi (by positivity)
            _ = _ := by push_cast; field_simp
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne, Finset.sum_empty]; positivity
    _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-- `Y^{12/25} ≥ 2 Y^{47/100}` for `Y = b^N`, `N ≥ 100`. -/
theorem Y_gap (b N : ℕ) (hb : 2 ≤ b) (hN : 100 ≤ N) :
    2 * ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (6 / 25 : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hY0 : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  have h1 : ((b : ℝ) ^ N) ^ (2 : ℕ) ≤ (b : ℝ) ^ (2 * N + 1) := by
    rw [← pow_mul, mul_comm]; exact pow_le_pow_right₀ hb1 (by omega)
  have h2 : ((b : ℝ) ^ N) ^ (12 / 25 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ (6 / 25 : ℝ) := by
    calc ((b : ℝ) ^ N) ^ (12 / 25 : ℝ) = (((b : ℝ) ^ N) ^ (2 : ℕ)) ^ (6 / 25 : ℝ) := by
          rw [show ((b : ℝ) ^ N) ^ (2 : ℕ) = ((b : ℝ) ^ N) ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast _ 2).symm,
            ← Real.rpow_mul hY0.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h3 : (2 : ℝ) ≤ ((b : ℝ) ^ N) ^ (1 / 100 : ℝ) := by
    rw [show ((b : ℝ) ^ N) = (b : ℝ) ^ (N : ℝ) from (Real.rpow_natCast _ _).symm,
      ← Real.rpow_mul (by positivity)]
    calc (2 : ℝ) ≤ (b : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hb2
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (by
          have : (100 : ℝ) ≤ N := by exact_mod_cast hN
          linarith)
  have e : ((b : ℝ) ^ N) ^ (12 / 25 : ℝ) = ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) * ((b : ℝ) ^ N) ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hY0]; norm_num
  have h4 : 0 ≤ ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) := by positivity
  nlinarith


/-- The TL¹ error term after weights: `C (2x^θ)^{κ/2} Y^{-κ} ≤ 2bC (b^{-κ/2})^N`. -/
theorem E2_le (b N : ℕ) (hb : 2 ≤ b) (θ κ C : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1 / 2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hC : 0 ≤ C) :
    C * (2 * ((b : ℝ) ^ (2 * N + 1)) ^ θ) ^ (κ / 2) * ((b : ℝ) ^ N) ^ (-κ) ≤
      C * (2 * (b : ℝ)) * ((b : ℝ) ^ (-(κ / 2))) ^ N := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  set β := Real.log b with hβ
  have hβ0 : 0 ≤ β := Real.log_nonneg hb1
  have hx : ((b : ℝ) ^ (2 * N + 1)) ^ θ = Real.exp (θ * ((2 * N + 1) * β)) := by
    rw [rpow_eq_exp _ _ (by positivity), Real.log_pow, ← hβ]; push_cast; ring_nf
  have hY : ((b : ℝ) ^ N) ^ (-κ) = Real.exp (-κ * (N * β)) := by
    rw [rpow_eq_exp _ _ (by positivity), Real.log_pow]
  have hR : ((b : ℝ) ^ (-(κ / 2))) ^ N = Real.exp (-(κ / 2) * (N * β)) := by
    rw [rpow_eq_exp _ _ hb0, ← Real.exp_natCast_mul]; congr 1; ring
  have h2 : (2 : ℝ) ^ (κ / 2) ≤ 2 := by
    calc (2 : ℝ) ^ (κ / 2) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  rw [hx, hY, hR, Real.mul_rpow (by norm_num) (by positivity), ← Real.exp_mul]
  have hb' : (b : ℝ) = Real.exp β := (Real.exp_log hb0).symm
  have hexp : θ * ((2 * N + 1) * β) * (κ / 2) + -κ * (N * β) ≤ β + -(κ / 2) * (N * β) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have ht1 : θ * (κ / 2) ≤ 1 / 2 * (κ / 2) := mul_le_mul_of_nonneg_right hθ1.le (by positivity)
    have ht2 : θ * (κ / 2) ≤ 1 / 2 := by linarith only [ht1, hκ1]
    have key : θ * (κ / 2) * (2 * N + 1) ≤ 1 + (κ / 2) * N := by
      have h3 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ 2 * N)
      nlinarith only [h3, ht2]
    have := mul_le_mul_of_nonneg_right key hβ0
    nlinarith only [this]
  calc C * (2 ^ (κ / 2) * Real.exp (θ * ((2 * N + 1) * β) * (κ / 2))) * Real.exp (-κ * (N * β))
      ≤ C * (2 * Real.exp (θ * ((2 * N + 1) * β) * (κ / 2))) * Real.exp (-κ * (N * β)) := by
        gcongr
    _ = 2 * C * Real.exp (θ * ((2 * N + 1) * β) * (κ / 2) + -κ * (N * β)) := by
        rw [Real.exp_add]; ring
    _ ≤ 2 * C * Real.exp (β + -(κ / 2) * (N * β)) := by gcongr
    _ = _ := by rw [Real.exp_add, ← hb']; ring

set_option maxHeartbeats 4000000 in
/-- **Level `θ`** (weights `3^ω`, saving `log³x`) from TL¹ on `[x^{6/25}, x^θ]`. -/
theorem level_theta (b : ℕ) (hb : 2 ≤ b) (θ κ : ℝ) (hθ : 6 / 25 ≤ θ) (hθ1 : θ < 1 / 2) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1)
    (hTL : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, ((b : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ θ →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q b) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + β) ≤ R0 * ((b : ℝ) ^ N) ^ (-κ)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ q ∈ (Icc 1 ⌊((b : ℝ) ^ (2 * N + 1)) ^ θ⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  classical
  obtain ⟨NT, hNT⟩ := hTL
  obtain ⟨Cw, hCw⟩ := three_pow_omega_le_rpow (del0 b) (del0_pos b hb)
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow (del0 b) (del0_pos b hb)
  obtain ⟨Cw2, hCw2⟩ := three_pow_omega_le_rpow (κ / 2) (by positivity)
  have hCw0 : 0 ≤ Cw := by
    have := hCw 1 le_rfl
    simp [ArithmeticFunction.cardDistinctFactors_one] at this; linarith
  have hCw20 : 0 ≤ Cw2 := by
    have := hCw2 1 le_rfl
    simp [ArithmeticFunction.cardDistinctFactors_one] at this; linarith
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl
    simp at this; linarith
  obtain ⟨cA, hcA, N₁, hN₁⟩ := card_piStar_lower b hb
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set K0 : ℝ := Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150 with hK0
  have hK00 : 0 ≤ K0 := by
    have h1 : 0 ≤ 1 + 50 * Ce * b := by positivity
    have h2 : 0 ≤ 1 + 18 * Ce * b := by positivity
    have := mul_nonneg (mul_nonneg (mul_nonneg hCw0 h1) (by positivity : (0 : ℝ) ≤ 32 * (b : ℝ) ^ 2 + 12))
      (Real.exp_nonneg (5 * colC b))
    have := mul_nonneg (mul_nonneg (mul_nonneg hCw0 h2) (by positivity : (0 : ℝ) ≤ 32 * (b : ℝ) ^ 2 + 12))
      (pow_nonneg (Real.exp_nonneg (m0 b)) 150)
    linarith
  set SB : ℝ := ∑ r ∈ (bigB b).divisors, (r : ℝ) with hSB
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg (fun r _ => by positivity)
  set Lb : ℝ := 3 * (1 + Real.log b) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  set C : ℝ := SB * K0 * 2 * b * Lb ^ 7 with hC
  obtain ⟨n₀, hn₀⟩ := eventually_poly_geom C 18 (rhoL b) (rhoL_nonneg b) (rhoL_lt_one b hb) (cA / 2) (by positivity)
  set C2 : ℝ := SB * Cw2 * 4 * (b : ℝ) ^ 2 * Lb ^ 7 * 2 ^ 7 with hC2
  have hρ0 : (0 : ℝ) ≤ (b : ℝ) ^ (-(κ / 2)) := by positivity
  have hρ1 : (b : ℝ) ^ (-(κ / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb1 (by linarith)
  obtain ⟨n₂, hn₂⟩ := eventually_poly_geom C2 7 _ hρ0 hρ1 (cA / 2) (by positivity)
  refine ⟨max (max (max 2500 N₁) (n₀ ^ 2)) (max NT n₂), fun N hN => ?_⟩
  have hN2500 : 2500 ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hnn₀ : n₀ ≤ Nat.sqrt N := Nat.le_sqrt'.2 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hNTle : NT ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNn₂ : n₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  -- the moduli ranges
  set x : ℝ := (b : ℝ) ^ (2 * N + 1) with hx
  set Y : ℝ := (b : ℝ) ^ N with hY
  have hY0 : 0 < Y := by positivity
  have hY1 : 1 ≤ Y := one_le_pow₀ hb1.le
  have hx1 : 1 ≤ x := one_le_pow₀ hb1.le
  have hxr1 : 1 ≤ x ^ (6 / 25 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  set D1 : ℕ := ⌊x ^ (6 / 25 : ℝ)⌋₊ with hD1def
  have hD1 : (D1 : ℝ) ≤ x ^ ((6 : ℝ) / 25) := Nat.floor_le (by linarith)
  have hD11 : 1 ≤ D1 := Nat.le_floor (by simpa using hxr1)
  have hxθ : x ^ (6 / 25 : ℝ) ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_le hx1 hθ
  set D : ℕ := ⌊x ^ θ⌋₊ with hDdef
  have hD : (D : ℝ) ≤ x ^ θ := Nat.floor_le (by linarith [Real.one_le_rpow hx1 (by linarith : (0 : ℝ) ≤ θ)])
  have hD1D : D1 ≤ D := Nat.floor_le_floor hxθ
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < D1) hD1D)
  set L : ℝ := Real.log x with hL
  have hLx : L = (2 * N + 1 : ℕ) * Real.log b := by rw [hL, hx, Real.log_pow]
  have hL0 : 0 < L := by rw [hLx]; positivity
  have hlogD : Real.log D ≤ L := by
    have h1 : Real.log D ≤ Real.log (x ^ θ) := Real.log_le_log hD0 hD
    rw [Real.log_rpow (by linarith)] at h1
    have : θ * L ≤ L := mul_le_of_le_one_left hL0.le (by linarith)
    linarith
  -- polynomial size of the logarithms
  set n : ℕ := Nat.sqrt N with hn
  have hNn : 2 * N + 1 ≤ 3 * (n + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' N
    rw [← hn] at this
    have : N + 1 ≤ (n + 1) ^ 2 := this
    generalize (n + 1) ^ 2 = m at this ⊢
    omega
  have h1L : 1 + L ≤ Lb * ((n : ℝ) + 1) ^ 2 := by
    have h1 : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * ((n : ℝ) + 1) ^ 2 := by exact_mod_cast hNn
    have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    rw [hLx, hLb]
    have h3 := mul_le_mul_of_nonneg_right h1 hlogb.le
    linarith
  have hH : ∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k ≤
      (Lb * ((n : ℝ) + 1) ^ 2) ^ 3 := by
    refine le_trans (sum_three_pow_omega_div_le D) ?_
    have h0 : 0 ≤ ∑ a ∈ Icc 1 D, (1 : ℝ) / a := Finset.sum_nonneg (fun a _ => by positivity)
    have h1 := sum_inv_le_log D
    gcongr
    linarith
  have hlog2 : ∀ E : ℕ, 1 ≤ E → E ≤ D → (Nat.log 2 E : ℝ) ≤ 2 * (Lb * ((n : ℝ) + 1) ^ 2) := by
    intro E hE hED
    have h1 : (2 : ℝ) ^ (Nat.log 2 E) ≤ E := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
    have h2 : (Nat.log 2 E : ℝ) * Real.log 2 ≤ Real.log E := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    have hED' : Real.log E ≤ Real.log D := Real.log_le_log hE0 (by exact_mod_cast hED)
    have h3 := Real.log_two_gt_d9
    have h4 : (0 : ℝ) ≤ Nat.log 2 E := Nat.cast_nonneg _
    have h5 : (Nat.log 2 E : ℝ) * (1 / 2) ≤ (Nat.log 2 E : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    linarith
  -- the Farey total
  set K : ℝ := K0 * ((n : ℝ) + 1) ^ 4 * rhoL b ^ n with hKdef
  have hK0' : 0 ≤ K := by have := rhoL_nonneg b; positivity
  set E2 : ℝ := Cw2 * (2 * x ^ θ) ^ (κ / 2) * Y ^ (-κ) with hE2
  have hE20 : 0 ≤ E2 := by positivity
  set Kt : ℝ := (Nat.log 2 D : ℝ) * E2 + (Nat.log 2 D1 : ℝ) * K with hKt
  have hF : ∀ k : ℤ, ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
      ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
      ∑ h ∈ redRes q, Fprod b N ((h : ℝ) / q + k / (bigB b : ℝ)) ≤ Kt := by
    intro k
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun q => D1 < q)]
    apply add_le_add
    · -- high part
      have hgap := Y_gap b N hb (by omega)
      have hD1Y : 2 * Y ^ (47 / 100 : ℝ) ≤ D1 + 1 := by
        have := Nat.lt_floor_add_one (x ^ (6 / 25 : ℝ))
        rw [← hD1def] at this
        linarith
      exact farey_high b hb N D D1 θ κ (κ / 2) Cw2 (by positivity) hCw20 hCw2 hD hD1Y (hNT N hNTle) k
    · -- low part
      have e : ((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter (fun q => ¬ D1 < q) =
          (Icc 2 D1).filter (fun q => Nat.Coprime q (bigB b)) := by
        ext q; simp only [mem_filter, mem_Icc, not_lt]; constructor
        · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 hD1D⟩, h3⟩, h2⟩
      rw [e]
      have hKe : K = (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
          Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
          (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N) := by rw [hKdef, hK0]
      exact farey_total_le b hb Cw Ce hCw0 hCe0 hCw hCe N D1 hN2500 hD1 hD11 k K hKe
  have hE := level_explicit_gen b hb N D (by omega) Kt hF
  -- the second error term
  have hE2le : E2 ≤ Cw2 * (2 * (b : ℝ)) * ((b : ℝ) ^ (-(κ / 2))) ^ N :=
    E2_le b N hb θ κ Cw2 (by linarith) hθ1 hκ hκ1 hCw20
  -- final estimate
  rw [le_div_iff₀ (by positivity)]
  have hL3 : L ^ 3 ≤ (Lb * ((n : ℝ) + 1) ^ 2) ^ 3 := by gcongr; linarith
  have hlD1 := hlog2 D1 hD11 hD1D
  have hlD := hlog2 D (le_trans hD11 hD1D) le_rfl
  set P : ℝ := Lb * ((n : ℝ) + 1) ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hKt : Kt ≤ 2 * P * K + 2 * P * E2 := by
    have h1 := mul_le_mul_of_nonneg_right hlD1 hK0'
    have h2 := mul_le_mul_of_nonneg_right hlD hE20
    rw [hKt]; linarith
  have hB : (∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|) ≤
      SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * K + 2 * P * E2))) := by
    refine le_trans hE ?_
    have hH0 : 0 ≤ ∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    apply mul_le_mul_of_nonneg_left _ hSB0
    apply mul_le_mul hH _ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hKt (by positivity)
  have hLHS0 : 0 ≤ ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| :=
    Finset.sum_nonneg (fun q _ => by positivity)
  -- part 1 (as in `level_piStar_weighted`)
  have hpart1 : SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * K))) * P ^ 3 ≤ cA / 2 * (b : ℝ) ^ N := by
    have hgeo := hn₀ n hnn₀
    have e : SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * K))) * P ^ 3 =
        (b : ℝ) ^ N * (C * ((n : ℝ) + 1) ^ 18 * rhoL b ^ n) := by
      rw [hP, hKdef, hC, pow_succ]; ring
    rw [e, mul_comm (cA / 2)]
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  -- part 2
  have hpart2 : SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * E2))) * P ^ 3 ≤ cA / 2 * (b : ℝ) ^ N := by
    have hgeo := hn₂ N hNn₂
    have hPN : P ≤ Lb * (2 * ((N : ℝ) + 1)) := by
      rw [hP]
      apply mul_le_mul_of_nonneg_left _ hLb0
      have hs : ((n : ℝ)) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
      nlinarith only [hs, sq_nonneg ((n : ℝ) - 1)]
    have hP7 : P ^ 7 ≤ Lb ^ 7 * 2 ^ 7 * ((N : ℝ) + 1) ^ 7 := by
      calc P ^ 7 ≤ (Lb * (2 * ((N : ℝ) + 1))) ^ 7 := pow_le_pow_left₀ hP0 hPN 7
        _ = _ := by ring
    have hE2' : 0 ≤ Cw2 * (2 * (b : ℝ)) * ((b : ℝ) ^ (-(κ / 2))) ^ N := by positivity
    calc SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * E2))) * P ^ 3
        = 2 * SB * (b : ℝ) ^ (N + 1) * P ^ 7 * E2 := by ring
      _ ≤ 2 * SB * (b : ℝ) ^ (N + 1) * (Lb ^ 7 * 2 ^ 7 * ((N : ℝ) + 1) ^ 7) *
          (Cw2 * (2 * (b : ℝ)) * ((b : ℝ) ^ (-(κ / 2))) ^ N) := by
          apply mul_le_mul _ hE2le hE20 (by positivity)
          exact mul_le_mul_of_nonneg_left hP7 (by positivity)
      _ = (b : ℝ) ^ N * (C2 * ((N : ℝ) + 1) ^ 7 * ((b : ℝ) ^ (-(κ / 2))) ^ N) := by
          rw [hC2, pow_succ]; ring
      _ ≤ (b : ℝ) ^ N * (cA / 2) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = _ := by ring
  calc _ ≤ SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * K + 2 * P * E2))) * P ^ 3 :=
        mul_le_mul hB hL3 (by positivity) (by positivity)
    _ = SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * K))) * P ^ 3 +
        SB * (P ^ 3 * ((b : ℝ) ^ (N + 1) * (2 * P * E2))) * P ^ 3 := by ring
    _ ≤ cA / 2 * (b : ℝ) ^ N + cA / 2 * (b : ℝ) ^ N := add_le_add hpart1 hpart2
    _ = cA * (b : ℝ) ^ N := by ring
    _ ≤ _ := hN₁ N hNN₁

end Palprimes
