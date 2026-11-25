import KappaOmega2.Items.QK01_Exp
import Palprimes.Level.Level

namespace KappaOmega2

open Finset Palprimes
open scoped ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-! Item LK14: regrouping of the κ level sum into the Farey totals at the shifts `k/(b³ − b)` (port of L14 over the
index set `(u, w)`, product formula `QK01.fK_exp`). -/

open QK01

lemma lk14_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma lk14_ee_zero : ee 0 = 1 := by simp [ee]

lemma lk14_ee_int (z : ℤ) : ee (z : ℝ) = 1 := by
  unfold ee
  have := Complex.exp_int_mul_two_pi_mul_I z
  rw [← this]
  congr 1
  push_cast
  ring

lemma lk14_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  rw [← this]
  congr 2
  push_cast
  ring

/-- Full orthogonality. -/
lemma lk14_orth (q : ℕ) (hq : 0 < q) (m : ℤ) :
    ∑ h ∈ Finset.range q, ee ((m : ℝ) * ((h : ℝ) / q)) = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ))) :=
    ⟨_, rfl⟩
  have key : ∀ h : ℕ, ee ((m : ℝ) * ((h : ℝ) / q)) = z ^ h := by
    intro h
    unfold ee
    rw [hz, ← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  simp only [key]
  by_cases hd : (q : ℤ) ∣ m
  · rw [if_pos hd]
    obtain ⟨n, hn⟩ := hd
    have hz1 : z = 1 := by
      rw [hz]
      have : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ))) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
        have : (m : ℂ) = (q : ℂ) * n := by exact_mod_cast hn
        rw [this]; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hz1]
  · rw [if_neg hd]
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hz] at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : ((m : ℂ) / (q : ℂ) - n) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
        linear_combination hn
      have h4 : (m : ℂ) / (q : ℂ) - n = 0 := (mul_eq_zero.mp h3).resolve_right hpi
      have h5 : (m : ℂ) = (n : ℂ) * (q : ℂ) := by
        rw [sub_eq_zero, div_eq_iff hqC] at h4
        exact h4
      have h6 : m = n * (q : ℤ) := by exact_mod_cast h5
      exact hd ⟨n, by rw [h6]; ring⟩
    have hzq : z ^ q = 1 := by
      rw [hz, ← Complex.exp_natCast_mul]
      have h7 : (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ)))
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
      rw [h7, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzq, sub_self, zero_div]

lemma lk14_ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

noncomputable def lk14c (b : ℕ) (g : ℕ → ℝ) (N r q : ℕ) : ℝ :=
  open Classical in ∑ d : KIdx b N, if r ∣ kv b N d ∧ q ∣ kv b N d then kw b g N d else 0

lemma lk14_pair (b : ℕ) (g : ℕ → ℝ) (N r q : ℕ) (hr : 0 < r) (hq : 0 < q) :
    ∑ h1 ∈ range r, ∑ h2 ∈ range q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q) =
      ((r * q : ℕ) : ℂ) * (lk14c b g N r q : ℂ) := by
  classical
  unfold lk14c
  simp_rw [fK_exp]
  have hterm : ∀ (d : KIdx b N) (h1 h2 : ℕ), ee ((kv b N d : ℝ) * ((h1 : ℝ) / r + (h2 : ℝ) / q)) =
      ee (((kv b N d : ℤ) : ℝ) * ((h1 : ℝ) / r)) * ee (((kv b N d : ℤ) : ℝ) * ((h2 : ℝ) / q)) := by
    intro d h1 h2
    rw [← lk14_ee_add]; congr 1; push_cast; ring
  simp_rw [hterm]
  rw [Complex.ofReal_sum, Finset.mul_sum]
  calc ∑ h1 ∈ range r, ∑ h2 ∈ range q, ∑ d : KIdx b N, (kw b g N d : ℂ) *
        (ee (((kv b N d : ℤ) : ℝ) * ((h1 : ℝ) / r)) * ee (((kv b N d : ℤ) : ℝ) * ((h2 : ℝ) / q)))
      = ∑ d : KIdx b N, (kw b g N d : ℂ) * ((∑ h1 ∈ range r, ee (((kv b N d : ℤ) : ℝ) * ((h1 : ℝ) / r))) *
          (∑ h2 ∈ range q, ee (((kv b N d : ℤ) : ℝ) * ((h2 : ℝ) / q)))) := by
        rw [Finset.sum_congr rfl (fun h1 _ => Finset.sum_comm), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro h1 _
        rw [Finset.mul_sum]
    _ = _ := by
        apply Finset.sum_congr rfl; intro d _
        rw [lk14_orth r hr, lk14_orth q hq]
        simp only [Int.natCast_dvd_natCast]
        by_cases h1 : r ∣ kv b N d <;> by_cases h2 : q ∣ kv b N d <;> simp [h1, h2]
        push_cast; ring

lemma lk14_AW (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) (hb : 2 ≤ b) :
    AK b g N q = ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * lk14c b g N r q := by
  classical
  have hB : bigB b ≠ 0 := by
    unfold bigB
    have : b < b ^ 3 := by
      calc b = b ^ 1 := (pow_one b).symm
        _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  rw [AK_eq]
  unfold lk14c
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hq : q ∣ kv b N d
  · have h := coprime_indicator (kv b N d) (bigB b) hB
    have h' : (if Nat.Coprime (kv b N d) (bigB b) then (1 : ℝ) else 0) =
        ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * (if r ∣ kv b N d then 1 else 0) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      simpa [Int.cast_sum, apply_ite] using this
    have e : ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * (if r ∣ kv b N d ∧ q ∣ kv b N d then kw b g N d else 0) =
        kw b g N d * ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * (if r ∣ kv b N d then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      by_cases hr : r ∣ kv b N d
      · simp [hr, hq]; ring
      · simp [hr]
    rw [e, ← h']
    by_cases hc : Nat.Coprime (kv b N d) (bigB b) <;> simp [hc, hq, mul_comm]
  · have : ∀ r ∈ (bigB b).divisors, (μ r : ℝ) * (if r ∣ kv b N d ∧ q ∣ kv b N d then kw b g N d else 0) = 0 := by
      intro r _; simp [hq]
    rw [Finset.sum_eq_zero this]
    simp [hq]

lemma lk14_R (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) (hb : 2 ≤ b) (hq : 0 < q) :
    |RK b g N q| ≤ (1 / (q : ℝ)) * ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) *
      ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
  classical
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnn : 0 ≤ (1 / (q : ℝ)) * ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) *
      ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by positivity
  by_cases hc : Nat.Coprime q (bigB b)
  swap
  · have hA : AK b g N q = 0 := by
      rw [AK_eq]
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hc (Nat.Coprime.coprime_dvd_left h2 h1)
    have hρ : rhoB b q = 0 := by unfold rhoB; rw [if_neg hc]
    unfold RK
    rw [hA, hρ]; simpa using hnn
  · have hρ : rhoB b q = 1 := by unfold rhoB; rw [if_pos hc]
    have hR : RK b g N q = ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * (lk14c b g N r q - lk14c b g N r 1 / q) := by
      unfold RK
      rw [hρ, lk14_AW b g N q hb]
      have hX : XK b g N = ∑ r ∈ (bigB b).divisors, (μ r : ℝ) * lk14c b g N r 1 := by
        unfold XK; exact lk14_AW b g N 1 hb
      rw [hX, mul_one, Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro r _; ring
    have hE : ∀ r ∈ (bigB b).divisors, (((lk14c b g N r q - lk14c b g N r 1 / q : ℝ)) : ℂ) =
        (∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)) / ((r : ℂ) * q) := by
      intro r hr
      have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      have p1 := lk14_pair b g N r q hr0 hq
      have p2 := lk14_pair b g N r 1 hr0 one_pos
      have hsplit : ∀ h1 : ℕ, ∑ h2 ∈ range q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q) =
          fK b g N ((h1 : ℝ) / r + ((0 : ℕ) : ℝ) / 1) + ∑ h2 ∈ Ico 1 q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q) := by
        intro h1
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hq]
        simp
      simp_rw [hsplit] at p1
      rw [Finset.sum_add_distrib] at p1
      have p3 : ∑ h1 ∈ range r, fK b g N ((h1 : ℝ) / r + ((0 : ℕ) : ℝ) / 1) = ((r * 1 : ℕ) : ℂ) * (lk14c b g N r 1 : ℂ) := by
        rw [← p2]
        apply Finset.sum_congr rfl; intro h1 _
        simp
      rw [p3] at p1
      rw [eq_div_iff (mul_ne_zero hrC hqC)]
      push_cast at p1 ⊢
      have hqq : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hqC
      linear_combination (-1 : ℂ) * p1 + (-((r : ℂ) * (lk14c b g N r 1 : ℂ))) * hqq
    have hnorm : ‖(RK b g N q : ℂ)‖ ≤ (1 / (q : ℝ)) * ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) *
        ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
      rw [hR, Complex.ofReal_sum]
      have : ∀ r ∈ (bigB b).divisors, (((μ r : ℝ) * (lk14c b g N r q - lk14c b g N r 1 / q) : ℝ) : ℂ) =
          (μ r : ℂ) * ((∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)) / ((r : ℂ) * q)) := by
        intro r hr
        rw [Complex.ofReal_mul, hE r hr]; push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
      have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
      rw [norm_mul, norm_div, norm_mul]
      have h1 : ‖(μ r : ℂ)‖ ≤ 1 := by
        have : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        simpa [Complex.norm_intCast] using this
      have h2 : ‖∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ ≤
          ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h1 _ => norm_sum_le _ _)
      have h3 : ‖(r : ℂ)‖ = (r : ℝ) := by simp
      have h4 : ‖(q : ℂ)‖ = (q : ℝ) := by simp
      rw [h3, h4]
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      calc ‖(μ r : ℂ)‖ * (‖∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ / ((r : ℝ) * q))
          ≤ 1 * ((∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖) / ((r : ℝ) * q)) := by
            apply mul_le_mul h1 (div_le_div_of_nonneg_right h2 (by positivity)) (by positivity) (by norm_num)
        _ = (1 / (q : ℝ)) * ((1 / (r : ℝ)) * ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖) := by
            generalize (∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖) = S
            field_simp
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm

lemma lk14_R0 (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) (hc : ¬ Nat.Coprime q (bigB b)) : RK b g N q = 0 := by
  classical
  have hA : AK b g N q = 0 := by
    rw [AK_eq]
    apply Finset.sum_eq_zero
    intro d _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hc (Nat.Coprime.coprime_dvd_left h2 h1)
  have hρ : rhoB b q = 0 := by unfold rhoB; rw [if_neg hc]
  unfold RK
  rw [hA, hρ]; simp

theorem itemLK14 : ItemLK14 := by
  classical
  intro b g N D Kt hb3 hKt
  have hb : 2 ≤ b := by omega
  have hB : bigB b ≠ 0 := by
    unfold bigB
    have : b < b ^ 3 := by
      calc b = b ^ 1 := (pow_one b).symm
        _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  set H : ℝ := ∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun e _ => by positivity)
  unfold levelSumK
  -- step 1: restrict to coprime d
  have hstep1 : ∑ d ∈ (Icc 1 D).filter Squarefree, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RK b g N d| ≤
      ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
        (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RK b g N d| := by
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro d _
    by_cases hs : Squarefree d
    · by_cases hc : Nat.Coprime d (bigB b)
      · rw [if_pos hs, if_pos hc]
      · rw [if_pos hs, if_neg hc, lk14_R0 b g N d hc]; simp
    · rw [if_neg hs]
      by_cases hc : Nat.Coprime d (bigB b)
      · rw [if_pos hc]; positivity
      · rw [if_neg hc]
  refine hstep1.trans ?_
  -- step 2: the bound for R
  have hstep2 : ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
        (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RK b g N d| ≤
      ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
          ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r,
            ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 0 < d := by
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hd).1).1; omega
    have := lk14_R b g N d hb hd1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd1.ne'
    have hinner : ∀ r : ℕ, ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h1 : ℝ) / r + (h2 : ℝ) / d)‖ =
        ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ := by
      intro r
      apply Finset.sum_congr rfl; intro h1 _
      apply Finset.sum_congr rfl; intro h2 _
      rw [add_comm]
    simp_rw [hinner] at this
    set T := ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r,
          ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ with hT
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by positivity
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RK b g N d|
        ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * ((1 / (d : ℝ)) * T) :=
          mul_le_mul_of_nonneg_left this h3
      _ = ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) * T := by ring
  refine hstep2.trans ?_
  -- per (r, h1) bound via regroup
  have hper : ∀ r ∈ (bigB b).divisors, ∀ h1 ∈ range r,
      ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
          ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ ≤ H * Kt := by
    intro r hr h1 hh1
    have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
    have hreg := regroup D (bigB b) (fun x => ‖fK b g N (x + (h1 : ℝ) / r)‖) (fun t => norm_nonneg _)
    have hKt' : FareyK b g N D ((h1 : ℝ) / r) ≤ Kt := by
      obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors hr
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h] at hc; simp at hc; exact absurd hc hB
        · exact h
      have hk : h1 * c < bigB b := by
        rw [hc]; exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.1 hh1) hc0
      have := hKt (h1 * c) hk
      have e : ((h1 * c : ℕ) : ℝ) / (bigB b : ℝ) = (h1 : ℝ) / r := by
        rw [hc]; push_cast
        have : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
        have : (c : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
        field_simp
      rwa [e] at this
    have hF : ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
          ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
            ∑ h ∈ redRes q, ‖fK b g N ((h : ℝ) / q + (h1 : ℝ) / r)‖ = FareyK b g N D ((h1 : ℝ) / r) := by
      unfold FareyK L1fareyK; rfl
    simp only [hF] at hreg
    refine hreg.trans ?_
    exact mul_le_mul_of_nonneg_left hKt' hH0
  -- swap sums
  have hswap : ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
      ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
        ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r,
          ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ =
      ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r,
        ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
          ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
            ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖ := by
    calc _ = ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)), ∑ r ∈ (bigB b).divisors,
          ∑ h1 ∈ range r, (1 / (r : ℝ)) * (((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
            ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖) := by
          apply Finset.sum_congr rfl; intro d _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
          rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro h1 _; ring
      _ = ∑ r ∈ (bigB b).divisors, ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
          ∑ h1 ∈ range r, (1 / (r : ℝ)) * (((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
            ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖) := Finset.sum_comm
      _ = ∑ r ∈ (bigB b).divisors, ∑ h1 ∈ range r, ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d (bigB b)),
          (1 / (r : ℝ)) * (((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d / d) *
            ∑ h2 ∈ Ico 1 d, ‖fK b g N ((h2 : ℝ) / d + (h1 : ℝ) / r)‖) := by
          apply Finset.sum_congr rfl; intro r _; exact Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro r _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h1 _
          rw [Finset.mul_sum]
  rw [hswap]
  calc _ ≤ ∑ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r, (H * Kt) := by
        apply Finset.sum_le_sum; intro r hr
        have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_mem_divisors hr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun h1 hh1 => hper r hr h1 hh1)
    _ = ((bigB b).divisors.card : ℝ) * H * Kt := by
        have : ∀ r ∈ (bigB b).divisors, (1 / (r : ℝ)) * ∑ h1 ∈ range r, (H * Kt) = H * Kt := by
          intro r hr
          have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_mem_divisors hr
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]; ring

end KappaOmega2
