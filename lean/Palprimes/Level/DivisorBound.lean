import Palprimes.Defs

/-! # M5. Divisor bound

`τ(n) ≤ C_ε n^ε` from `τ(n) = Π (a_p + 1)` with `(a+1) ≤ (1 + 1/(ε log 2)) 2^{aε}` for the
boundedly many primes `p < 2^{1/ε}` and `(a+1) ≤ 2^a ≤ p^{aε}` otherwise;
`3^{ω(n)} ≤ τ(n)²`; `τ* = b^{o(L)}`. Not in mathlib or PNT+. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- `a + 1 ≤ C_ε · 2^{aε}` with `C_ε = 1 + 1/(ε log 2)`. -/
theorem add_one_le_two_rpow (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + 1 / (ε * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * ε) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < ε * Real.log 2 := by positivity
  have h2 : (2 : ℝ) ^ ((a : ℝ) * ε) = Real.exp ((a : ℝ) * ε * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  rw [h2]
  set x : ℝ := (a : ℝ) * ε * Real.log 2 with hxdef
  set c : ℝ := 1 / (ε * Real.log 2) with hcdef
  have he := Real.add_one_le_exp x
  have hx0 : 0 ≤ x := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hax : (a : ℝ) = c * x := by rw [hxdef, hcdef]; field_simp
  calc (a : ℝ) + 1 = c * x + 1 := by rw [hax]
    _ ≤ (1 + c) * (x + 1) := by nlinarith
    _ ≤ (1 + c) * Real.exp x := mul_le_mul_of_nonneg_left he (by linarith)

/-- **Divisor bound** `τ(n) ≤ C_ε n^ε`. -/
theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set C0 : ℝ := 1 + 1 / (ε * Real.log 2) with hC0
  have hC01 : 1 ≤ C0 := by
    have : 0 < ε * Real.log 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
    rw [hC0]; have : 0 < 1 / (ε * Real.log 2) := by positivity
    linarith
  set B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hB
  refine ⟨C0 ^ B, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  set P := n.primeFactors
  set a : ℕ → ℕ := fun p => n.factorization p
  rw [Nat.card_divisors hn0]
  have hnprod : (n : ℝ) = ∏ p ∈ P, ((p : ℝ) ^ (a p)) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    push_cast; rfl
  have hrpow : (n : ℝ) ^ ε = ∏ p ∈ P, ((p : ℝ) ^ ((a p : ℝ) * ε)) := by
    rw [hnprod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [hrpow]
  -- termwise bound
  have hterm : ∀ p ∈ P, ((a p : ℝ) + 1) ≤
      (if p < B then C0 else 1) * (p : ℝ) ^ ((a p : ℝ) * ε) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    split_ifs with hpB
    · calc (a p : ℝ) + 1 ≤ C0 * (2 : ℝ) ^ ((a p : ℝ) * ε) := add_one_le_two_rpow ε hε (a p)
        _ ≤ C0 * (p : ℝ) ^ ((a p : ℝ) * ε) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    · push Not at hpB
      have hpB' : (2 : ℝ) ^ (1 / ε) ≤ p := by
        calc (2 : ℝ) ^ (1 / ε) ≤ (B : ℝ) := Nat.le_ceil _
          _ ≤ p := by exact_mod_cast hpB
      have hpe : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hpB' hε.le
      have : (p : ℝ) ^ ((a p : ℝ) * ε) = ((p : ℝ) ^ ε) ^ (a p) := by
        rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
      rw [this, one_mul]
      calc (a p : ℝ) + 1 ≤ 2 ^ (a p) := by
            have := Nat.lt_two_pow_self (n := a p)
            exact_mod_cast this
        _ ≤ ((p : ℝ) ^ ε) ^ (a p) := pow_le_pow_left₀ (by norm_num) hpe _
  push_cast
  calc ∏ p ∈ P, ((a p : ℝ) + 1) ≤ ∏ p ∈ P, ((if p < B then C0 else 1) * (p : ℝ) ^ ((a p : ℝ) * ε)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hterm
    _ = (∏ p ∈ P, (if p < B then C0 else 1)) * ∏ p ∈ P, (p : ℝ) ^ ((a p : ℝ) * ε) :=
        Finset.prod_mul_distrib
    _ ≤ C0 ^ B * ∏ p ∈ P, (p : ℝ) ^ ((a p : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p _ => by positivity))
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply pow_le_pow_right₀ hC01
        calc #(P.filter (fun p => p < B)) ≤ #(range B) := by
              apply card_le_card
              intro p hp; rw [mem_range]; exact (mem_filter.1 hp).2
          _ = B := card_range B

theorem two_pow_omega_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ (ArithmeticFunction.cardDistinctFactors n) ≤ #n.divisors := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.card_divisors hn,
    ← Finset.prod_const]
  apply Finset.prod_le_prod
  intro p hp
  have : 1 ≤ n.factorization p := (Nat.Prime.factorization_pos_of_dvd
    (Nat.prime_of_mem_primeFactors hp) hn (Nat.dvd_of_mem_primeFactors hp))
  omega

theorem three_pow_omega_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC⟩ := card_divisors_le_rpow (ε / 2) (by positivity)
  refine ⟨C ^ 2, fun n hn => ?_⟩
  have h1 := two_pow_omega_le n (by omega)
  have h2 := hC n hn
  set w := ArithmeticFunction.cardDistinctFactors n
  have h3 : (3 : ℝ) ^ w ≤ ((2 : ℝ) ^ w) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; apply pow_le_pow_left₀ (by norm_num); norm_num
  have h4 : (2 : ℝ) ^ w ≤ C * (n : ℝ) ^ (ε / 2) := by
    calc (2 : ℝ) ^ w ≤ (#n.divisors : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ w := by positivity
  calc (3 : ℝ) ^ w ≤ ((2 : ℝ) ^ w) ^ 2 := h3
    _ ≤ (C * (n : ℝ) ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ h5 h4 2
    _ = C ^ 2 * (n : ℝ) ^ ε := by
        have : ((n : ℝ) ^ (ε / 2)) ^ 2 = (n : ℝ) ^ ε := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [mul_pow, this]

/-- Divisors of `w` in a dyadic range are at most `τ(w)`. -/
theorem card_dvd_Icc_le (Q w : ℕ) (hw : w ≠ 0) :
    #((Icc Q (2 * Q)).filter (· ∣ w)) ≤ #w.divisors := by
  apply card_le_card
  intro q hq
  rw [Nat.mem_divisors]
  exact ⟨(mem_filter.1 hq).2, hw⟩

/-- `τ* = b^{o(L)}`. -/
theorem tauStar_subexp (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ L Q : ℕ, (tauStar b L Q : ℝ) ≤ C * (b : ℝ) ^ (ε * L) := by
  set e : ℝ := min ε 1 / 3 with he
  have he0 : 0 < e := by rw [he]; have := lt_min hε one_pos; positivity
  have he1 : e ≤ 1 / 3 := by rw [he]; have := min_le_right ε 1; linarith
  have he2 : 2 * e ≤ ε := by rw [he]; have := min_le_left ε 1; linarith
  obtain ⟨C, hC⟩ := card_divisors_le_rpow e he0
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl
    simp at this
    linarith
  refine ⟨C * (2 * b), fun L Q => ?_⟩
  have hW1 : 1 ≤ 2 * b ^ (2 * L + 1) := by
    have := Nat.one_le_pow (2 * L + 1) b (by omega); omega
  have hsup : tauStar b L Q ≤ ((Icc 1 (2 * b ^ (2 * L + 1))).sup fun w => #w.divisors) := by
    unfold tauStar
    apply Finset.sup_mono_fun
    intro w hw
    exact card_dvd_Icc_le Q w (by rw [mem_Icc] at hw; omega)
  have hbound : ∀ w ∈ Icc 1 (2 * b ^ (2 * L + 1)), (#w.divisors : ℝ) ≤
      C * ((2 * b ^ (2 * L + 1) : ℕ) : ℝ) ^ e := by
    intro w hw
    rw [mem_Icc] at hw
    calc (#w.divisors : ℝ) ≤ C * (w : ℝ) ^ e := hC w hw.1
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hC0
          apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hw.2) he0.le
  have hsup' : (((Icc 1 (2 * b ^ (2 * L + 1))).sup fun w => #w.divisors : ℕ) : ℝ) ≤
      C * ((2 * b ^ (2 * L + 1) : ℕ) : ℝ) ^ e := by
    obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image (Icc 1 (2 * b ^ (2 * L + 1)))
      (fun w => #w.divisors) ⟨1, by rw [mem_Icc]; exact ⟨le_rfl, hW1⟩⟩
    have : ((Icc 1 (2 * b ^ (2 * L + 1))).sup fun w => #w.divisors) = #w.divisors :=
      le_antisymm (Finset.sup_le (fun v hv => hwmax v hv))
        (Finset.le_sup (f := fun w => #w.divisors) hw)
    rw [this]
    exact hbound w hw
  have hpow : ((2 * b ^ (2 * L + 1) : ℕ) : ℝ) ^ e ≤ (2 * b) * (b : ℝ) ^ (ε * L) := by
    push_cast
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul (by positivity)]
    have h2 : (2 : ℝ) ^ e ≤ 2 := by
      calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h3 : (b : ℝ) ^ (((2 * L + 1 : ℕ) : ℝ) * e) ≤ (b : ℝ) ^ (1 + ε * L) := by
      apply Real.rpow_le_rpow_of_exponent_le hb1
      push_cast
      have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    rw [Real.rpow_add (by positivity), Real.rpow_one] at h3
    have h4 : (0 : ℝ) ≤ (b : ℝ) ^ (((2 * L + 1 : ℕ) : ℝ) * e) := by positivity
    calc (2 : ℝ) ^ e * (b : ℝ) ^ (((2 * L + 1 : ℕ) : ℝ) * e) ≤ 2 * ((b : ℝ) * (b : ℝ) ^ (ε * L)) :=
          mul_le_mul h2 h3 h4 (by norm_num)
      _ = _ := by ring
  calc (tauStar b L Q : ℝ) ≤ (((Icc 1 (2 * b ^ (2 * L + 1))).sup fun w => #w.divisors : ℕ) : ℝ) := by
        exact_mod_cast hsup
    _ ≤ C * ((2 * b ^ (2 * L + 1) : ℕ) : ℝ) ^ e := hsup'
    _ ≤ C * ((2 * b) * (b : ℝ) ^ (ε * L)) := mul_le_mul_of_nonneg_left hpow hC0
    _ = _ := by ring

end Palprimes
