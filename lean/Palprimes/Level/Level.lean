import Palprimes.ExpSum.ColBound

/-! # M10. Level of distribution `6/25` for `Π*_b(2N)`

* `level_err_le`: Möbius over `r ∣ b³ − b` and orthogonality for pairs (`sum_Ssum_pair`) give
  `|A*_q − #A*/q| ≤ q⁻¹ Σ_{r,h1} Σ_{0<h2<q} |S(h1/r + h2/q)|`;
* `regroup`: reduced fractions `h'/q'` with weights `3^ω`, using `3^{ω(k)} ≤ τ₃(k)`
  (`three_pow_omega_le_triples`) and `Σ_{k≤D} 3^{ω(k)}/k ≤ H_D³`;
* `level_block_gen`: one dyadic block `q ∈ [R, 2R)`: weight, Col's bound on the outer digits,
  `farey_block` on the window;
* `level_piStar_weighted`: assembly over dyadic blocks with two regimes. -/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Moebius

namespace Palprimes

/-- Digit vectors with nonzero outer digit. -/
def D0 (b N : ℕ) : Finset (DigVec b N) := (univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0)

/-- The exponential sum over `Π_b(2N)`. -/
noncomputable def Ssum (b N : ℕ) (α : ℝ) : ℂ := ∑ d ∈ D0 b N, ee ((palVal b N d : ℝ) * α)

theorem moebius_sum_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- `[(n, B) = 1] = Σ_{r ∣ B} μ(r) [r ∣ n]`. -/
theorem coprime_indicator (n B : ℕ) (hB : B ≠ 0) :
    (if Nat.Coprime n B then (1 : ℤ) else 0) =
      ∑ r ∈ B.divisors, (μ r : ℤ) * (if r ∣ n then 1 else 0) := by
  have e : B.divisors.filter (· ∣ n) = (Nat.gcd n B).divisors := by
    ext r
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, Nat.gcd_ne_zero_right hB⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hB⟩, h1⟩
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, e, moebius_sum_divisors]

/-- **Orthogonality for pairs**: `Σ_{h1<r} Σ_{h2<q} S(h1/r + h2/q) = rq · #{r ∣ n, q ∣ n}`. -/
theorem sum_Ssum_pair (b N r q : ℕ) (hr : 0 < r) (hq : 0 < q) :
    ∑ h1 ∈ range r, ∑ h2 ∈ range q, Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q) =
      ((r * q : ℕ) : ℂ) * #((D0 b N).filter (fun d => r ∣ palVal b N d ∧ q ∣ palVal b N d)) := by
  unfold Ssum
  have hterm : ∀ d h1 h2, ee ((palVal b N d : ℝ) * ((h1 : ℝ) / r + (h2 : ℝ) / q)) =
      ee (((palVal b N d : ℤ) : ℝ) * h1 / r) * ee (((palVal b N d : ℤ) : ℝ) * h2 / q) := by
    intro d h1 h2
    rw [← ee_add]; congr 1; push_cast; ring
  simp only [hterm]
  calc ∑ h1 ∈ range r, ∑ h2 ∈ range q, ∑ d ∈ D0 b N,
        ee (((palVal b N d : ℤ) : ℝ) * h1 / r) * ee (((palVal b N d : ℤ) : ℝ) * h2 / q)
      = ∑ d ∈ D0 b N, ∑ h1 ∈ range r, ∑ h2 ∈ range q,
        ee (((palVal b N d : ℤ) : ℝ) * h1 / r) * ee (((palVal b N d : ℤ) : ℝ) * h2 / q) := by
        rw [Finset.sum_congr rfl (fun h1 _ => Finset.sum_comm), Finset.sum_comm]
    _ = ∑ d ∈ D0 b N, (if (r : ℤ) ∣ (palVal b N d : ℤ) then (r : ℂ) else 0) *
          (if (q : ℤ) ∣ (palVal b N d : ℤ) then (q : ℂ) else 0) := by
        apply Finset.sum_congr rfl; intro d _
        rw [← sum_ee_root r hr, ← sum_ee_root q hq, Finset.sum_mul_sum]
    _ = _ := by
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        simp only [Int.natCast_dvd_natCast]
        split_ifs <;> simp_all

theorem piStar_eq_image (b N : ℕ) (hb : 2 ≤ b) :
    piStar b N = ((D0 b N).filter (fun d => Nat.Coprime (palVal b N d) (bigB b))).image (palVal b N) := by
  have h := pal_eq_image b N hb
  ext n
  simp only [piStar, D0, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hI, hpal, hcop⟩
    have : n ∈ (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := mem_filter.2 ⟨hI, hpal⟩
    rw [h] at this
    obtain ⟨d, hd, rfl⟩ := mem_image.1 this
    exact ⟨d, ⟨(mem_filter.1 hd).2, hcop⟩, rfl⟩
  · rintro ⟨d, ⟨hd, hcop⟩, rfl⟩
    have : palVal b N d ∈ (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := by
      rw [h]; exact mem_image.2 ⟨d, mem_filter.2 ⟨mem_univ _, hd⟩, rfl⟩
    obtain ⟨hI, hpal⟩ := mem_filter.1 this
    exact ⟨hI, hpal, hcop⟩

theorem bigB_ne_zero (b : ℕ) (hb : 2 ≤ b) : bigB b ≠ 0 := by
  unfold bigB
  have h4 : 4 ≤ b * b := Nat.mul_le_mul hb hb
  have h3 : b * 4 ≤ b ^ 3 := by
    calc b * 4 ≤ b * (b * b) := Nat.mul_le_mul_left _ h4
      _ = b ^ 3 := by ring
  omega

/-- **Möbius expansion** of `A*_q` over `r ∣ b³ − b`. -/
theorem countDvd_moebius (b N q : ℕ) (hb : 2 ≤ b) :
    (countDvd (piStar b N) q : ℤ) =
      ∑ r ∈ (bigB b).divisors, (μ r : ℤ) *
        #((D0 b N).filter (fun d => r ∣ palVal b N d ∧ q ∣ palVal b N d)) := by
  classical
  unfold countDvd
  rw [piStar_eq_image b N hb, Finset.filter_image, Finset.card_image_of_injective _ (palVal_injective b N hb),
    Finset.filter_filter]
  rw [Finset.card_filter]
  push_cast
  have hrow : ∀ d ∈ D0 b N, (if Nat.Coprime (palVal b N d) (bigB b) ∧ q ∣ palVal b N d then (1 : ℤ) else 0) =
      ∑ r ∈ (bigB b).divisors, (μ r : ℤ) * (if r ∣ palVal b N d ∧ q ∣ palVal b N d then 1 else 0) := by
    intro d _
    by_cases hq : q ∣ palVal b N d
    · simp only [hq, and_true]
      exact coprime_indicator _ _ (bigB_ne_zero b hb)
    · simp [hq]
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [← Finset.mul_sum, Finset.card_filter]; push_cast; rfl

theorem card_piStar_moebius (b N : ℕ) (hb : 2 ≤ b) :
    (#(piStar b N) : ℤ) = ∑ r ∈ (bigB b).divisors, (μ r : ℤ) *
      #((D0 b N).filter (fun d => r ∣ palVal b N d ∧ 1 ∣ palVal b N d)) := by
  rw [← countDvd_moebius b N 1 hb]
  unfold countDvd
  simp

/-- **The level error** as exponential sums at `h1/r + h2/q`, `r ∣ b³ − b`, `0 < h2 < q`. -/
theorem level_err_le (b N q : ℕ) (hb : 2 ≤ b) (hq : 0 < q) :
    |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| ≤
      (1 / (q : ℝ)) * ∑ r ∈ (bigB b).divisors, ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q,
        ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
  classical
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  set c : ℕ → ℕ → ℕ := fun r q => #((D0 b N).filter (fun d => r ∣ palVal b N d ∧ q ∣ palVal b N d))
  set E : ℕ → ℂ := fun r => ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)
  have hE : ∀ r ∈ (bigB b).divisors, ((r * q : ℕ) : ℂ) * c r q = ((r : ℕ) : ℂ) * c r 1 + E r := by
    intro r hr
    have hr0 : 0 < r := Nat.pos_of_mem_divisors hr
    have h1 := sum_Ssum_pair b N r q hr0 hq
    have h2 := sum_Ssum_pair b N r 1 hr0 one_pos
    simp only [c] at h1 h2 ⊢
    rw [← h1]
    rw [show ((r : ℕ) : ℂ) = ((r * 1 : ℕ) : ℂ) by simp, ← h2]
    simp only [E, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro h1' _
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hq, Finset.sum_range_one]
    simp
  -- the identity for the error
  have hid : ((countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q : ℂ) =
      ∑ r ∈ (bigB b).divisors, ((μ r : ℤ) : ℂ) * (E r / ((r : ℂ) * q)) := by
    have h1 := countDvd_moebius b N q hb
    have h2 := card_piStar_moebius b N hb
    have h1' : ((countDvd (piStar b N) q : ℕ) : ℂ) = ∑ r ∈ (bigB b).divisors, ((μ r : ℤ) : ℂ) * (c r q : ℂ) := by
      exact_mod_cast h1
    have h2' : ((#(piStar b N) : ℕ) : ℂ) = ∑ r ∈ (bigB b).divisors, ((μ r : ℤ) : ℂ) * (c r 1 : ℂ) := by
      exact_mod_cast h2
    push_cast
    rw [h1', h2', Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r hr
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hr).ne'
    have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have := hE r hr
    push_cast at this
    rw [show E r = (r : ℂ) * q * c r q - r * c r 1 by rw [this]; ring]
    field_simp
  have habs : |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| =
      ‖((countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q : ℂ)‖ := by
    have e : (((countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q : ℝ) : ℂ) =
        ((countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q : ℂ) := by push_cast; ring
    rw [← e, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hid]
  calc ‖∑ r ∈ (bigB b).divisors, ((μ r : ℤ) : ℂ) * (E r / ((r : ℂ) * q))‖
      ≤ ∑ r ∈ (bigB b).divisors, ‖((μ r : ℤ) : ℂ) * (E r / ((r : ℂ) * q))‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ (bigB b).divisors, (1 / (q : ℝ)) * ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q,
          ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
        apply Finset.sum_le_sum; intro r hr
        have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.pos_of_mem_divisors hr
        have hmu : ‖((μ r : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hEr : ‖E r‖ ≤ ∑ h1 ∈ range r, ∑ h2 ∈ Ico 1 q, ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h1 _ => norm_sum_le _ _))
        rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
        calc ‖((μ r : ℤ) : ℂ)‖ * (‖E r‖ / ((r : ℝ) * q)) ≤ 1 * (‖E r‖ / (1 * q)) := by
              apply mul_le_mul hmu _ (by positivity) (by norm_num)
              apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right hr1 hq0.le
          _ ≤ _ := by rw [one_mul, one_mul, div_eq_mul_one_div, mul_comm]; gcongr
    _ = _ := by rw [Finset.mul_sum]


theorem omega_mul_le (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ArithmeticFunction.cardDistinctFactors (m * n) ≤
      ArithmeticFunction.cardDistinctFactors m + ArithmeticFunction.cardDistinctFactors n := by
  simp only [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_mul hm hn]
  exact card_union_le _ _

theorem three_pow_omega_mul_le (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors (m * n) ≤
      (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors m * (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n := by
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (omega_mul_le m n hm hn)

/-- Triples with product `k`. -/
def triples (k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Icc 1 k) ×ˢ (Icc 1 k) ×ˢ (Icc 1 k)).filter (fun t => t.1 * t.2.1 * t.2.2 = k)

/-- Component of an assignment of primes to three factors. -/
def comp (k : ℕ) (f : k.primeFactors → Fin 3) (i : Fin 3) : ℕ :=
  ∏ p ∈ (k.primeFactors).attach.filter (fun p => f p = i), (p : ℕ) ^ (k.factorization p)

theorem prod_attach_pow (k : ℕ) (hk : k ≠ 0) :
    ∏ p ∈ (k.primeFactors).attach, (p : ℕ) ^ (k.factorization p) = k := by
  rw [Finset.prod_attach (k.primeFactors) (fun p => p ^ k.factorization p)]
  exact (Nat.prod_primeFactors_pow_factorization hk).symm

theorem comp_mul (k : ℕ) (hk : k ≠ 0) (f : k.primeFactors → Fin 3) :
    comp k f 0 * comp k f 1 * comp k f 2 = k := by
  unfold comp
  have h := Finset.prod_fiberwise ((k.primeFactors).attach) f
    (fun p : k.primeFactors => (p : ℕ) ^ (k.factorization p))
  rw [prod_attach_pow k hk, Fin.prod_univ_three] at h
  exact h

theorem comp_dvd (k : ℕ) (hk : k ≠ 0) (f : k.primeFactors → Fin 3) (i : Fin 3) : comp k f i ∣ k := by
  unfold comp
  conv_rhs => rw [← prod_attach_pow k hk]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

theorem dvd_comp_iff (k : ℕ) (f : k.primeFactors → Fin 3) (p : k.primeFactors) (i : Fin 3) :
    (p : ℕ) ∣ comp k f i ↔ f p = i := by
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  unfold comp
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨p', hp', hdvd⟩
    rw [Finset.mem_filter] at hp'
    have hp'p : (p' : ℕ).Prime := Nat.prime_of_mem_primeFactors p'.2
    have := (Nat.prime_dvd_prime_iff_eq hp hp'p).1 (hp.dvd_of_dvd_pow hdvd)
    have hpp : p = p' := Subtype.ext this
    rw [hpp]; exact hp'.2
  · intro h
    refine ⟨p, Finset.mem_filter.2 ⟨Finset.mem_attach _ _, h⟩, ?_⟩
    have hv : 1 ≤ k.factorization p := (Nat.Prime.factorization_pos_of_dvd hp
      (Nat.mem_primeFactors.1 p.2).2.2 (Nat.dvd_of_mem_primeFactors p.2))
    exact dvd_pow_self _ (by omega)

/-- `3^{ω(k)} ≤ τ₃(k)`. -/
theorem three_pow_omega_le_triples (k : ℕ) (hk : k ≠ 0) :
    3 ^ ArithmeticFunction.cardDistinctFactors k ≤ #(triples k) := by
  classical
  have hcard : Fintype.card (k.primeFactors → Fin 3) = 3 ^ ArithmeticFunction.cardDistinctFactors k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  rw [← hcard, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun f => (comp k f 0, comp k f 1, comp k f 2))
  · intro f _
    simp only [triples, coe_filter, mem_product, mem_Icc]
    have h := comp_mul k hk f
    have hpos : ∀ i, 1 ≤ comp k f i := fun i => Nat.pos_of_ne_zero (fun h0 => by
      have := comp_dvd k hk f i; rw [h0] at this; exact hk (Nat.eq_zero_of_zero_dvd this))
    have hle : ∀ i, comp k f i ≤ k := fun i => Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (comp_dvd k hk f i)
    exact ⟨⟨⟨hpos 0, hle 0⟩, ⟨hpos 1, hle 1⟩, ⟨hpos 2, hle 2⟩⟩, h⟩
  · intro f _ g _ hfg
    simp only [Prod.mk.injEq] at hfg
    funext p
    have h1 : (p : ℕ) ∣ comp k f (f p) := (dvd_comp_iff k f p (f p)).2 rfl
    have key : ∀ i, comp k f i = comp k g i := by
      intro i; fin_cases i
      · exact hfg.1
      · exact hfg.2.1
      · exact hfg.2.2
    rw [key] at h1
    exact ((dvd_comp_iff k g p (f p)).1 h1).symm

/-- `Σ_{k≤D} 3^{ω(k)}/k ≤ H_D³`. -/
theorem sum_three_pow_omega_div_le (D : ℕ) :
    ∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k ≤
      (∑ a ∈ Icc 1 D, (1 : ℝ) / a) ^ 3 := by
  classical
  have h1 : ∀ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k ≤
      ∑ t ∈ triples k, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) := by
    intro k hk
    rw [mem_Icc] at hk
    have hk0 : k ≠ 0 := by omega
    have := three_pow_omega_le_triples k hk0
    have e : ∑ t ∈ triples k, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) = (#(triples k) : ℝ) / k := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ) / k) (fun t ht => by
        simp only [triples, mem_filter] at ht; rw [← ht.2]; push_cast; ring), Finset.sum_const,
        nsmul_eq_mul]; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
    exact_mod_cast this
  calc ∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k
      ≤ ∑ k ∈ Icc 1 D, ∑ t ∈ triples k, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) := Finset.sum_le_sum h1
    _ = ∑ t ∈ (Icc 1 D).biUnion triples, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) := by
        rw [Finset.sum_biUnion]
        intro k _ k' _ hkk'
        rw [Function.onFun, Finset.disjoint_left]
        intro t h1 h2
        simp only [triples, mem_filter] at h1 h2
        exact hkk' (h1.2.symm.trans h2.2)
    _ ≤ ∑ t ∈ Icc 1 D ×ˢ Icc 1 D ×ˢ Icc 1 D, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          obtain ⟨k, hk, htk⟩ := Finset.mem_biUnion.1 ht
          simp only [triples, mem_filter, mem_product, mem_Icc] at htk hk ⊢
          refine ⟨⟨htk.1.1.1, ?_⟩, ⟨htk.1.2.1.1, ?_⟩, ⟨htk.1.2.2.1, ?_⟩⟩
          · have := htk.1.1.2; omega
          · have := htk.1.2.1.2; omega
          · have := htk.1.2.2.2; omega
        · intro t _ _; positivity
    _ = _ := by
        have hsplit : ∀ t : ℕ × ℕ × ℕ, (1 : ℝ) / (t.1 * t.2.1 * t.2.2) =
            (1 / (t.1 : ℝ)) * ((1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) := by
          intro t; simp only [one_div, mul_inv]; ring
        simp only [hsplit, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

/-- **Regrouping into reduced fractions** with `3^ω` weights. -/
theorem regroup (D B : ℕ) (G : ℝ → ℝ) (hG : ∀ t, 0 ≤ G t) :
    ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q B),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) * ∑ h ∈ Ico 1 q, G ((h : ℝ) / q) ≤
      (∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q B),
          ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) * ∑ h ∈ redRes q, G ((h : ℝ) / q) := by
  classical
  set Q1 := (Icc 1 D).filter (fun q => Nat.Coprime q B)
  set Q2 := (Icc 2 D).filter (fun q => Nat.Coprime q B)
  set w : ℕ → ℝ := fun q => (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q
  have hw0 : ∀ q, 0 ≤ w q := fun q => by positivity
  set P := Q1.sigma (fun q => Ico 1 q)
  set T := (Q2.sigma (fun q => redRes q)) ×ˢ Icc 1 D
  set f : (Σ _ : ℕ, ℕ) → ℝ := fun p => w p.1 * G ((p.2 : ℝ) / p.1)
  set F : (Σ _ : ℕ, ℕ) × ℕ → ℝ := fun x => (w x.1.1 * G ((x.1.2 : ℝ) / x.1.1)) * w x.2
  have hF0 : ∀ x, 0 ≤ F x := fun x => mul_nonneg (mul_nonneg (hw0 _) (hG _)) (hw0 _)
  set φ : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) × ℕ := fun p =>
    (⟨p.1 / Nat.gcd p.2 p.1, p.2 / Nat.gcd p.2 p.1⟩, Nat.gcd p.2 p.1)
  have hLHS : ∑ q ∈ Q1, w q * ∑ h ∈ Ico 1 q, G ((h : ℝ) / q) = ∑ p ∈ P, f p := by
    rw [Finset.sum_sigma]; apply Finset.sum_congr rfl; intro q _; rw [Finset.mul_sum]
  have hRHS : (∑ k ∈ Icc 1 D, w k) * ∑ q ∈ Q2, w q * ∑ h ∈ redRes q, G ((h : ℝ) / q) = ∑ x ∈ T, F x := by
    rw [Finset.sum_product, Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro k _
    simp only [F]; ring
  rw [hLHS, hRHS]
  have hmem : ∀ p ∈ P, φ p ∈ T ∧ f p ≤ F (φ p) := by
    rintro ⟨q, h⟩ hp
    simp only [P, Finset.mem_sigma] at hp
    obtain ⟨hq, hh⟩ := hp
    simp only [Q1, mem_filter, mem_Icc] at hq
    rw [mem_Ico] at hh
    set g := Nat.gcd h q with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgq : g ∣ q := Nat.gcd_dvd_right h q
    have hgh : g ∣ h := Nat.gcd_dvd_left h q
    have hgle : g ≤ h := Nat.le_of_dvd (by omega) hgh
    have hq' : 2 ≤ q / g := by
      obtain ⟨c, hc⟩ := hgq
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, mul_zero] at hc; omega
        · exact h0
      rw [hc, Nat.mul_div_cancel_left _ hg0]
      by_contra hlt
      have : c = 1 := by omega
      rw [this, mul_one] at hc
      omega
    have hqD : q / g ≤ D := le_trans (Nat.div_le_self _ _) hq.1.2
    have hcopB : Nat.Coprime (q / g) B := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hgq) hq.2
    have hred : h / g ∈ redRes (q / g) := by
      simp only [redRes, mem_filter, mem_range]
      refine ⟨?_, Nat.coprime_div_gcd_div_gcd hg0⟩
      exact Nat.div_lt_div_of_lt_of_dvd hgq hh.2
    have hgD : g ∈ Icc 1 D := by rw [mem_Icc]; exact ⟨hg0, le_trans (Nat.le_of_dvd (by omega) hgq) hq.1.2⟩
    refine ⟨?_, ?_⟩
    · simp only [T, Q2, φ, mem_product, mem_sigma, mem_filter]
      exact ⟨⟨⟨mem_Icc.2 ⟨hq', hqD⟩, hcopB⟩, hred⟩, hgD⟩
    · simp only [f, F, φ, w]
      have hqq : q = q / g * g := (Nat.div_mul_cancel hgq).symm
      have hfrac : ((h / g : ℕ) : ℝ) / ((q / g : ℕ) : ℝ) = (h : ℝ) / q := by
        rw [Nat.cast_div hgh (by exact_mod_cast hg0.ne'), Nat.cast_div hgq (by exact_mod_cast hg0.ne')]
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
        field_simp
      rw [hfrac, ← hg]
      have hw3 := three_pow_omega_mul_le (q / g) g (by omega) hg0.ne'
      rw [← hqq] at hw3
      have hqR : (q : ℝ) = ((q / g : ℕ) : ℝ) * g := by exact_mod_cast hqq
      set t := G ((h : ℝ) / q) with ht
      have ht0 : 0 ≤ t := hG _
      have hpos1 : (0 : ℝ) < ((q / g : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q / g)
      have hpos2 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
      rw [hqR]
      calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / (((q / g : ℕ) : ℝ) * g) * t
          ≤ ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors (q / g) *
              (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors g) / (((q / g : ℕ) : ℝ) * g) * t := by
            apply mul_le_mul_of_nonneg_right _ ht0
            exact div_le_div_of_nonneg_right hw3 (by positivity)
        _ = _ := by field_simp
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, h⟩ hp ⟨q2, h2⟩ hp2 heq
    simp only [φ, Prod.mk.injEq, Sigma.mk.injEq] at heq
    obtain ⟨⟨e1, e2⟩, e3⟩ := heq
    simp only [P, Finset.mem_coe, Finset.mem_sigma] at hp hp2
    have hq0 : 0 < q := by simp only [Q1, mem_filter, mem_Icc] at hp; omega
    have hq20 : 0 < q2 := by simp only [Q1, mem_filter, mem_Icc] at hp2; omega
    have hqq : q = q / Nat.gcd h q * Nat.gcd h q := (Nat.div_mul_cancel (Nat.gcd_dvd_right h q)).symm
    have hqq2 : q2 = q2 / Nat.gcd h2 q2 * Nat.gcd h2 q2 := (Nat.div_mul_cancel (Nat.gcd_dvd_right h2 q2)).symm
    have hhh : h = h / Nat.gcd h q * Nat.gcd h q := (Nat.div_mul_cancel (Nat.gcd_dvd_left h q)).symm
    have hhh2 : h2 = h2 / Nat.gcd h2 q2 * Nat.gcd h2 q2 := (Nat.div_mul_cancel (Nat.gcd_dvd_left h2 q2)).symm
    have hqe : q = q2 := by rw [hqq, hqq2, e1, e3]
    subst hqe
    have hhe : h = h2 := by
      have e2' : h / Nat.gcd h q = h2 / Nat.gcd h2 q := by simpa using e2
      rw [hhh, hhh2, e2', e3]
    subst hhe
    rfl
  calc ∑ p ∈ P, f p ≤ ∑ p ∈ P, F (φ p) := Finset.sum_le_sum (fun p hp => (hmem p hp).2)
    _ = ∑ x ∈ P.image φ, F x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ T, F x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx; exact (hmem p hp).1
        · intro x _ _; exact hF0 x


/-- `√(RX) · √(√(R Y γ⁴) · √(RX)) ≤ R X Y γ` for `X, Y ≥ 1`, `R, γ ≥ 0`. -/
theorem sqrt_combo (R X Y γ : ℝ) (hR : 0 ≤ R) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hγ : 0 ≤ γ) :
    Real.sqrt (R * X) * Real.sqrt (Real.sqrt (R * Y * γ ^ 4) * Real.sqrt (R * X)) ≤ R * X * Y * γ := by
  have hX0 : 0 ≤ X := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h1 : Real.sqrt (R * Y * γ ^ 4) = Real.sqrt (R * Y) * γ ^ 2 := by
    rw [Real.sqrt_mul (by positivity), show γ ^ 4 = (γ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h2 : Real.sqrt (R * Y) * Real.sqrt (R * X) = R * Real.sqrt (X * Y) := by
    rw [← Real.sqrt_mul (by positivity), show R * Y * (R * X) = R ^ 2 * (X * Y) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hR]
  have h3 : Real.sqrt (X * Y) ≤ X * Y := by
    have hXY : 1 ≤ X * Y := by nlinarith
    calc Real.sqrt (X * Y) ≤ Real.sqrt ((X * Y) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = X * Y := Real.sqrt_sq (by positivity)
  have hprod : Real.sqrt (R * X) * Real.sqrt (Real.sqrt (R * Y * γ ^ 4) * Real.sqrt (R * X)) =
      Real.sqrt (R * X * (γ ^ 2 * (R * Real.sqrt (X * Y)))) := by
    rw [h1, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [← h2]; ring
  rw [hprod]
  calc Real.sqrt (R * X * (γ ^ 2 * (R * Real.sqrt (X * Y))))
      ≤ Real.sqrt ((R * X * Y * γ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have : R * X * (γ ^ 2 * (R * Real.sqrt (X * Y))) ≤ R * X * (γ ^ 2 * (R * (X * Y))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h3 hR
        calc _ ≤ R * X * (γ ^ 2 * (R * (X * Y))) := this
          _ = R ^ 2 * X ^ 2 * Y * γ ^ 2 := by ring
          _ ≤ R ^ 2 * X ^ 2 * Y ^ 2 * γ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith
          _ = (R * X * Y * γ) ^ 2 := by ring
    _ = R * X * Y * γ := Real.sqrt_sq (by positivity)

theorem gam_pow_four (b : ℕ) : gam b ^ 4 = (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) := by
  unfold gam
  have h0 : 0 ≤ (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) := by positivity
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h0]

/-- `#{q ∈ Qs : q ∣ w} ≤ C_e |w|^e`. -/
theorem card_filter_dvd_le (Qs : Finset ℕ) (hQ : ∀ q ∈ Qs, 0 < q) (e Ce : ℝ)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ e) (he : 0 ≤ e)
    (w : ℤ) (hw : w ≠ 0) (W : ℝ) (hwW : (|w| : ℝ) ≤ W) :
    (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ Ce * W ^ e := by
  have hn : 1 ≤ w.natAbs := Int.natAbs_pos.2 hw
  have hsub : Qs.filter (fun q : ℕ => (q : ℤ) ∣ w) ⊆ w.natAbs.divisors := by
    intro q hq
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    exact Int.natCast_dvd.1 (mem_filter.1 hq).2
  have h1 : (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ (#w.natAbs.divisors : ℝ) := by
    exact_mod_cast card_le_card hsub
  have h2 := hCe w.natAbs hn
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl; simp at this; linarith
  refine h1.trans (h2.trans (mul_le_mul_of_nonneg_left ?_ hCe0))
  have : ((w.natAbs : ℕ) : ℝ) = |(w : ℝ)| := by rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]
  exact Real.rpow_le_rpow (abs_nonneg _) hwW he

set_option maxHeartbeats 1600000 in
/-- **One dyadic block of moduli** in the level sum: weight, Col factor and Farey block. -/
theorem level_block_gen (b N ℓ a R : ℕ) (hb : 2 ≤ b) (ha : a ≤ ℓ) (hlay : 2 * ℓ + a + 1 ≤ N)
    (hR : 1 ≤ R) (h2R : 2 * R < b ^ ℓ) (hbl : b ^ ℓ ≤ 2 * b * R)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q < 2 * R ∧ Nat.Coprime q (bigB b)) (hcard : #Qs ≤ R)
    (ε Cw e Ce : ℝ) (hε : 0 ≤ ε) (he : 0 ≤ e)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ ε)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ e)
    (colF : ℝ) (hcol0 : 0 ≤ colF) (β : ℝ)
    (hcol : ∀ q ∈ Qs, ∀ h ∈ redRes q, ∏ n ∈ Ico 1 (N - ℓ - a - ℓ),
      Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β))) ≤ colF) :
    ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β))) ≤
      Cw * (2 * (R : ℝ)) ^ ε * colF *
        (1 + 2 * (Ce * (((8 * b * (ℓ + a + ℓ) * b ^ (2 * (N - (N - ℓ - a - ℓ))) + 1 : ℕ) : ℝ)) ^ e)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ a := by
  classical
  set w0 := N - ℓ - a - ℓ with hw0
  set Wm : ℝ := ((8 * b * (ℓ + a + ℓ) * b ^ (2 * (N - w0)) + 1 : ℕ) : ℝ) with hWm
  set T : ℝ := Ce * Wm ^ e with hT
  have hCe0 : 0 ≤ Ce := by have := hCe 1 le_rfl; simp at this; linarith
  have hCw0 : 0 ≤ Cw := by have := hCw 1 le_rfl; simp at this; linarith
  have hT0 : 0 ≤ T := by positivity
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbl' : (2 * (R : ℝ)) < (b : ℝ) ^ ℓ := by exact_mod_cast h2R
  have hbl2 : ((b : ℝ) ^ ℓ) ≤ 2 * b * R := by exact_mod_cast hbl
  set Pw : ℕ → ℕ → ℝ := fun q h => ∏ n ∈ Ico w0 N, Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β)))
  -- step 1: split off the outer digits
  have hsplit : ∀ q ∈ Qs, ∀ h ∈ redRes q,
      ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β))) ≤ colF * Pw q h := by
    intro q hq h hh
    rw [← Finset.prod_Ico_consecutive _ (by omega : 1 ≤ w0) (by omega : w0 ≤ N)]
    exact mul_le_mul_of_nonneg_right (hcol q hq h hh)
      (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _))
  -- step 2: the weight
  have hweight : ∀ q ∈ Qs, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤
      Cw * (2 * (R : ℝ)) ^ ε / R := by
    intro q hq
    obtain ⟨hq1, hq2, _⟩ := hQs q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hqR : (R : ℝ) ≤ q := by exact_mod_cast hq1
    have hq2R : (q : ℝ) ≤ 2 * R := by exact_mod_cast hq2.le
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q ≤ Cw * (q : ℝ) ^ ε / q :=
          div_le_div_of_nonneg_right (hCw q (by omega)) hq0.le
      _ ≤ Cw * (2 * (R : ℝ)) ^ ε / q := by
          apply div_le_div_of_nonneg_right _ hq0.le
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq0.le hq2R hε) hCw0
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hR0 hqR
  -- step 3: Farey block
  have hT' : ∀ w : ℤ, w ≠ 0 →
      |w| ≤ ((8 * b * (ℓ + a + ℓ) * b ^ (2 * (N - (N - ℓ - a - ℓ))) + 1 : ℕ) : ℤ) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ T := by
    intro w hw hwW
    apply card_filter_dvd_le Qs (fun q hq => by have := (hQs q hq).1; omega) e Ce hCe he w hw Wm
    have : ((|w| : ℤ) : ℝ) ≤ Wm := by rw [hWm]; exact_mod_cast hwW
    simpa using this
  have hQs' : ∀ q ∈ Qs, R ≤ q ∧ q ≤ 2 * R ∧ Nat.Coprime q b := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hQs q hq
    refine ⟨h1, h2.le, ?_⟩
    have hbB : b ∣ bigB b := by rw [bigB_eq b (by omega)]; exact ⟨(b - 1) * (b + 1), by ring⟩
    exact Nat.Coprime.coprime_dvd_right hbB h3
  have hFB := farey_block b N ℓ a a ℓ R hb ha (by omega) hR Qs hQs' T hT0 hT' β
  -- step 4: simplify the Farey bound
  set g' : ℝ := (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3) with hg'
  have hg'eq : g' = gam b ^ 4 / b := by
    rw [hg', gam_pow_four]; field_simp
  have hγ0 : 0 ≤ gam b := gam_nonneg b
  have hγ1 : gam b ^ 4 ≤ 1 := by
    rw [gam_pow_four, div_le_one (by positivity)]; nlinarith
  have hρ : g' ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹ = (gam b ^ a) ^ 4 / (b : ℝ) ^ ℓ := by
    rw [hg'eq, div_pow, ← pow_mul, mul_comm 4 a, pow_mul]
    have hpow : (b : ℝ) ^ ℓ = (b : ℝ) ^ a * (b : ℝ) ^ (ℓ - a) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]; field_simp
  have hX : 2 * R * (#Qs * ((b : ℝ) ^ ℓ)⁻¹ + T) ≤ R * (1 + 2 * T) := by
    have : (#Qs : ℝ) * ((b : ℝ) ^ ℓ)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have : (#Qs : ℝ) ≤ R := by exact_mod_cast hcard
      linarith
    nlinarith
  have hX3 : 2 * R * (#Qs * (g' ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹) + T) ≤ R * (1 + 2 * T) := by
    rw [hρ]
    have h1 : (gam b ^ a) ^ 4 / (b : ℝ) ^ ℓ ≤ ((b : ℝ) ^ ℓ)⁻¹ := by
      rw [div_eq_mul_inv]
      apply mul_le_of_le_one_left (by positivity)
      rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_one₀ (by positivity) hγ1
    have : (#Qs : ℝ) * ((gam b ^ a) ^ 4 / (b : ℝ) ^ ℓ) ≤ (#Qs : ℝ) * ((b : ℝ) ^ ℓ)⁻¹ :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    have h2 := hX
    nlinarith
  have hY : (4 * ((4 * b * ℓ * b ^ (2 * (N - (N - ℓ))) + 1 : ℕ) : ℝ) + 12 * (R : ℝ) ^ 2 + 2) *
      (g' ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹) ≤ R * (32 * (b : ℝ) ^ 2 * ℓ + 12) * (gam b ^ a) ^ 4 := by
    rw [hρ, show N - (N - ℓ) = ℓ by omega]
    push_cast
    have hbl0 : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
    rw [mul_div_assoc', div_le_iff₀ hbl0]
    have hγ4 : 0 ≤ (gam b ^ a) ^ 4 := by positivity
    have hb2l : (b : ℝ) ^ (2 * ℓ) = (b : ℝ) ^ ℓ * (b : ℝ) ^ ℓ := by rw [two_mul, pow_add]
    rw [hb2l]
    have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    have key : 4 * (4 * (b : ℝ) * ℓ * ((b : ℝ) ^ ℓ * (b : ℝ) ^ ℓ) + 1) + 12 * (R : ℝ) ^ 2 + 2 ≤
        R * (32 * (b : ℝ) ^ 2 * ℓ + 12) * (b : ℝ) ^ ℓ := by
      have h1 : 16 * (b : ℝ) * ℓ * ((b : ℝ) ^ ℓ * (b : ℝ) ^ ℓ) ≤ 32 * (b : ℝ) ^ 2 * ℓ * R * (b : ℝ) ^ ℓ := by
        have := mul_le_mul_of_nonneg_left hbl2 (by positivity : (0 : ℝ) ≤ 16 * (b : ℝ) * ℓ * (b : ℝ) ^ ℓ)
        nlinarith
      have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
      have h2 : 12 * (R : ℝ) ^ 2 + 6 ≤ 12 * (R : ℝ) * (b : ℝ) ^ ℓ := by
        nlinarith [mul_lt_mul_of_pos_left hbl' (by positivity : (0 : ℝ) < 12 * R)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right key hγ4]
  have hFB' : Real.sqrt (2 * R * (#Qs * ((b : ℝ) ^ ℓ)⁻¹ + T)) *
      Real.sqrt (Real.sqrt ((4 * ((4 * b * ℓ * b ^ (2 * (N - (N - ℓ))) + 1 : ℕ) : ℝ) +
          12 * (R : ℝ) ^ 2 + 2) * (g' ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹)) *
        Real.sqrt (2 * R * (#Qs * (g' ^ a * ((b : ℝ) ^ (ℓ - a))⁻¹) + T))) ≤
      R * (1 + 2 * T) * (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ a := by
    have hX1 : 1 ≤ 1 + 2 * T := by linarith
    have hY1 : 1 ≤ 32 * (b : ℝ) ^ 2 * ℓ + 12 := by have : (0 : ℝ) ≤ 32 * (b : ℝ) ^ 2 * ℓ := by positivity
                                                   linarith
    calc _ ≤ Real.sqrt (R * (1 + 2 * T)) * Real.sqrt (Real.sqrt (R * (32 * (b : ℝ) ^ 2 * ℓ + 12) *
          (gam b ^ a) ^ 4) * Real.sqrt (R * (1 + 2 * T))) := by
          apply mul_le_mul (Real.sqrt_le_sqrt hX) _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (Real.sqrt_le_sqrt hY) (Real.sqrt_le_sqrt hX3) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ ≤ _ := sqrt_combo R (1 + 2 * T) (32 * (b : ℝ) ^ 2 * ℓ + 12) (gam b ^ a) hR0.le hX1 hY1
          (by positivity)
  -- step 5: assemble
  calc ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + β)))
      ≤ ∑ q ∈ Qs, (Cw * (2 * (R : ℝ)) ^ ε / R) * ∑ h ∈ redRes q, colF * Pw q h := by
        apply Finset.sum_le_sum; intro q hq
        apply mul_le_mul (hweight q hq) (Finset.sum_le_sum (fun h hh => hsplit q hq h hh))
          (Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)))
          (by positivity)
    _ = (Cw * (2 * (R : ℝ)) ^ ε / R) * colF * ∑ q ∈ Qs, ∑ h ∈ redRes q, Pw q h := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro h _; ring
    _ ≤ (Cw * (2 * (R : ℝ)) ^ ε / R) * colF *
          (R * (1 + 2 * T) * (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ a) := by
        apply mul_le_mul_of_nonneg_left (hFB.trans hFB') (by positivity)
    _ = Cw * (2 * (R : ℝ)) ^ ε * colF * (1 + 2 * T) * (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ a *
          ((R : ℝ) / R) := by ring
    _ = _ := by rw [div_self hR0.ne', mul_one]

/-! ## Asymptotic block bounds -/
/-- `c_b` of Col's bound. -/
noncomputable def colC (b : ℕ) : ℝ := ((b : ℝ) - 1) / ((b : ℝ) ^ 6 * ((b : ℝ) + 1) ^ 2)

theorem colC_pos (b : ℕ) (hb : 2 ≤ b) : 0 < colC b := by
  unfold colC
  have : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  positivity

/-- Regime I (`3ℓ + 1 ≤ N`): window of `3ℓ` digits plus Col's bound. -/
theorem block_regime_I (b N ℓ R : ℕ) (k : ℤ) (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) (hlay : 3 * ℓ + 1 ≤ N)
    (hR : 1 ≤ R) (h2R : 2 * R < b ^ ℓ) (hbl : b ^ ℓ ≤ 2 * b * R)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q < 2 * R ∧ Nat.Coprime q (bigB b) ∧ 2 ≤ q)
    (hcard : #Qs ≤ R) (ε Cw e Ce : ℝ) (hε : 0 ≤ ε) (he : 0 ≤ e)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ ε)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ e) :
    ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) ≤
      Cw * (2 * (R : ℝ)) ^ ε * Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ)) *
        (1 + 2 * (Ce * (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (N - (N - ℓ - ℓ - ℓ))) + 1 : ℕ) : ℝ)) ^ e)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ ℓ := by
  apply level_block_gen b N ℓ ℓ R hb le_rfl (by omega) hR h2R hbl Qs
    (fun q hq => ⟨(hQs q hq).1, (hQs q hq).2.1, (hQs q hq).2.2.1⟩) hcard ε Cw e Ce hε he hCw hCe
    _ (Real.exp_nonneg _) _
  intro q hq h hh
  obtain ⟨hq1, hq2, hqB, hq2'⟩ := hQs q hq
  have hhq : Nat.Coprime h q := (Finset.mem_filter.1 hh).2
  have hcol := col_bound b N (N - 3 * ℓ - 1) q h k hb hq2' (by omega) hhq hqB
  rw [show N - 3 * ℓ - 1 + 1 = N - ℓ - ℓ - ℓ by omega] at hcol
  refine hcol.trans ?_
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonpos_left _ (by have := colC_pos b hb; unfold colC at this; linarith)
  -- `⌊(M−1)/ℓ⌋ ≤ ⌊(M−1)/(log_b q + 1)⌋` since `log_b q + 1 ≤ ℓ`
  have hlog : Nat.log b q + 1 ≤ ℓ := by
    have : q < b ^ ℓ := by omega
    have := Nat.log_lt_of_lt_pow (by omega) this
    omega
  have : (N - 3 * ℓ - 2) / ℓ ≤ (N - 3 * ℓ - 1 - 1) / (Nat.log b q + 1) := by
    rw [show N - 3 * ℓ - 1 - 1 = N - 3 * ℓ - 2 by omega]
    exact Nat.div_le_div_left hlog (by omega)
  exact_mod_cast this

/-- Regime II (`N ≤ 3ℓ`, `2ℓ + 1 ≤ N`): full window, `a = N − 1 − 2ℓ`. -/
theorem block_regime_II (b N ℓ R : ℕ) (k : ℤ) (hb : 2 ≤ b) (hl3 : N ≤ 3 * ℓ) (hl2 : 2 * ℓ + 1 ≤ N)
    (hR : 1 ≤ R) (h2R : 2 * R < b ^ ℓ) (hbl : b ^ ℓ ≤ 2 * b * R)
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, R ≤ q ∧ q < 2 * R ∧ Nat.Coprime q (bigB b) ∧ 2 ≤ q)
    (hcard : #Qs ≤ R) (ε Cw e Ce : ℝ) (hε : 0 ≤ ε) (he : 0 ≤ e)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ ε)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ e) :
    ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) ≤
      Cw * (2 * (R : ℝ)) ^ ε * 1 *
        (1 + 2 * (Ce * (((8 * b * (ℓ + (N - 1 - 2 * ℓ) + ℓ) *
          b ^ (2 * (N - (N - ℓ - (N - 1 - 2 * ℓ) - ℓ))) + 1 : ℕ) : ℝ)) ^ e)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ (N - 1 - 2 * ℓ) := by
  apply level_block_gen b N ℓ (N - 1 - 2 * ℓ) R hb (by omega) (by omega) hR h2R hbl Qs
    (fun q hq => ⟨(hQs q hq).1, (hQs q hq).2.1, (hQs q hq).2.2.1⟩) hcard ε Cw e Ce hε he hCw hCe
    1 zero_le_one _
  intro q _ h _
  rw [show N - ℓ - (N - 1 - 2 * ℓ) - ℓ = 1 by omega]
  simp

/-- Polynomial times geometric decay is eventually small. -/
theorem eventually_poly_geom (C : ℝ) (k : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, C * ((n : ℝ) + 1) ^ k * ρ ^ n ≤ ε := by
  have hγ : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one k hγ
  have hC : 0 < 2 ^ k * |C| + 1 := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 ht).2 (ε / (2 ^ k * |C| + 1)) (by positivity))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hg0 : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  calc C * ((n : ℝ) + 1) ^ k * ρ ^ n ≤ |C| * (2 ^ k * (n : ℝ) ^ k) * ρ ^ n := by
        apply mul_le_mul_of_nonneg_right _ hg0
        calc C * ((n : ℝ) + 1) ^ k ≤ |C| * ((n : ℝ) + 1) ^ k :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          _ ≤ |C| * (2 ^ k * (n : ℝ) ^ k) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = 2 ^ k * |C| * ((n : ℝ) ^ k * ρ ^ n) := by ring
    _ ≤ (2 ^ k * |C| + 1) * (ε / (2 ^ k * |C| + 1)) := by
        apply mul_le_mul (by linarith) h1.le (by positivity) (by positivity)
    _ = ε := by field_simp

theorem gam_pos (b : ℕ) (hb : 1 ≤ b) : 0 < gam b := by
  unfold gam
  have : (0 : ℝ) < b := by exact_mod_cast hb
  apply Real.sqrt_pos.2; apply Real.sqrt_pos.2
  positivity

/-- Exponent bookkeeping constants. -/
noncomputable def m0 (b : ℕ) : ℝ := min (colC b / 14) (-Real.log (gam b) / 300)
noncomputable def rhoL (b : ℕ) : ℝ := max (Real.exp (-colC b / 2)) (Real.sqrt (gam b))

theorem m0_pos (b : ℕ) (hb : 2 ≤ b) : 0 < m0 b := by
  unfold m0
  apply lt_min
  · have := colC_pos b hb; positivity
  · have h1 := gam_lt_one b hb
    have h0 := gam_pos b (by omega)
    have : Real.log (gam b) < 0 := Real.log_neg h0 h1
    linarith

theorem rhoL_lt_one (b : ℕ) (hb : 2 ≤ b) : rhoL b < 1 := by
  unfold rhoL
  apply max_lt
  · have := colC_pos b hb
    calc Real.exp (-colC b / 2) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  · rw [Real.sqrt_lt' one_pos, one_pow]; exact gam_lt_one b hb

theorem rhoL_nonneg (b : ℕ) : 0 ≤ rhoL b := le_trans (Real.exp_nonneg _) (le_max_left _ _)

/-- `u = exp(m0)` satisfies `u⁷ e^{−c} ≤ e^{−c/2}` and `u^150 γ ≤ √γ`. -/
theorem u_bounds (b : ℕ) (hb : 2 ≤ b) :
    Real.exp (m0 b) ^ 7 * Real.exp (-colC b) ≤ rhoL b ∧
    Real.exp (m0 b) ^ 150 * gam b ≤ rhoL b := by
  have hc := colC_pos b hb
  have hγ0 := gam_pos b (by omega)
  constructor
  · calc Real.exp (m0 b) ^ 7 * Real.exp (-colC b) = Real.exp (7 * m0 b - colC b) := by
          rw [← Real.exp_natCast_mul, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ Real.exp (-colC b / 2) := by
          apply Real.exp_le_exp.2
          have : m0 b ≤ colC b / 14 := min_le_left _ _
          linarith
      _ ≤ rhoL b := le_max_left _ _
  · calc Real.exp (m0 b) ^ 150 * gam b = Real.exp (150 * m0 b + Real.log (gam b)) := by
          rw [← Real.exp_natCast_mul, Real.exp_add, Real.exp_log hγ0]; push_cast; ring_nf
      _ ≤ Real.exp (Real.log (gam b) / 2) := by
          apply Real.exp_le_exp.2
          have : m0 b ≤ -Real.log (gam b) / 300 := min_le_right _ _
          linarith
      _ = Real.sqrt (gam b) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hγ0]; ring_nf
      _ ≤ rhoL b := le_max_right _ _

noncomputable def del0 (b : ℕ) : ℝ := m0 b / Real.log b

theorem del0_pos (b : ℕ) (hb : 2 ≤ b) : 0 < del0 b := by
  unfold del0
  have : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  have := m0_pos b hb
  positivity

theorem rpow_del0 (b : ℕ) (hb : 2 ≤ b) (t : ℕ) :
    ((b : ℝ) ^ t) ^ del0 b = Real.exp (m0 b) ^ t := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hl : Real.log b ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < b))).ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, Real.rpow_def_of_pos hb0, ← Real.exp_natCast_mul]
  congr 1; unfold del0; field_simp

theorem del0_le_one (b : ℕ) (hb : 2 ≤ b) : del0 b ≤ 1 := by
  unfold del0
  have hl : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hc : colC b ≤ 1 := by
    unfold colC
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    rw [div_le_one (by positivity)]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) this 6]
  have hm : m0 b ≤ 1 / 14 := le_trans (min_le_left _ _) (by linarith)
  rw [div_le_one (by linarith)]; linarith

/-- `x^δ ≤ x` for `x ≥ 1`, `0 ≤ δ ≤ 1`. -/
theorem rpow_le_self_of_one_le (x δ : ℝ) (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : x ^ δ ≤ x := by
  calc x ^ δ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hδ1
    _ = x := Real.rpow_one x

/-- The common shape `K₀ ℓ² u^{7ℓ} γ^ℓ colF` in regime I. -/
theorem bnd_I_shape (b N ℓ R : ℕ) (hb : 2 ≤ b) (hℓ : 1 ≤ ℓ) (hlay : 3 * ℓ + 1 ≤ N)
    (h2R : 2 * R ≤ b ^ ℓ) (Cw Ce colF : ℝ) (hCw : 0 ≤ Cw) (hCe : 0 ≤ Ce) (hcol : 0 ≤ colF) :
    Cw * (2 * (R : ℝ)) ^ del0 b * colF *
        (1 + 2 * (Ce * (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (N - (N - ℓ - ℓ - ℓ))) + 1 : ℕ) : ℝ)) ^ del0 b)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ ℓ ≤
      Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * (ℓ : ℝ) ^ 2 *
        (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ * colF := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set u := Real.exp (m0 b) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (le_of_lt (m0_pos b hb))
  have hd0 := (del0_pos b hb).le
  have hd1 := del0_le_one b hb
  have hA : (2 * (R : ℝ)) ^ del0 b ≤ u ^ ℓ := by
    rw [← rpow_del0 b hb ℓ]
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast h2R) hd0
  have hN3 : N - (N - ℓ - ℓ - ℓ) = 3 * ℓ := by omega
  rw [hN3]
  have hWv : (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (3 * ℓ)) + 1 : ℕ) : ℝ)) ≤ 25 * b * ℓ * (b : ℝ) ^ (6 * ℓ) := by
    push_cast
    have h1 : (1 : ℝ) ≤ b * ℓ * (b : ℝ) ^ (6 * ℓ) := by
      have h6 : (1 : ℝ) ≤ (b : ℝ) ^ (6 * ℓ) := one_le_pow₀ hb1
      have hbl : (1 : ℝ) ≤ b * ℓ := one_le_mul_of_one_le_of_one_le hb1 hℓ1
      exact one_le_mul_of_one_le_of_one_le hbl h6
    rw [show 2 * (3 * ℓ) = 6 * ℓ by ring]
    nlinarith
  have hW : (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (3 * ℓ)) + 1 : ℕ) : ℝ)) ^ del0 b ≤ 25 * b * ℓ * u ^ (6 * ℓ) := by
    calc _ ≤ (25 * b * ℓ * (b : ℝ) ^ (6 * ℓ)) ^ del0 b :=
          Real.rpow_le_rpow (by positivity) hWv hd0
      _ = (25 * b * ℓ : ℝ) ^ del0 b * ((b : ℝ) ^ (6 * ℓ)) ^ del0 b :=
          Real.mul_rpow (by positivity) (by positivity)
      _ ≤ 25 * b * ℓ * u ^ (6 * ℓ) := by
          rw [rpow_del0 b hb]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply rpow_le_self_of_one_le _ _ (by nlinarith) hd0 hd1
  have hT : 1 + 2 * (Ce * (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (3 * ℓ)) + 1 : ℕ) : ℝ)) ^ del0 b) ≤
      (1 + 50 * Ce * b) * ℓ * u ^ (6 * ℓ) := by
    have hu6 : 1 ≤ u ^ (6 * ℓ) := one_le_pow₀ hu1
    have : 2 * (Ce * (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (3 * ℓ)) + 1 : ℕ) : ℝ)) ^ del0 b) ≤
        2 * (Ce * (25 * b * ℓ * u ^ (6 * ℓ))) := by gcongr
    nlinarith
  have hY : 32 * (b : ℝ) ^ 2 * ℓ + 12 ≤ (32 * (b : ℝ) ^ 2 + 12) * ℓ := by nlinarith
  have hγ0 := (gam_pos b (by omega)).le
  calc Cw * (2 * (R : ℝ)) ^ del0 b * colF *
        (1 + 2 * (Ce * (((8 * b * (ℓ + ℓ + ℓ) * b ^ (2 * (3 * ℓ)) + 1 : ℕ) : ℝ)) ^ del0 b)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ ℓ
      ≤ Cw * u ^ ℓ * colF * ((1 + 50 * Ce * b) * ℓ * u ^ (6 * ℓ)) *
        ((32 * (b : ℝ) ^ 2 + 12) * ℓ) * gam b ^ ℓ := by
        gcongr
    _ = Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * (ℓ : ℝ) ^ 2 *
          (u ^ 7 * gam b) ^ ℓ * colF := by
        rw [mul_pow, ← pow_mul, show 6 * ℓ = ℓ * 6 by ring]
        ring

/-- The common shape in regime II. -/
theorem bnd_II_shape (b N ℓ R : ℕ) (hb : 2 ≤ b) (hl2 : 2 * ℓ + 1 ≤ N)
    (h2R : 2 * R ≤ b ^ ℓ) (Cw Ce : ℝ) (hCw : 0 ≤ Cw) (hCe : 0 ≤ Ce) :
    Cw * (2 * (R : ℝ)) ^ del0 b * 1 *
        (1 + 2 * (Ce * (((8 * b * (ℓ + (N - 1 - 2 * ℓ) + ℓ) *
          b ^ (2 * (N - (N - ℓ - (N - 1 - 2 * ℓ) - ℓ))) + 1 : ℕ) : ℝ)) ^ del0 b)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ (N - 1 - 2 * ℓ) ≤
      Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * (N : ℝ) ^ 2 *
        Real.exp (m0 b) ^ (3 * N) * gam b ^ (N - 1 - 2 * ℓ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  set u := Real.exp (m0 b) with hu
  have hu1 : 1 ≤ u := Real.one_le_exp (le_of_lt (m0_pos b hb))
  have hd0 := (del0_pos b hb).le
  have hd1 := del0_le_one b hb
  have hA : (2 * (R : ℝ)) ^ del0 b ≤ u ^ N := by
    calc (2 * (R : ℝ)) ^ del0 b ≤ ((b : ℝ) ^ ℓ) ^ del0 b :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast h2R) hd0
      _ = u ^ ℓ := rpow_del0 b hb ℓ
      _ ≤ u ^ N := pow_le_pow_right₀ hu1 (by omega)
  have e1 : ℓ + (N - 1 - 2 * ℓ) + ℓ = N - 1 := by omega
  have e2 : N - (N - ℓ - (N - 1 - 2 * ℓ) - ℓ) = N - 1 := by omega
  rw [e1, e2]
  have hWv : (((8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 : ℕ) : ℝ)) ≤ 9 * b * N * (b : ℝ) ^ (2 * N) := by
    have h1 : 8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 ≤ 9 * b * N * b ^ (2 * N) := by
      have hp : b ^ (2 * (N - 1)) ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
      have hq : 1 ≤ b * N * b ^ (2 * N) := by
        have h1 := Nat.one_le_pow (2 * N) b (by omega)
        have h2 : 1 * 1 ≤ b * N := Nat.mul_le_mul (by omega : 1 ≤ b) (by omega : 1 ≤ N)
        calc 1 = 1 * 1 := rfl
          _ ≤ b * N * b ^ (2 * N) := Nat.mul_le_mul (by simpa using h2) h1
      have h8 : 8 * b * (N - 1) * b ^ (2 * (N - 1)) ≤ 8 * b * N * b ^ (2 * N) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hp
      have h9 : 9 * b * N * b ^ (2 * N) = 8 * b * N * b ^ (2 * N) + b * N * b ^ (2 * N) := by ring
      omega
    exact_mod_cast h1
  have hW : (((8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 : ℕ) : ℝ)) ^ del0 b ≤ 9 * b * N * u ^ (2 * N) := by
    calc _ ≤ (9 * b * N * (b : ℝ) ^ (2 * N)) ^ del0 b := Real.rpow_le_rpow (by positivity) hWv hd0
      _ = (9 * b * N : ℝ) ^ del0 b * ((b : ℝ) ^ (2 * N)) ^ del0 b :=
          Real.mul_rpow (by positivity) (by positivity)
      _ ≤ 9 * b * N * u ^ (2 * N) := by
          rw [rpow_del0 b hb]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply rpow_le_self_of_one_le _ _ (by nlinarith) hd0 hd1
  have hT : 1 + 2 * (Ce * (((8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 : ℕ) : ℝ)) ^ del0 b) ≤
      (1 + 18 * Ce * b) * N * u ^ (2 * N) := by
    have hu6 : 1 ≤ u ^ (2 * N) := one_le_pow₀ hu1
    have : 2 * (Ce * (((8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 : ℕ) : ℝ)) ^ del0 b) ≤
        2 * (Ce * (9 * b * N * u ^ (2 * N))) := by gcongr
    nlinarith
  have hY : 32 * (b : ℝ) ^ 2 * ℓ + 12 ≤ (32 * (b : ℝ) ^ 2 + 12) * N := by
    have : (ℓ : ℝ) ≤ N := by exact_mod_cast (by omega : ℓ ≤ N)
    nlinarith
  have hγ0 := (gam_pos b (by omega)).le
  calc Cw * (2 * (R : ℝ)) ^ del0 b * 1 *
        (1 + 2 * (Ce * (((8 * b * (N - 1) * b ^ (2 * (N - 1)) + 1 : ℕ) : ℝ)) ^ del0 b)) *
        (32 * (b : ℝ) ^ 2 * ℓ + 12) * gam b ^ (N - 1 - 2 * ℓ)
      ≤ Cw * u ^ N * 1 * ((1 + 18 * Ce * b) * N * u ^ (2 * N)) *
        ((32 * (b : ℝ) ^ 2 + 12) * N) * gam b ^ (N - 1 - 2 * ℓ) := by
        gcongr
    _ = _ := by rw [show 3 * N = N + 2 * N by ring, pow_add]; ring

/-- The digit-length bound for the block of `2^i`: `25 ℓ ≤ 12 N + 56`. -/
theorem ell_bound (b N i : ℕ) (hb : 2 ≤ b)
    (hiD : (2 : ℝ) ^ (i + 1) ≤ 2 * ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25)) :
    25 * (Nat.log b (2 ^ (i + 1)) + 1) ≤ 12 * N + 56 := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  set L := Nat.log b (2 ^ (i + 1))
  have h1 : ((b ^ L : ℕ) : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
    exact_mod_cast Nat.pow_log_le_self b (by positivity)
  have h2 : (b : ℝ) ^ ((L : ℕ) : ℝ) ≤ (b : ℝ) ^ (1 + ((2 * N + 1 : ℕ) : ℝ) * (6 / 25)) := by
    rw [Real.rpow_natCast, Real.rpow_add hb0, Real.rpow_one, Real.rpow_natCast_mul hb0.le]
    push_cast at h1 ⊢
    have h2' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    calc (b : ℝ) ^ L ≤ (2 : ℝ) ^ (i + 1) := h1
      _ ≤ 2 * ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25) := hiD
      _ ≤ b * ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25) := by
          apply mul_le_mul_of_nonneg_right h2' (by positivity)
  rw [Real.rpow_le_rpow_left_iff hb1] at h2
  push_cast at h2
  have : (25 * ((L : ℝ) + 1)) ≤ 12 * N + 56 := by nlinarith
  exact_mod_cast this

theorem nat_aux_sq (n : ℕ) (hn : 2 ≤ n) : (n - 2) * n + 2 ≤ n * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 2 = m by omega]; nlinarith

/-- **Every dyadic block** is `≤ K (n+1)⁴ rhoL b^n` with `n = ⌊√N⌋`. -/
theorem block_le_geom (b : ℕ) (hb : 2 ≤ b) (Cw Ce : ℝ) (hCw0 : 0 ≤ Cw) (hCe0 : 0 ≤ Ce)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ del0 b)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ del0 b)
    (N i : ℕ) (hN : 2500 ≤ N) (hi1 : 1 ≤ i)
    (hiD : (2 : ℝ) ^ (i + 1) ≤ 2 * ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25))
    (Qs : Finset ℕ) (hQs : ∀ q ∈ Qs, 2 ^ i ≤ q ∧ q < 2 ^ (i + 1) ∧ Nat.Coprime q (bigB b) ∧ 2 ≤ q)
    (hcard : #Qs ≤ 2 ^ i) (k : ℤ) :
    ∑ q ∈ Qs, ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) ≤
      (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
        (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N) := by
  set R := 2 ^ i with hRdef
  set ℓ := Nat.log b (2 ^ (i + 1)) + 1 with hℓdef
  set n := Nat.sqrt N with hn
  have hc := colC_pos b hb
  have hu1 : 1 ≤ Real.exp (m0 b) := Real.one_le_exp (le_of_lt (m0_pos b hb))
  have hρ0 : 0 ≤ rhoL b := rhoL_nonneg b
  have hρ1 : rhoL b ≤ 1 := (rhoL_lt_one b hb).le
  have hγ0 : 0 ≤ gam b := (gam_pos b (by omega)).le
  have hγ1 : gam b ≤ 1 := (gam_lt_one b hb).le
  obtain ⟨hu7, hu150⟩ := u_bounds b hb
  have hR1 : 1 ≤ R := Nat.one_le_two_pow
  have h2R : 2 * R < b ^ ℓ := by
    rw [hRdef, ← pow_succ']; exact Nat.lt_pow_succ_log_self (by omega) _
  have hbl : b ^ ℓ ≤ 2 * b * R := by
    have hL := Nat.pow_log_le_self b (by positivity : 2 ^ (i + 1) ≠ 0)
    calc b ^ ℓ = b ^ Nat.log b (2 ^ (i + 1)) * b := pow_succ _ _
      _ ≤ 2 ^ (i + 1) * b := Nat.mul_le_mul_right _ hL
      _ = 2 * b * R := by rw [hRdef]; ring
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓN := ell_bound b N i hb hiD
  have hnN : n ^ 2 ≤ N := by rw [hn]; exact Nat.sqrt_le' N
  have hNn : N < (n + 1) ^ 2 := by rw [hn]; exact Nat.lt_succ_sqrt' N
  have hNR : (N : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
    have : (N : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by exact_mod_cast hNn.le
    calc (N : ℝ) ^ 2 ≤ (((n : ℝ) + 1) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = _ := by ring
  have hQs' : ∀ q ∈ Qs, R ≤ q ∧ q < 2 * R ∧ Nat.Coprime q (bigB b) ∧ 2 ≤ q := by
    intro q hq; obtain ⟨a1, a2, a3, a4⟩ := hQs q hq
    exact ⟨a1, by rw [hRdef, ← pow_succ']; exact a2, a3, a4⟩
  have h50 : 2500 ≤ N → 50 ≤ n := fun h => Nat.le_sqrt'.2 (by norm_num; omega)
  clear_value n ℓ R
  set K0 := Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12)
  set K1 := Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12)
  have hK0 : 0 ≤ K0 := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  have he5 : 1 ≤ Real.exp (5 * colC b) := Real.one_le_exp (by linarith)
  have hgeom : 0 ≤ (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by positivity
  by_cases hreg : 3 * ℓ + 1 ≤ N
  · -- regime I
    have hblk := block_regime_I b N ℓ R k hb hℓ1 hreg hR1 h2R hbl Qs hQs' hcard (del0 b) Cw (del0 b) Ce
      (del0_pos b hb).le (del0_pos b hb).le hCw hCe
    have hshape := bnd_I_shape b N ℓ R hb hℓ1 hreg h2R.le Cw Ce
      (Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ))) hCw0 hCe0 (Real.exp_nonneg _)
    refine (hblk.trans hshape).trans ?_
    have hmain : K0 * (ℓ : ℝ) ^ 2 * (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ *
        Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ)) ≤
        K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by
      by_cases hln : ℓ ≤ n
      · -- Col wins
        have hdiv : (n : ℝ) - 5 ≤ (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ) := by
          by_cases hn5 : n ≤ 5
          · have : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
            have : (0 : ℝ) ≤ (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith
          · push Not at hn5
            have hle : (n - 5) * ℓ ≤ N - 3 * ℓ - 2 := by
              have h1 : (n - 5) * ℓ + 3 * ℓ + 2 ≤ n * n := by
                have : (n - 5) * ℓ + 3 * ℓ ≤ (n - 2) * ℓ := by
                  rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
                have : (n - 2) * ℓ ≤ (n - 2) * n := Nat.mul_le_mul_left _ hln
                have : (n - 2) * n + 2 ≤ n * n := nat_aux_sq n (by omega)
                omega
              have : n * n ≤ N := by rw [← sq]; exact hnN
              omega
            have := (Nat.le_div_iff_mul_le (by omega)).2 hle
            have : ((n - 5 : ℕ) : ℝ) ≤ (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ) := by exact_mod_cast this
            push_cast [show 5 ≤ n by omega] at this
            linarith
        have hcol : Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ)) ≤ Real.exp (5 * colC b) * Real.exp (-colC b) ^ n := by
          rw [← Real.exp_natCast_mul, ← Real.exp_add]
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left hdiv hc.le
          linarith
        have hpow : (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ ≤ (Real.exp (m0 b) ^ 7) ^ n := by
          calc (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ ≤ (Real.exp (m0 b) ^ 7) ^ ℓ := by
                apply pow_le_pow_left₀ (by positivity)
                exact mul_le_of_le_one_right (by positivity) hγ1
            _ ≤ (Real.exp (m0 b) ^ 7) ^ n := pow_le_pow_right₀ (one_le_pow₀ hu1) hln
        have hl2 : (ℓ : ℝ) ^ 2 ≤ (((n : ℕ) : ℝ) + 1) ^ 4 := by
          have : (ℓ : ℝ) ≤ n := by exact_mod_cast hln
          have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                                                 linarith
          calc (ℓ : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
            _ ≤ ((n : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
        have hfin : (Real.exp (m0 b) ^ 7) ^ n * Real.exp (-colC b) ^ n ≤ rhoL b ^ n := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hu7 n
        calc K0 * (ℓ : ℝ) ^ 2 * (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ * Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ))
            ≤ K0 * (((n : ℕ) : ℝ) + 1) ^ 4 * (Real.exp (m0 b) ^ 7) ^ n * (Real.exp (5 * colC b) * Real.exp (-colC b) ^ n) := by
              gcongr
          _ = K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * ((Real.exp (m0 b) ^ 7) ^ n * Real.exp (-colC b) ^ n) := by ring
          _ ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by gcongr
      · -- geometric decay wins
        push Not at hln
        have hcol1 : Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; have : (0 : ℝ) ≤ (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
          have := mul_nonneg hc.le this
          linarith
        have hu7γ : Real.exp (m0 b) ^ 7 * gam b ≤ rhoL b := by
          calc Real.exp (m0 b) ^ 7 * gam b ≤ Real.exp (m0 b) ^ 150 * gam b := by
                apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hu1 (by norm_num)) hγ0
            _ ≤ rhoL b := hu150
        have hpow : (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ ≤ rhoL b ^ n := by
          calc (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ ≤ rhoL b ^ ℓ := pow_le_pow_left₀ (by positivity) hu7γ ℓ
            _ ≤ rhoL b ^ n := pow_le_pow_of_le_one hρ0 hρ1 hln.le
        have hl2 : (ℓ : ℝ) ^ 2 ≤ (((n : ℕ) : ℝ) + 1) ^ 4 := by
          have : (ℓ : ℝ) ≤ N := by exact_mod_cast (by omega : ℓ ≤ N)
          calc (ℓ : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
            _ ≤ _ := hNR
        calc K0 * (ℓ : ℝ) ^ 2 * (Real.exp (m0 b) ^ 7 * gam b) ^ ℓ * Real.exp (-colC b * (((N - 3 * ℓ - 2) / ℓ : ℕ) : ℝ))
            ≤ K0 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n * 1 := by gcongr
          _ ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by
              rw [mul_one]
              have hX : 0 ≤ (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := hgeom
              calc K0 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n = K0 * 1 * ((((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n) := by ring
                _ ≤ K0 * Real.exp (5 * colC b) * ((((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n) := by gcongr
                _ = _ := by ring
    calc _ ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := hmain
      _ ≤ _ := by
          have h2 : 0 ≤ K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by positivity
          calc K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n
              ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n +
                K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by linarith
            _ = _ := by ring
  · -- regime II
    push Not at hreg
    have hl2 : 2 * ℓ + 1 ≤ N := by omega
    have hblk := block_regime_II b N ℓ R k hb (by omega) hl2 hR1 h2R hbl Qs hQs' hcard (del0 b) Cw
      (del0 b) Ce (del0_pos b hb).le (del0_pos b hb).le hCw hCe
    have hshape := bnd_II_shape b N ℓ R hb hl2 h2R.le Cw Ce hCw0 hCe0
    refine (hblk.trans hshape).trans ?_
    set a := N - 1 - 2 * ℓ
    have ha50 : N / 50 ≤ a := by
      apply Nat.div_le_of_le_mul; omega
    have hn50 : n ≤ N / 50 := by
      have h50 : 50 ≤ n := h50 hN
      apply (Nat.le_div_iff_mul_le (by norm_num)).2
      calc n * 50 ≤ n * n := Nat.mul_le_mul_left _ h50
        _ = n ^ 2 := (sq n).symm
        _ ≤ N := hnN
    have hγa : gam b ^ a ≤ gam b ^ (N / 50) := pow_le_pow_of_le_one hγ0 hγ1 ha50
    have hu3 : Real.exp (m0 b) ^ (3 * N) ≤ Real.exp (m0 b) ^ 150 * (Real.exp (m0 b) ^ 150) ^ (N / 50) := by
      rw [← pow_mul, ← pow_add]
      apply pow_le_pow_right₀ hu1
      have := Nat.lt_div_mul_add (a := N) (by norm_num : 0 < 50)
      omega
    have hgeo : (Real.exp (m0 b) ^ 150) ^ (N / 50) * gam b ^ (N / 50) ≤ rhoL b ^ n := by
      rw [← mul_pow]
      calc (Real.exp (m0 b) ^ 150 * gam b) ^ (N / 50) ≤ rhoL b ^ (N / 50) := pow_le_pow_left₀ (by positivity) hu150 _
        _ ≤ rhoL b ^ n := pow_le_pow_of_le_one hρ0 hρ1 hn50
    calc K1 * (N : ℝ) ^ 2 * Real.exp (m0 b) ^ (3 * N) * gam b ^ a
        ≤ K1 * (((n : ℕ) : ℝ) + 1) ^ 4 * (Real.exp (m0 b) ^ 150 * (Real.exp (m0 b) ^ 150) ^ (N / 50)) * gam b ^ (N / 50) := by
          gcongr
      _ = K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * ((Real.exp (m0 b) ^ 150) ^ (N / 50) * gam b ^ (N / 50)) := by ring
      _ ≤ K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by gcongr
      _ ≤ _ := by
          have h2 : 0 ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by positivity
          calc K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n
              ≤ K0 * Real.exp (5 * colC b) * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n +
                K1 * Real.exp (m0 b) ^ 150 * (((n : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ n := by linarith
            _ = _ := by ring

/-- `‖S(α)‖ ≤ b^{N+1} Π_{1≤n<N} √ψ(c_n α)`. -/
theorem Ssum_le (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (α : ℝ) :
    ‖Ssum b N α‖ ≤ (b : ℝ) ^ (N + 1) * ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * α)) := by
  have h := expsum_le_PhiN b N hb hN α
  rw [PhiN_eq b N (by omega) α] at h
  have e : (b : ℝ) ^ 2 * ((b : ℝ) ^ (N - 1) * ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * α))) =
      (b : ℝ) ^ (N + 1) * ∏ n ∈ Ico 1 N, Real.sqrt (psiB b (cK b N n * α)) := by
    rw [← mul_assoc, ← pow_add, show 2 + (N - 1) = N + 1 by omega]
  rw [e] at h
  exact h

/-- `h1/r = k/(b³−b)` for `r ∣ b³ − b`. -/
theorem div_eq_k (b r h1 : ℕ) (hb : 2 ≤ b) (hr : r ∣ bigB b) (hr0 : 0 < r) :
    (h1 : ℝ) / r = ((h1 * (bigB b / r) : ℕ) : ℤ) / (bigB b : ℝ) := by
  have hB0 : (bigB b : ℝ) ≠ 0 := by exact_mod_cast bigB_ne_zero b hb
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
  obtain ⟨m, hm⟩ := hr
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; exact absurd hm (bigB_ne_zero b hb)
    · exact h
  rw [hm, Nat.mul_div_cancel_left _ hr0]
  push_cast
  field_simp

/-- The sum over Farey points with the full product, for a fixed shift `β = k/B`. -/
theorem farey_total_le (b : ℕ) (hb : 2 ≤ b) (Cw Ce : ℝ) (hCw0 : 0 ≤ Cw) (hCe0 : 0 ≤ Ce)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ del0 b)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ del0 b)
    (N D : ℕ) (hN : 2500 ≤ N) (hD : (D : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25)) (hD1 : 1 ≤ D)
    (k : ℤ) (K : ℝ)
    (hK : K = (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
        (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N)) :
    ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) ≤
      (Nat.log 2 D : ℝ) * K := by
  classical
  have hmaps : ∀ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
      Nat.log 2 q ∈ Icc 1 (Nat.log 2 D) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    rw [mem_Icc]
    exact ⟨Nat.log_pos (by norm_num) hq.1.1, Nat.log_mono_right hq.1.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ i ∈ Icc 1 (Nat.log 2 D), K := by
        apply Finset.sum_le_sum
        intro i hi
        rw [mem_Icc] at hi
        have hiD : (2 : ℝ) ^ (i + 1) ≤ 2 * ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25) := by
          have h1 : 2 ^ i ≤ D := le_trans (Nat.pow_le_pow_right (by norm_num) hi.2)
            (Nat.pow_log_le_self 2 (by omega))
          have h1' : (2 : ℝ) ^ i ≤ D := by exact_mod_cast h1
          rw [pow_succ]; linarith
        have hQs : ∀ q ∈ ((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter
            (fun q => Nat.log 2 q = i),
            2 ^ i ≤ q ∧ q < 2 ^ (i + 1) ∧ Nat.Coprime q (bigB b) ∧ 2 ≤ q := by
          intro q hq
          simp only [mem_filter, mem_Icc] at hq
          obtain ⟨⟨⟨h2, _⟩, hcop⟩, hlog⟩ := hq
          refine ⟨?_, ?_, hcop, h2⟩
          · rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
          · rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) q
        have hcard : #(((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter
            (fun q => Nat.log 2 q = i)) ≤ 2 ^ i := by
          have hsub : ((Icc 2 D).filter (fun q => Nat.Coprime q (bigB b))).filter
              (fun q => Nat.log 2 q = i) ⊆ Ico (2 ^ i) (2 ^ (i + 1)) := by
            intro q hq
            rw [mem_Ico]
            exact ⟨(hQs q hq).1, (hQs q hq).2.1⟩
          calc _ ≤ #(Ico (2 ^ i) (2 ^ (i + 1))) := card_le_card hsub
            _ = 2 ^ i := by rw [Nat.card_Ico, pow_succ]; omega
        rw [hK]
        exact block_le_geom b hb Cw Ce hCw0 hCe0 hCw hCe N i hN hi.1 hiD _ hQs hcard k
    _ = (Nat.log 2 D : ℝ) * K := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

theorem sum_inv_le_log (D : ℕ) : ∑ a ∈ Icc 1 D, (1 : ℝ) / a ≤ 1 + Real.log D := by
  have h := harmonic_le_one_add_log D
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- One shift `h1/r`: regrouping plus the Farey total. -/
theorem inner_le (b : ℕ) (hb : 2 ≤ b) (Cw Ce : ℝ) (hCw0 : 0 ≤ Cw) (hCe0 : 0 ≤ Ce)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ del0 b)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ del0 b)
    (N D : ℕ) (hN : 2500 ≤ N) (hD : (D : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25)) (hD1 : 1 ≤ D)
    (K : ℝ)
    (hK : K = (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
        (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N))
    (r h1 : ℕ) (hr : r ∈ (bigB b).divisors) :
    ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
          ∑ h2 ∈ Ico 1 q, ‖Ssum b N ((h1 : ℝ) / r + (h2 : ℝ) / q)‖ ≤
      (∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * ((Nat.log 2 D : ℝ) * K)) := by
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
  have hF := farey_total_le b hb Cw Ce hCw0 hCe0 hCw hCe N D hN hD hD1 k K hK
  have hb0 : (0 : ℝ) ≤ (b : ℝ) ^ (N + 1) := by positivity
  calc _ ≤ ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, (b : ℝ) ^ (N + 1) * ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) := by
        apply Finset.sum_le_sum; intro q _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro h _
        have e : (h1 : ℝ) / r + (h : ℝ) / q = (h : ℝ) / q + (k : ℝ) / (bigB b : ℝ) := by
          rw [hk, add_comm]
        show ‖Ssum b N ((h1 : ℝ) / r + (h : ℝ) / q)‖ ≤ _
        rw [e]
        exact Ssum_le b N hb (by omega) _
    _ = (b : ℝ) ^ (N + 1) * ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
        ((3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q) *
        ∑ h ∈ redRes q, ∏ n ∈ Ico 1 N,
          Real.sqrt (psiB b (cK b N n * ((h : ℝ) / q + k / (bigB b : ℝ)))) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
        rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF hb0

/-- The explicit level bound for one `N`. -/
theorem level_explicit (b : ℕ) (hb : 2 ≤ b) (Cw Ce : ℝ) (hCw0 : 0 ≤ Cw) (hCe0 : 0 ≤ Ce)
    (hCw : ∀ n : ℕ, 1 ≤ n → (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors n) ≤ Cw * (n : ℝ) ^ del0 b)
    (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ del0 b)
    (N D : ℕ) (hN : 2500 ≤ N) (hD : (D : ℝ) ≤ ((b : ℝ) ^ (2 * N + 1)) ^ ((6 : ℝ) / 25)) (hD1 : 1 ≤ D)
    (K : ℝ)
    (hK : K = (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
        (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N)) :
    ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
          |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| ≤
      (∑ r ∈ (bigB b).divisors, (r : ℝ)) *
        ((∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * ((Nat.log 2 D : ℝ) * K))) := by
  classical
  set Q1 := (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b))
  set R := (∑ k ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors k / k) *
        ((b : ℝ) ^ (N + 1) * ((Nat.log 2 D : ℝ) * K))
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
        exact inner_le b hb Cw Ce hCw0 hCe0 hCw hCe N D hN hD hD1 K hK r h1 hr
    _ = _ := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The form the sieve (M13) consumes: level `6/25`, weights `3^ω`, saving `log³x`. -/
theorem level_piStar_weighted (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ q ∈ (Icc 1 ⌊((b : ℝ) ^ (2 * N + 1)) ^ (6 / 25 : ℝ)⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  classical
  obtain ⟨Cw, hCw⟩ := three_pow_omega_le_rpow (del0 b) (del0_pos b hb)
  obtain ⟨Ce, hCe⟩ := card_divisors_le_rpow (del0 b) (del0_pos b hb)
  have hCw0 : 0 ≤ Cw := by
    have := hCw 1 le_rfl
    simp [ArithmeticFunction.cardDistinctFactors_one] at this; linarith
  have hCe0 : 0 ≤ Ce := by
    have := hCe 1 le_rfl
    simp at this; linarith
  obtain ⟨cA, hcA, N₁, hN₁⟩ := card_piStar_lower b hb
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
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
  obtain ⟨n₀, hn₀⟩ := eventually_poly_geom C 18 (rhoL b) (rhoL_nonneg b) (rhoL_lt_one b hb) cA hcA
  refine ⟨max (max 2500 N₁) (n₀ ^ 2), fun N hN => ?_⟩
  have hN2500 : 2500 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnn₀ : n₀ ≤ Nat.sqrt N := Nat.le_sqrt'.2 (le_trans (le_max_right _ _) hN)
  -- the moduli range
  set x : ℝ := (b : ℝ) ^ (2 * N + 1) with hx
  have hx1 : 1 ≤ x := one_le_pow₀ hb1.le
  have hxr1 : 1 ≤ x ^ (6 / 25 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  set D : ℕ := ⌊x ^ (6 / 25 : ℝ)⌋₊ with hDdef
  have hD : (D : ℝ) ≤ x ^ ((6 : ℝ) / 25) := Nat.floor_le (by linarith)
  have hD1 : 1 ≤ D := Nat.le_floor (by simpa using hxr1)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  set L : ℝ := Real.log x with hL
  have hLx : L = (2 * N + 1 : ℕ) * Real.log b := by rw [hL, hx, Real.log_pow]
  have hL0 : 0 < L := by rw [hLx]; positivity
  have hlogD : Real.log D ≤ L := by
    have h1 : Real.log D ≤ Real.log (x ^ ((6 : ℝ) / 25)) := Real.log_le_log hD0 hD
    rw [Real.log_rpow (by linarith)] at h1
    linarith
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD1)
  -- polynomial size of the logarithms
  set n : ℕ := Nat.sqrt N with hn
  have hNn : 2 * N + 1 ≤ 3 * (n + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' N
    rw [← hn] at this
    have : N + 1 ≤ (n + 1) ^ 2 := this
    generalize (n + 1) ^ 2 = m at this ⊢
    omega
  have hLn : L ≤ Lb * ((n : ℝ) + 1) ^ 2 := by
    have h1 : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * ((n : ℝ) + 1) ^ 2 := by exact_mod_cast hNn
    rw [hLx, hLb]
    have h3 := mul_le_mul_of_nonneg_right h1 hlogb.le
    have h4 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
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
  have hlog2 : (Nat.log 2 D : ℝ) ≤ 2 * (Lb * ((n : ℝ) + 1) ^ 2) := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 D) ≤ D := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : (Nat.log 2 D : ℝ) * Real.log 2 ≤ Real.log D := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
    have h3 := Real.log_two_gt_d9
    have h4 : (0 : ℝ) ≤ Nat.log 2 D := Nat.cast_nonneg _
    have h5 : (Nat.log 2 D : ℝ) * (1 / 2) ≤ (Nat.log 2 D : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    linarith
  -- the explicit bound
  have hK : K0 * (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N) =
      (Cw * (1 + 50 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (5 * colC b) +
        Cw * (1 + 18 * Ce * b) * (32 * (b : ℝ) ^ 2 + 12) * Real.exp (m0 b) ^ 150) *
        (((Nat.sqrt N : ℕ) : ℝ) + 1) ^ 4 * rhoL b ^ (Nat.sqrt N) := by rw [hK0]
  have hE := level_explicit b hb Cw Ce hCw0 hCe0 hCw hCe N D hN2500 hD hD1 _ hK
  rw [← hn] at hE
  have hKn0 : 0 ≤ K0 * ((n : ℝ) + 1) ^ 4 * rhoL b ^ n := by
    have := rhoL_nonneg b; positivity
  have hB : (∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|) ≤
      SB * ((Lb * ((n : ℝ) + 1) ^ 2) ^ 3 * ((b : ℝ) ^ (N + 1) *
        ((2 * (Lb * ((n : ℝ) + 1) ^ 2)) * (K0 * ((n : ℝ) + 1) ^ 4 * rhoL b ^ n)))) := by
    refine le_trans hE ?_
    gcongr
  rw [le_div_iff₀ (by positivity)]
  have hL3 : L ^ 3 ≤ (Lb * ((n : ℝ) + 1) ^ 2) ^ 3 := by gcongr
  have hLHS0 : 0 ≤ ∑ q ∈ (Icc 1 D).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| :=
    Finset.sum_nonneg (fun q _ => by positivity)
  have hgeo := hn₀ n hnn₀
  have hbN : (0 : ℝ) ≤ (b : ℝ) ^ N := by positivity
  calc _ ≤ (SB * ((Lb * ((n : ℝ) + 1) ^ 2) ^ 3 * ((b : ℝ) ^ (N + 1) *
        ((2 * (Lb * ((n : ℝ) + 1) ^ 2)) * (K0 * ((n : ℝ) + 1) ^ 4 * rhoL b ^ n))))) *
        (Lb * ((n : ℝ) + 1) ^ 2) ^ 3 := mul_le_mul hB hL3 (by positivity) (by
          have := mul_nonneg hSB0 (mul_nonneg (by positivity : (0:ℝ) ≤ (Lb * ((n : ℝ) + 1) ^ 2) ^ 3)
            (mul_nonneg (by positivity : (0:ℝ) ≤ (b : ℝ) ^ (N + 1))
              (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (Lb * ((n : ℝ) + 1) ^ 2)) hKn0)))
          exact this)
    _ = (b : ℝ) ^ N * (C * ((n : ℝ) + 1) ^ 18 * rhoL b ^ n) := by
        rw [hC, pow_succ]; ring
    _ ≤ (b : ℝ) ^ N * cA := mul_le_mul_of_nonneg_left hgeo hbN
    _ = cA * (b : ℝ) ^ N := by ring
    _ ≤ _ := hN₁ N hNN₁

end Palprimes
