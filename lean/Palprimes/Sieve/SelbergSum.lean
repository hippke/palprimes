import Palprimes.Sieve.Vendor.Selberg

/-! # Lower bounds for the Selberg sum `S(t, ξ) = Σ_{l | P(t), l ≤ ξ} 1/φ(l)` (sieve route, M13)

- `rankin_lower`, `rankin_rel`: Rankin's trick, `S ≥ V⁻¹ (1 − ξ^{−σ} Π(1 + (q^σ − 1)/q))`.
- `sum_inv_factored_le`, `factored_le_selbergS`: `S ≥ Σ_{n ≤ ξ, rad n | P} 1/n` (Euler product, radical grouping).
- `HB`, `HB_eq`, `HB_approx`: `Σ_{m ≤ K, (m, B) = 1} 1/m = β log K + O_B(1)`.
See `plan/sieve_route/SIEVE_ROUTE.md`. -/

open Finset Real

namespace Palprimes

theorem sum_divisors_primes (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (f : ℕ → ℝ) :
    ∑ d ∈ (∏ p ∈ Pset, p).divisors, f d = ∑ t ∈ Pset.powerset, f (∏ p ∈ t, p) := by
  have hsq := SelbergPort.prod_primes_squarefree Pset hP
  have hP0 : (∏ p ∈ Pset, p) ≠ 0 := hsq.ne_zero
  symm
  apply Finset.sum_nbij' (fun t => ∏ p ∈ t, p) (fun d => d.primeFactors)
  · intro t ht
    rw [mem_powerset] at ht
    rw [Nat.mem_divisors]
    exact ⟨Finset.prod_dvd_prod_of_subset _ _ _ ht, hP0⟩
  · intro d hd
    rw [Nat.mem_divisors] at hd
    rw [mem_powerset]
    have := Nat.primeFactors_mono hd.1 hP0
    rwa [Nat.primeFactors_prod hP] at this
  · intro t ht
    rw [mem_powerset] at ht
    exact Nat.primeFactors_prod (fun p hp => hP p (ht hp))
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hd.1)
  · intro t _; rfl

theorem totient_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    (Nat.totient (∏ p ∈ t, p) : ℝ) = ∏ p ∈ t, ((p : ℝ) - 1) := by
  rw [SelbergPort.totient_eq_prod_of_squarefree (SelbergPort.prod_primes_squarefree t ht), Nat.primeFactors_prod ht]

/-- `Σ_{l | P} l^σ/φ(l) = Π_{q}(1 + q^σ/(q−1))`. -/
theorem sum_rpow_div_totient (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (σ : ℝ) :
    ∑ d ∈ (∏ p ∈ Pset, p).divisors, (d : ℝ) ^ σ / (Nat.totient d) =
      ∏ q ∈ Pset, (1 + (q : ℝ) ^ σ / ((q : ℝ) - 1)) := by
  rw [sum_divisors_primes Pset hP, prod_one_add]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mem_powerset] at ht
  have htP : ∀ p ∈ t, p.Prime := fun p hp => hP p (ht hp)
  rw [totient_prod_primes t htP, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Finset.prod_div_distrib]

/-- **Rankin.** The truncated Selberg sum is the full Euler product minus a Rankin tail. -/
theorem rankin_lower (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (σ y : ℝ) (hσ : 0 ≤ σ) (hy : 0 < y) :
    ∏ q ∈ Pset, (1 + 1 / ((q : ℝ) - 1)) -
        y ^ (-(σ / 2)) * ∏ q ∈ Pset, (1 + (q : ℝ) ^ σ / ((q : ℝ) - 1)) ≤
      ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l) := by
  classical
  have hfull := sum_rpow_div_totient Pset hP 0
  simp only [Real.rpow_zero] at hfull
  have htail := sum_rpow_div_totient Pset hP σ
  rw [← hfull, ← htail]
  rw [← Finset.sum_filter_add_sum_filter_not (∏ p ∈ Pset, p).divisors (fun l : ℕ => ((l : ℝ)) ^ 2 ≤ y)]
  have hT : ∑ l ∈ (∏ p ∈ Pset, p).divisors with ¬ (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l) ≤
      y ^ (-(σ / 2)) * ∑ d ∈ (∏ p ∈ Pset, p).divisors, (d : ℝ) ^ σ / (Nat.totient d) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ l ∈ (∏ p ∈ Pset, p).divisors with ¬ (((l : ℕ) : ℝ) ^ 2 ≤ y), y ^ (-(σ / 2)) * ((l : ℝ) ^ σ / (Nat.totient l)) := by
          apply Finset.sum_le_sum; intro l hl
          rw [mem_filter, not_le] at hl
          have hφ : (0 : ℝ) ≤ 1 / (Nat.totient l) := by positivity
          have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
          have h1 : 1 ≤ y ^ (-(σ / 2)) * (l : ℝ) ^ σ := by
            have hyl : y ^ (σ / 2) ≤ (l : ℝ) ^ σ := by
              have : (l : ℝ) ^ σ = (((l : ℝ)) ^ 2) ^ (σ / 2) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]; congr 1; push_cast; ring
              rw [this]
              exact Real.rpow_le_rpow hy.le hl.2.le (by linarith)
            rw [Real.rpow_neg hy.le, inv_mul_eq_div, le_div_iff₀ (Real.rpow_pos_of_pos hy _), one_mul]
            exact hyl
          calc (1 : ℝ) / (Nat.totient l) = 1 * (1 / (Nat.totient l)) := by ring
            _ ≤ (y ^ (-(σ / 2)) * (l : ℝ) ^ σ) * (1 / (Nat.totient l)) :=
                mul_le_mul_of_nonneg_right h1 hφ
            _ = _ := by ring
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro l _ _; positivity
  linarith

theorem one_add_rpow_div (q σ : ℝ) (hq : 1 < q) :
    1 + q ^ σ / (q - 1) = (1 + 1 / (q - 1)) * (1 + (q ^ σ - 1) / q) := by
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : q ≠ 0 := by linarith
  field_simp
  ring

theorem rpow_sub_one_le (q t a : ℝ) (hq : 1 ≤ q) (hqt : q ≤ t) (ht : 1 < t) (ha : 0 ≤ a) :
    q ^ (a / Real.log t) - 1 ≤ (Real.exp a - 1) * (Real.log q / Real.log t) := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  set s := Real.log q / Real.log t with hs
  have hs0 : 0 ≤ s := div_nonneg (Real.log_nonneg hq) hlt.le
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hlt]; exact Real.log_le_log (by linarith) hqt
  have hq0 : 0 < q := by linarith
  have e : q ^ (a / Real.log t) = Real.exp (s * a + (1 - s) * 0) := by
    rw [Real.rpow_def_of_pos hq0, hs]; congr 1; field_simp; ring
  rw [e]
  have hc := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ 0) hs0 (by linarith : 0 ≤ 1 - s) (by ring)
  simp only [smul_eq_mul, Real.exp_zero] at hc
  linarith

/-- Rankin in relative form: `S ≥ V⁻¹ (1 − y^{−a/(2 log t)} exp((e^a − 1) Σ log q/q / log t))`. -/
theorem rankin_rel (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (t a y : ℝ) (ht : 1 < t)
    (hPt : ∀ p ∈ Pset, (p : ℝ) ≤ t) (ha : 0 ≤ a) (hy : 0 < y) :
    (∏ q ∈ Pset, (1 + 1 / ((q : ℝ) - 1))) *
        (1 - y ^ (-(a / Real.log t / 2)) *
          Real.exp ((Real.exp a - 1) / Real.log t * ∑ q ∈ Pset, Real.log q / q)) ≤
      ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l) := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  have hσ : 0 ≤ a / Real.log t := div_nonneg ha hlt.le
  refine le_trans ?_ (rankin_lower Pset hP (a / Real.log t) y hσ hy)
  have hq1 : ∀ q ∈ Pset, (1 : ℝ) < q := fun q hq => by exact_mod_cast (hP q hq).one_lt
  rw [Finset.prod_congr rfl (fun (q : ℕ) hq => one_add_rpow_div (q : ℝ) (a / Real.log t) (hq1 q hq)),
    Finset.prod_mul_distrib]
  set V := ∏ q ∈ Pset, (1 + 1 / ((q : ℝ) - 1))
  have hV : 0 ≤ V := Finset.prod_nonneg (fun q hq => by
    have := hq1 q hq; have : 0 < (q : ℝ) - 1 := by linarith
    positivity)
  have hR : ∏ q ∈ Pset, (1 + ((q : ℝ) ^ (a / Real.log t) - 1) / q) ≤
      Real.exp ((Real.exp a - 1) / Real.log t * ∑ q ∈ Pset, Real.log q / q) := by
    calc _ ≤ ∏ q ∈ Pset, Real.exp (((q : ℝ) ^ (a / Real.log t) - 1) / q) := by
          apply Finset.prod_le_prod₀
          · intro q hq
            have h1 : 0 ≤ (q : ℝ) ^ (a / Real.log t) - 1 := by
              have := Real.one_le_rpow (hq1 q hq).le hσ; linarith
            have : (0 : ℝ) < q := by linarith [hq1 q hq]
            positivity
          · intro q _
            have := Real.add_one_le_exp (((q : ℝ) ^ (a / Real.log t) - 1) / q); linarith
      _ = Real.exp (∑ q ∈ Pset, ((q : ℝ) ^ (a / Real.log t) - 1) / q) := (Real.exp_sum _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro q hq
          have h := rpow_sub_one_le (q : ℝ) t a (hq1 q hq).le (hPt q hq) ht ha
          have hq0 : (0 : ℝ) < q := by linarith [hq1 q hq]
          rw [div_le_iff₀ hq0]
          calc _ ≤ (Real.exp a - 1) * (Real.log q / Real.log t) := h
            _ = _ := by field_simp
  have hy0 : 0 ≤ y ^ (-(a / Real.log t / 2)) := Real.rpow_nonneg hy.le _
  have e2 : -(a / Real.log t / 2) = -((a / Real.log t) / 2) := rfl
  nlinarith [mul_le_mul_of_nonneg_left hR (mul_nonneg hV hy0)]

/-- `n ↦ 1/n` as a monoid hom. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

/-- Finite partial sums of `1/m` over `t`-factored numbers are below the Euler product. -/
theorem sum_inv_factored_le (t : Finset ℕ) (K : ℕ) :
    ∑ m ∈ (Icc 1 K).filter (fun m => m ∈ Nat.factoredNumbers t), (1 : ℝ) / m ≤
      ∏ p ∈ t with p.Prime, (1 - (1 : ℝ) / p)⁻¹ := by
  classical
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := invHom) (fun {p} hp => by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
      exact inv_lt_one_of_one_lt₀ this) t).2
  have hle := sum_le_hasSum (((Icc 1 K).filter (fun m => m ∈ Nat.factoredNumbers t)).subtype
    (fun m => m ∈ Nat.factoredNumbers t)) (fun m _ => by
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]; positivity) h
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_filter] at hle
  simp only [and_self, invHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  simpa [one_div, Finset.prod_inv_distrib] using hle

/-- `(1/l) Π_{p | l} (1 − 1/p)⁻¹ = 1/φ(l)` for squarefree `l`. -/
theorem inv_mul_euler_eq (l : ℕ) (hl : Squarefree l) :
    (1 / (l : ℝ)) * ∏ p ∈ l.primeFactors with p.Prime, (1 - (1 : ℝ) / p)⁻¹ = 1 / (Nat.totient l) := by
  have hf : l.primeFactors.filter Nat.Prime = l.primeFactors :=
    Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have e : (l : ℝ) = ∏ p ∈ l.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hl]
  rw [hf, SelbergPort.totient_eq_prod_of_squarefree hl, e, one_div, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ≠ 0 := by linarith
  field_simp

/-- Grouping by the radical: factored numbers up to `K` give a lower bound for the Selberg sum. -/
theorem factored_le_selbergS (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (K : ℕ) (y : ℝ)
    (hKy : (K : ℝ) ^ 2 ≤ y) :
    ∑ n ∈ (Icc 1 K).filter (fun n => n ∈ Nat.factoredNumbers Pset), (1 : ℝ) / n ≤
      ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l) := by
  classical
  set P := ∏ p ∈ Pset, p
  have hsq : Squarefree P := SelbergPort.prod_primes_squarefree Pset hP
  have hP0 : P ≠ 0 := hsq.ne_zero
  set F := (Icc 1 K).filter (fun n => n ∈ Nat.factoredNumbers Pset)
  set T := P.divisors.filter (fun l : ℕ => ((l : ℕ) : ℝ) ^ 2 ≤ y)
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors, p
  have hmaps : ∀ n ∈ F, g n ∈ T := by
    intro n hn
    simp only [F, mem_filter, mem_Icc] at hn
    have hsub := Nat.primeFactors_subset_of_mem_factoredNumbers hn.2
    simp only [T, mem_filter, Nat.mem_divisors]
    refine ⟨⟨Finset.prod_dvd_prod_of_subset _ _ _ hsub, hP0⟩, ?_⟩
    have hg : g n ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have : ((g n : ℕ) : ℝ) ≤ K := by exact_mod_cast le_trans hg hn.1.2
    have h0 : (0 : ℝ) ≤ g n := Nat.cast_nonneg _
    nlinarith
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro l hl
  simp only [T, mem_filter, Nat.mem_divisors] at hl
  have hlsq : Squarefree l := hsq.squarefree_of_dvd hl.1.1
  have hl0 : 0 < l := Nat.pos_of_ne_zero hlsq.ne_zero
  rw [← inv_mul_euler_eq l hlsq]
  -- the fibre, written as `n = l * m`
  set Fl := F.filter (fun n => g n = l)
  have hdiv : ∀ n ∈ Fl, l ∣ n := by
    intro n hn
    simp only [Fl, mem_filter] at hn
    rw [← hn.2]; exact Nat.prod_primeFactors_dvd n
  have hinj : Set.InjOn (fun n => n / l) (Fl : Set ℕ) := by
    intro n hn n' hn' h
    simp only at h
    have e1 := Nat.div_mul_cancel (hdiv n hn)
    have e2 := Nat.div_mul_cancel (hdiv n' hn')
    rw [← e1, ← e2, h]
  have himg : Fl.image (fun n => n / l) ⊆
      (Icc 1 K).filter (fun m => m ∈ Nat.factoredNumbers l.primeFactors) := by
    intro m hm
    rw [mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    have hn' := hn
    simp only [Fl, F, mem_filter, mem_Icc] at hn'
    obtain ⟨⟨⟨hn1, hnK⟩, hnf⟩, hgl⟩ := hn'
    have hln := hdiv n hn
    have hml : n / l ≠ 0 := by
      intro h0; rw [Nat.div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · omega
      · exact absurd (Nat.le_of_dvd (by omega) hln) (not_le.2 h0)
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 hml, le_trans (Nat.div_le_self n l) hnK⟩, ?_⟩
    apply Nat.mem_factoredNumbers_of_primeFactors_subset hml
    have h1 : (n / l).primeFactors ⊆ n.primeFactors :=
      Nat.primeFactors_mono (Nat.div_dvd_of_dvd hln) (by omega)
    have h2 : l.primeFactors = n.primeFactors := by
      rw [← hgl]; exact Nat.primeFactors_prod_primeFactors n
    rw [h2]; exact h1
  calc ∑ n ∈ Fl, (1 : ℝ) / n = ∑ n ∈ Fl, (1 / (l : ℝ)) * (1 / ((n / l : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl; intro n hn
        have e := Nat.div_mul_cancel (hdiv n hn)
        conv_lhs => rw [← e]
        push_cast; rw [mul_comm]; field_simp
    _ = (1 / (l : ℝ)) * ∑ m ∈ Fl.image (fun n => n / l), (1 : ℝ) / m := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (1 / (l : ℝ)) * ∑ m ∈ (Icc 1 K).filter (fun m => m ∈ Nat.factoredNumbers l.primeFactors),
          (1 : ℝ) / m := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg himg
        intro m _ _; positivity
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_factored_le l.primeFactors K) (by positivity)

/-- `H_s(K) = Σ_{m ≤ K, q ∤ m ∀ q ∈ s} 1/m`. -/
noncomputable def HB (s : Finset ℕ) (K : ℕ) : ℝ :=
  ∑ m ∈ (Icc 1 K).filter (fun m => ∀ q ∈ s, ¬ q ∣ m), (1 : ℝ) / m

theorem sum_Icc_dvd (d K : ℕ) (hd : 0 < d) :
    ∑ m ∈ (Icc 1 K).filter (fun m => d ∣ m), (1 : ℝ) / m =
      (1 / (d : ℝ)) * ∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_nbij' (fun j => d * j) (fun m => m / d)
  · intro j hj
    simp only [mem_Icc] at hj
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
    calc d * j ≤ d * (K / d) := Nat.mul_le_mul_left d hj.2
      _ ≤ K := Nat.mul_div_le K d
  · intro m hm
    simp only [mem_filter, mem_Icc] at hm
    simp only [mem_Icc]
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left k hd]
    have h3 : d * k / d ≤ K / d := Nat.div_le_div_right h2
    rw [Nat.mul_div_cancel_left k hd] at h3
    refine ⟨?_, h3⟩
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at h1
    · exact h
  · intro j _; exact Nat.mul_div_cancel_left j hd
  · intro m hm
    simp only [mem_filter] at hm
    exact Nat.mul_div_cancel' hm.2
  · intro j _
    push_cast
    rw [one_div_mul_one_div]

theorem prod_dvd_iff_primes (t : Finset ℕ) (ht : ∀ q ∈ t, q.Prime) (m : ℕ) :
    (∏ q ∈ t, q) ∣ m ↔ ∀ q ∈ t, q ∣ m := by
  constructor
  · intro h q hq; exact dvd_trans (Finset.dvd_prod_of_mem _ hq) h
  · intro h
    apply Finset.prod_primes_dvd
    · intro q hq; exact (ht q hq).prime
    · intro q hq; exact h q hq

theorem HB_eq (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) (K : ℕ) :
    HB s K = ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) * ((1 / ((∏ q ∈ t, q : ℕ) : ℝ)) *
      ∑ j ∈ Icc 1 (K / ∏ q ∈ t, q), (1 : ℝ) / j) := by
  classical
  have hind : ∀ m : ℕ, (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) else 0) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) * (if (∏ q ∈ t, q) ∣ m then 1 else 0) := by
    intro m
    have h1 : (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) else 0) =
        ∏ q ∈ s, (1 + (-(if q ∣ m then (1 : ℝ) else 0))) := by
      rw [← Finset.prod_boole]
      apply Finset.prod_congr rfl; intro q _
      split_ifs <;> simp_all
    rw [h1, Finset.prod_one_add]
    apply Finset.sum_congr rfl; intro t ht
    rw [mem_powerset] at ht
    rw [Finset.prod_neg, Finset.prod_boole]
    congr 1
    have := prod_dvd_iff_primes t (fun q hq => hs q (ht hq)) m
    simp only [this]
  unfold HB
  rw [Finset.sum_filter]
  calc ∑ m ∈ Icc 1 K, (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) / m else 0)
      = ∑ m ∈ Icc 1 K, (1 : ℝ) / m * (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro m _; split_ifs <;> simp
    _ = ∑ m ∈ Icc 1 K, ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) *
          ((1 : ℝ) / m * (if (∏ q ∈ t, q) ∣ m then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro m _
        rw [hind, Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
    _ = ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) *
          ∑ m ∈ (Icc 1 K).filter (fun m => (∏ q ∈ t, q) ∣ m), (1 : ℝ) / m := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro t _
        rw [← Finset.mul_sum, Finset.sum_filter]
        congr 1; apply Finset.sum_congr rfl; intro m _; split_ifs <;> simp
    _ = _ := by
        apply Finset.sum_congr rfl; intro t ht
        rw [mem_powerset] at ht
        have hd : 0 < ∏ q ∈ t, q := Finset.prod_pos (fun q hq => (hs q (ht hq)).pos)
        rw [sum_Icc_dvd _ K hd]

/-- `|H(⌊K/d⌋) − log(K/d)| ≤ 2 + log d` for `K, d ≥ 1`. -/
theorem harm_div_approx (K d : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) :
    |∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j - Real.log ((K : ℝ) / d)| ≤ 2 + Real.log d := by
  have hH : ∀ n : ℕ, ∑ j ∈ Icc 1 n, (1 : ℝ) / j = (harmonic n : ℝ) := by
    intro n; rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rw [hH]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  rcases Nat.lt_or_ge K d with hKd | hKd
  · -- `K/d = 0`
    rw [Nat.div_eq_of_lt hKd, harmonic_zero]
    simp only [Rat.cast_zero, zero_sub, abs_neg]
    have h1 : Real.log ((K : ℝ) / d) ≤ 0 := by
      apply Real.log_nonpos (by positivity)
      rw [div_le_one hd0]; exact_mod_cast hKd.le
    have h2 : -Real.log d ≤ Real.log ((K : ℝ) / d) := by
      rw [Real.log_div hK0.ne' hd0.ne']
      linarith [Real.log_nonneg (by exact_mod_cast hK : (1 : ℝ) ≤ K)]
    rw [abs_of_nonpos h1]; linarith
  · set n := K / d with hn
    have hn1 : 1 ≤ n := Nat.div_pos hKd (by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlow : (n : ℝ) ≤ (K : ℝ) / d := by
      rw [le_div_iff₀ hd0]; exact_mod_cast Nat.div_mul_le_self K d
    have hhigh : (K : ℝ) / d ≤ 2 * n := by
      rw [div_le_iff₀ hd0]
      have : K < (n + 1) * d := by rw [hn, add_mul, one_mul]; exact Nat.lt_div_mul_add (by omega)
      have h2 : ((K : ℕ) : ℝ) < ((n : ℝ) + 1) * d := by exact_mod_cast this
      have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    have hl1 : Real.log n ≤ Real.log ((K : ℝ) / d) := Real.log_le_log hn0 hlow
    have hl2 : Real.log ((K : ℝ) / d) ≤ Real.log 2 + Real.log n := by
      rw [← Real.log_mul (by norm_num) hn0.ne']; exact Real.log_le_log (by positivity) hhigh
    have hh1 := harmonic_le_one_add_log n
    have hh2 := log_add_one_le_harmonic n
    have hh3 : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
    have hl2' := Real.log_two_lt_d9
    rw [abs_le]; constructor <;> push_cast at hh2 <;> linarith

theorem beta_eq (s : Finset ℕ) :
    ∏ q ∈ s, (1 - 1 / (q : ℝ)) = ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) * (1 / ((∏ q ∈ t, q : ℕ) : ℝ)) := by
  rw [show (∏ q ∈ s, (1 - 1 / (q : ℝ))) = ∏ q ∈ s, (1 + (-(1 / (q : ℝ)))) by
    apply Finset.prod_congr rfl; intro q _; ring, Finset.prod_one_add]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.prod_neg, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]

/-- `H_s(K) = β log K + O_s(1)` with `β = Π_{q ∈ s}(1 − 1/q)`. -/
theorem HB_approx (s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) (K : ℕ) (hK : 1 ≤ K) :
    |HB s K - (∏ q ∈ s, (1 - 1 / (q : ℝ))) * Real.log K| ≤
      2 ^ (#s) * (2 + 2 * Real.log (∏ q ∈ s, q : ℕ)) := by
  classical
  rw [HB_eq s hs K, beta_eq, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hP1 : 1 ≤ ∏ q ∈ s, q := Finset.one_le_prod (fun q hq => (hs q hq).one_lt.le)
  calc _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (#t) * ((1 / ((∏ q ∈ t, q : ℕ) : ℝ)) *
          ∑ j ∈ Icc 1 (K / ∏ q ∈ t, q), (1 : ℝ) / j) -
          (-1 : ℝ) ^ (#t) * (1 / ((∏ q ∈ t, q : ℕ) : ℝ)) * Real.log K| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ s.powerset, (2 + 2 * Real.log (∏ q ∈ s, q : ℕ)) := by
        apply Finset.sum_le_sum; intro t ht
        rw [mem_powerset] at ht
        set d := ∏ q ∈ t, q with hd
        have hd1 : 1 ≤ d := Finset.one_le_prod (fun q hq => (hs q (ht hq)).one_lt.le)
        have hdP : d ≤ ∏ q ∈ s, q := Nat.le_of_dvd (by omega) (Finset.prod_dvd_prod_of_subset _ _ _ ht)
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
        have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
        have hlogdP : Real.log d ≤ Real.log (∏ q ∈ s, q : ℕ) :=
          Real.log_le_log hd0 (by exact_mod_cast hdP)
        have happ := harm_div_approx K d hK hd1
        have e : (-1 : ℝ) ^ (#t) * ((1 / (d : ℝ)) * ∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j) -
            (-1 : ℝ) ^ (#t) * (1 / (d : ℝ)) * Real.log K =
            (-1 : ℝ) ^ (#t) * (1 / (d : ℝ)) *
              ((∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j - Real.log ((K : ℝ) / d)) - Real.log d) := by
          rw [Real.log_div hK0.ne' hd0.ne']; ring
        rw [e, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have hinv : |1 / (d : ℝ)| ≤ 1 := by
          rw [abs_of_pos (by positivity)]; rw [div_le_one hd0]; exact_mod_cast hd1
        have hin : |(∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j - Real.log ((K : ℝ) / d)) - Real.log d| ≤
            2 + 2 * Real.log (∏ q ∈ s, q : ℕ) := by
          calc _ ≤ |∑ j ∈ Icc 1 (K / d), (1 : ℝ) / j - Real.log ((K : ℝ) / d)| + |Real.log d| :=
                abs_sub _ _
            _ ≤ (2 + Real.log d) + Real.log d := by rw [abs_of_nonneg hlogd]; linarith
            _ ≤ _ := by linarith
        calc |1 / (d : ℝ)| * _ ≤ 1 * (2 + 2 * Real.log (∏ q ∈ s, q : ℕ)) :=
              mul_le_mul hinv hin (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _
    _ = _ := by rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]; push_cast; ring

end Palprimes
