import Omega3.Statements
import Palprimes.Sieve.SelbergSum

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-! Item S13: facts on `𝒟`. -/

/-- The geometric tail induction. -/
lemma s13_tail (t : ℕ → ℝ) : ∀ (Q : Finset ℕ),
    (∀ q ∈ Q, 2 * t q + ∑ x ∈ Q.filter (fun x => q ≤ x), t x < 1) →
    ∀ B ρ : ℝ, 1 - B * ρ < ∑ x ∈ Q, t x → 1 < B * (3 / 2) ^ Q.card * ρ := by
  intro Q
  induction Q using Finset.induction_on_min with
  | empty =>
    intro _ B ρ h
    simpa using h
  | insert a s hmin ih =>
    intro hcond B ρ h
    have has : a ∉ s := fun h' => lt_irrefl a (hmin a h')
    have hfa : (insert a s).filter (fun x => a ≤ x) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact (hmin x hx).le
    have h1 := hcond a (Finset.mem_insert_self a s)
    rw [hfa, Finset.sum_insert has] at h1
    rw [Finset.sum_insert has] at h
    have hta : t a < B * ρ / 2 := by linarith
    have h2 : ∀ q ∈ s, 2 * t q + ∑ x ∈ s.filter (fun x => q ≤ x), t x < 1 := by
      intro q hq
      have := hcond q (Finset.mem_insert_of_mem hq)
      have e : (insert a s).filter (fun x => q ≤ x) = s.filter (fun x => q ≤ x) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx | hx, hqx⟩
          · exact absurd (hmin q hq) (not_lt.2 (hx ▸ hqx))
          · exact ⟨hx, hqx⟩
        · rintro ⟨hx, hqx⟩; exact ⟨Or.inr hx, hqx⟩
      rwa [e] at this
    have := ih h2 (3 / 2 * B) ρ (by linarith)
    rw [Finset.card_insert_of_notMem has, pow_succ]
    nlinarith

lemma s13_mem (y : ℝ) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) :
    δ ∣ primorialLt (y ^ UU) ∧ δ ≠ 1 ∧ chibar y mm δ = 1 ∧ Odd (ω δ) ∧ (ω δ : ℝ) ≤ 1 / mm := by
  classical
  unfold Dset at h
  rw [Finset.mem_filter, Nat.mem_divisors] at h
  exact ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma s13_chi (y m : ℝ) (δ : ℕ) (h1 : δ ≠ 1) (h : chibar y m δ = 1) :
    chiProp y m (δ / δ.minFac) ∧ ¬ chiProp y m δ := by
  classical
  unfold chibar at h
  rw [if_neg h1] at h
  unfold chi at h
  by_cases ha : chiProp y m (δ / δ.minFac)
  · by_cases hb : chiProp y m δ
    · simp [ha, hb] at h
    · exact ⟨ha, hb⟩
  · by_cases hb : chiProp y m δ
    · simp [ha, hb] at h; norm_num at h
    · simp [ha, hb] at h

lemma s13_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Squarefree (∏ p ∈ P, p) :=
  SelbergPort.prod_primes_squarefree P hP

lemma s13_primorial (z : ℝ) (δ : ℕ) (h : δ ∣ primorialLt z) (hδ : δ ≠ 0) :
    Squarefree δ ∧ ∀ p ∈ δ.primeFactors, (p : ℝ) < z := by
  have hsq := s13_prod (primesBelow z) (fun p hp => ((mem_primesBelow z p).1 hp).1)
  refine ⟨hsq.squarefree_of_dvd h, fun p hp => ?_⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ ∏ q ∈ primesBelow z, q := (Nat.dvd_of_mem_primeFactors hp).trans h
  obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hpp.prime hpd
  have := (Nat.prime_dvd_prime_iff_eq hpp ((mem_primesBelow z q).1 hq).1).1 hpq
  rw [this]; exact ((mem_primesBelow z q).1 hq).2

/-- The violating divisor contains `p(δ)`, so `y ≤ δ p(δ)²`. -/
lemma s13_y_le (y : ℝ) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
    (hc1 : chiProp y mm (δ / δ.minFac)) (hc0 : ¬ chiProp y mm δ) :
    y ≤ (δ : ℝ) * (δ.minFac : ℝ) ^ 2 := by
  classical
  unfold chiProp at hc0
  push Not at hc0
  obtain ⟨h, hh, hne, hcond, hge⟩ := hc0
  rw [Nat.mem_divisors] at hh
  have hδ0 : δ ≠ 0 := hsq.ne_zero
  set p := δ.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpδ : p ∣ δ := Nat.minFac_dvd δ
  obtain ⟨c, hc⟩ := hpδ
  have hdivc : δ / p = c := by rw [hc]; exact Nat.mul_div_cancel_left c hp.pos
  have hnd : ¬ h ∣ c := by
    intro hd
    have := hc1 h (by rw [Nat.mem_divisors, hdivc]; exact ⟨hd, by rintro rfl; simp at hc; exact hδ0 hc⟩) hne hcond
    linarith
  have hph : p ∣ h := by
    by_contra hnp
    apply hnd
    have hcop : Nat.Coprime h p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnp).symm
    have : h ∣ p * c := by rw [← hc]; exact hh.1
    exact hcop.dvd_of_dvd_mul_left this
  have hmf : h.minFac = p := by
    apply le_antisymm
    · exact Nat.minFac_le_of_dvd hp.two_le hph
    · exact Nat.minFac_le_of_dvd (Nat.minFac_prime hne).two_le ((Nat.minFac_dvd h).trans hh.1)
  rw [hmf] at hge
  have hle : (h : ℝ) ≤ δ := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) hh.1
  calc y ≤ (h : ℝ) * (p : ℝ) ^ 2 := hge
    _ ≤ (δ : ℝ) * (p : ℝ) ^ 2 := by gcongr

lemma s13_minFac_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (q : ℕ) (hq : q ∈ E) (hmin : ∀ x ∈ E, q ≤ x) :
    (∏ p ∈ E, p).minFac = q := by
  have h1 : (∏ p ∈ E, p) ≠ 1 := by
    intro h
    have := Finset.dvd_prod_of_mem (fun p => p) hq
    rw [h] at this
    exact (hE q hq).ne_one (Nat.dvd_one.1 this)
  have hpos : 0 < ∏ p ∈ E, p := Finset.prod_pos (fun p hp => (hE p hp).pos)
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd (hE q hq).two_le (Finset.dvd_prod_of_mem _ hq)
  · have hmem : (∏ p ∈ E, p).minFac ∈ (∏ p ∈ E, p).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.minFac_prime h1, Nat.minFac_dvd _, hpos.ne'⟩
    rw [Nat.primeFactors_prod hE] at hmem
    exact hmin _ hmem

lemma s13_rho (y : ℝ) (hy : 1 < y) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
    (hc1 : chiProp y mm (δ / δ.minFac)) (hν : δ.primeFactors.card ≤ 85) (hν2 : 2 ≤ δ.primeFactors.card) :
    y ^ ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84) ≤ y / δ := by
  classical
  have hL : 0 < Real.log y := Real.log_pos hy
  have hδ0 : δ ≠ 0 := hsq.ne_zero
  set p := δ.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpmem : p ∈ δ.primeFactors := Nat.mem_primeFactors.2 ⟨hp, Nat.minFac_dvd δ, hδ0⟩
  set Q := δ.primeFactors.erase p with hQ
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  have hQmin : ∀ q ∈ Q, p < q := by
    intro q hq
    have hqδ := Finset.mem_of_mem_erase hq
    have hne := (Finset.mem_erase.1 hq).1
    have : p ≤ q := Nat.minFac_le_of_dvd (hQp q hq).two_le (Nat.dvd_of_mem_primeFactors hqδ)
    exact lt_of_le_of_ne this (Ne.symm hne)
  have hδprod : δ = p * ∏ q ∈ Q, q := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    rw [← Finset.mul_prod_erase δ.primeFactors (fun x => x) hpmem]
  have hQcard : Q.card = δ.primeFactors.card - 1 := Finset.card_erase_of_mem hpmem
  have hdivQ : δ / p = ∏ q ∈ Q, q := by
    rw [hδprod]; exact Nat.mul_div_cancel_left _ hp.pos
  set t : ℕ → ℝ := fun x => Real.log x / Real.log y with ht
  have htail : ∀ q ∈ Q, 2 * t q + ∑ x ∈ Q.filter (fun x => q ≤ x), t x < 1 := by
    intro q hq
    set T := Q.filter (fun x => q ≤ x) with hT
    have hTp : ∀ x ∈ T, x.Prime := fun x hx => hQp x (Finset.mem_filter.1 hx).1
    have hqT : q ∈ T := Finset.mem_filter.2 ⟨hq, le_rfl⟩
    have hmf := s13_minFac_prod hTp q hqT (fun x hx => (Finset.mem_filter.1 hx).2)
    have hTpos : 0 < ∏ x ∈ T, x := Finset.prod_pos (fun x hx => (hTp x hx).pos)
    have hne1 : (∏ x ∈ T, x) ≠ 1 := by
      intro h
      have := Finset.dvd_prod_of_mem (fun x => x) hqT
      rw [h] at this
      exact (hQp q hq).ne_one (Nat.dvd_one.1 this)
    have hdvd : (∏ x ∈ T, x) ∣ δ / p := by
      rw [hdivQ]; exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    have hω : ((ω (∏ x ∈ T, x) : ℕ) : ℝ) ≤ 1 / mm := by
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_prod hTp]
      have : T.card ≤ Q.card := Finset.card_le_card (Finset.filter_subset _ _)
      unfold mm
      have : (T.card : ℝ) ≤ 85 := by
        have : T.card ≤ 85 := by omega
        exact_mod_cast this
      linarith
    have hlt := hc1 (∏ x ∈ T, x) (by rw [Nat.mem_divisors]; exact ⟨hdvd, by rw [hdivQ]; exact (Finset.prod_pos (fun x hx => (hQp x hx).pos)).ne'⟩)
      hne1 (Or.inr hω)
    rw [hmf] at hlt
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQp q hq).pos
    have hlog : Real.log (((∏ x ∈ T, x : ℕ) : ℝ) * (q : ℝ) ^ 2) < Real.log y :=
      Real.log_lt_log (mul_pos (by exact_mod_cast hTpos) (pow_pos hq0 2)) hlt
    rw [Real.log_mul (by exact_mod_cast hTpos.ne') (by positivity), Real.log_pow, Nat.cast_prod,
      Real.log_prod (fun x hx => by exact_mod_cast (hTp x hx).ne_zero)] at hlog
    have : 2 * t q + ∑ x ∈ T, t x = (2 * Real.log q + ∑ x ∈ T, Real.log x) / Real.log y := by
      simp only [ht]; rw [← Finset.sum_div]; ring
    rw [this, div_lt_one hL]
    push_cast at hlog
    linarith
  -- ρ
  set ρ : ℝ := 1 - t p - ∑ x ∈ Q, t x with hρ
  have hQne : Q.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hq2 := Finset.min'_mem Q hQne
  set q2 := Q.min' hQne with hq2def
  have hfilt : Q.filter (fun x => q2 ≤ x) = Q := Finset.filter_true_of_mem (fun x hx => Finset.min'_le Q x hx)
  have hc2 := htail q2 hq2
  rw [hfilt] at hc2
  have htp : t p < t q2 := by
    simp only [ht]
    apply div_lt_div_of_pos_right _ hL
    apply Real.log_lt_log (by exact_mod_cast hp.pos)
    exact_mod_cast hQmin q2 hq2
  have htp2 : t p < ρ := by rw [hρ]; linarith
  have hsum : 1 - 2 * ρ < ∑ x ∈ Q, t x := by rw [hρ] at *; linarith
  have hmain := s13_tail t Q htail 2 ρ hsum
  have hρ0 : 0 < ρ := by
    by_contra hneg
    push Not at hneg
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3 / 2) Q.card]
  have hgen : ∀ N0 : ℕ, Q.card ≤ N0 → (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ N0 ≤ ρ := by
    intro N0 hN0
    have hcard : (3 / 2 : ℝ) ^ Q.card ≤ (3 / 2 : ℝ) ^ N0 := pow_le_pow_right₀ (by norm_num) hN0
    have h2 : 1 < 2 * (3 / 2 : ℝ) ^ N0 * ρ := by nlinarith
    have e : (2 / 3 : ℝ) ^ N0 * (3 / 2 : ℝ) ^ N0 = 1 := by
      rw [← mul_pow]; norm_num
    have hd : 0 < (3 / 2 : ℝ) ^ N0 := pow_pos (by norm_num) _
    have hc : 0 < (2 / 3 : ℝ) ^ N0 := pow_pos (by norm_num) _
    nlinarith
  have hρc : (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 ≤ ρ := hgen 84 (by omega)
  -- y/δ = y^ρ
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
  have hlogδ : Real.log δ = Real.log p + ∑ x ∈ Q, Real.log x := by
    conv_lhs => rw [hδprod]
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero) (by
      exact_mod_cast (Finset.prod_pos (fun x hx => (hQp x hx).pos)).ne'), Nat.cast_prod,
      Real.log_prod (fun x hx => by exact_mod_cast (hQp x hx).ne_zero)]
  have hyδ : y / δ = y ^ ρ := by
    have hlog : Real.log (y / δ) = Real.log y * ρ := by
      rw [Real.log_div (by linarith) hδpos.ne', hρ, hlogδ]
      simp only [ht]
      rw [← Finset.sum_div]
      field_simp
      ring
    rw [Real.rpow_def_of_pos (by linarith), ← hlog, Real.exp_log (by positivity)]
  rw [hyδ]
  exact Real.rpow_le_rpow_of_exponent_le hy.le hρc

theorem itemS13 : ItemS13 := by
  classical
  intro y hy δ hδ
  obtain ⟨hdvd, h1, hchi, hodd, hω⟩ := s13_mem y δ hδ
  have hPne : primorialLt (y ^ UU) ≠ 0 := by
    unfold primorialLt
    exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hPne (zero_dvd_iff.1 hdvd)
  obtain ⟨hsq, hpz⟩ := s13_primorial (y ^ UU) δ hdvd hδ0
  obtain ⟨hc1, hc0⟩ := s13_chi y mm δ h1 hchi
  have hcard : δ.primeFactors.card ≤ 85 := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hω
    unfold mm at hω
    have : (δ.primeFactors.card : ℝ) ≤ 85 := by linarith
    exact_mod_cast this
  refine ⟨hsq, hpz, s13_y_le y δ hsq h1 hc1 hc0, ?_⟩
  by_cases h2 : 2 ≤ δ.primeFactors.card
  · exact s13_rho y hy δ hsq h1 hc1 hcard h2
  · -- δ is prime
    have hc : δ.primeFactors.card = 1 := by
      have : 0 < δ.primeFactors.card := by
        rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hodd
        obtain ⟨k, hk⟩ := hodd; omega
      omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
    have hpδ : δ = p := by
      have := Nat.prod_primeFactors_of_squarefree hsq
      rw [hp] at this; simpa using this.symm
    have hpmem : p ∈ δ.primeFactors := by rw [hp]; simp
    have hlt := hpz p hpmem
    have hδy : (δ : ℝ) < y ^ UU := by rw [hpδ]; exact hlt
    have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
    have hyU : y ^ ((1 : ℝ) - UU) = y / y ^ UU := by
      rw [Real.rpow_sub (by linarith), Real.rpow_one]
    have hcc : (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 ≤ 1 - UU := by
      unfold UU
      have : (2 / 3 : ℝ) ^ 84 ≤ 4 / 85 := by norm_num
      linarith
    calc y ^ ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84) ≤ y ^ ((1 : ℝ) - UU) :=
          Real.rpow_le_rpow_of_exponent_le hy.le hcc
      _ = y / y ^ UU := hyU
      _ ≤ y / δ := by
          apply div_le_div_of_nonneg_left (by linarith) hδpos hδy.le

end Omega3
