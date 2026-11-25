import KappaOmega2.Statements
import Palprimes.Sieve.SelbergSum

namespace KappaOmega2.S11c

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-! Shared core for S11 (copy of the S12 core): facts on `𝒟`, supports of `lamA`, divisibility into `radLt`. -/

lemma c_mem (y : ℝ) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) :
    δ ∣ primorialLt (y ^ UU) ∧ δ ≠ 1 ∧ chibar y mm δ = 1 ∧ Odd (ω δ) ∧ (ω δ : ℝ) ≤ 1 / mm := by
  classical
  unfold Dset at h
  rw [Finset.mem_filter, Nat.mem_divisors] at h
  exact ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma c_chi (y m : ℝ) (δ : ℕ) (h1 : δ ≠ 1) (h : chibar y m δ = 1) :
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

lemma c_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Squarefree (∏ p ∈ P, p) :=
  SelbergPort.prod_primes_squarefree P hP

lemma c_primorial (z : ℝ) (δ : ℕ) (h : δ ∣ primorialLt z) (hδ : δ ≠ 0) :
    Squarefree δ ∧ ∀ p ∈ δ.primeFactors, (p : ℝ) < z := by
  have hsq := c_prod (primesBelow z) (fun p hp => ((mem_primesBelow z p).1 hp).1)
  refine ⟨hsq.squarefree_of_dvd h, fun p hp => ?_⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ ∏ q ∈ primesBelow z, q := (Nat.dvd_of_mem_primeFactors hp).trans h
  obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hpp.prime hpd
  have := (Nat.prime_dvd_prime_iff_eq hpp ((mem_primesBelow z q).1 hq).1).1 hpq
  rw [this]; exact ((mem_primesBelow z q).1 hq).2

/-- The violating divisor contains `p(δ)`, so `y ≤ δ p(δ)²`. -/
lemma c_y_le (y : ℝ) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
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


lemma c_supp (b : ℕ) (e : StepFn) (x : ℝ) (d : ℕ) (h : lamA b e x d ≠ 0) :
    Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) < Real.sqrt x := by
  classical
  unfold lamA at h
  by_cases hc : Nat.Coprime d (bigB b)
  swap
  · rw [if_neg hc] at h; exact absurd rfl h
  rw [if_pos hc] at h
  have h2 : ∑ k ∈ (ltSet (Real.sqrt x)).filter (fun k => d ∣ k), (μ (k / d) : ℝ) * ykA b e x k ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  rw [Finset.mem_filter] at hk
  have hμ : (μ k : ℝ) ≠ 0 := by
    intro h0; apply hk0; unfold ykA; rw [h0]; ring
  have hsq : Squarefree k := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 (by exact_mod_cast hμ)
  have hk1 := hk.1
  unfold ltSet at hk1
  rw [Finset.mem_filter, Finset.mem_range] at hk1
  have hdk : d ≤ k := Nat.le_of_dvd (by omega) hk.2
  refine ⟨hsq.squarefree_of_dvd hk.2, ?_, lt_of_le_of_lt (by exact_mod_cast hdk) hk1.2.2⟩
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · subst h0; simp at hk; omega
  · exact h0


lemma c_dvd_primorial (z : ℝ) (m : ℕ) (hsq : Squarefree m) (hz : ∀ p ∈ m.primeFactors, (p : ℝ) < z) :
    m ∣ primorialLt z := by
  unfold primorialLt
  have : m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
  conv_lhs => rw [this]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  exact (mem_primesBelow z p).2 ⟨Nat.prime_of_mem_primeFactors hp, hz p hp⟩

lemma c_rad_dvd (a : ℕ) (ha : a ≠ 0) (z : ℝ) : radLt a z ∣ a ∧ radLt a z ∣ primorialLt z ∧ radLt a z ≠ 0 := by
  classical
  unfold radLt primorialLt
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.prod_primes_dvd a
    · intro p hp; exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime
    · intro p hp; exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  · apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have := Finset.mem_filter.1 hp
    exact (mem_primesBelow z p).2 ⟨Nat.prime_of_mem_primeFactors this.1, this.2⟩
  · exact Finset.prod_ne_zero_iff.2 (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).ne_zero)

lemma c_dvd_rad (a : ℕ) (ha : a ≠ 0) (z : ℝ) (m : ℕ) (hm : m ∣ primorialLt z) :
    m ∣ a ↔ m ∣ radLt a z := by
  classical
  obtain ⟨h1, h2, h3⟩ := c_rad_dvd a ha z
  constructor
  · intro hma
    have hP : primorialLt z ≠ 0 := by
      unfold primorialLt
      exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
    have hm0 : m ≠ 0 := by rintro rfl; exact hP (zero_dvd_iff.1 hm)
    obtain ⟨hsq, hpz⟩ := c_primorial z m hm hm0
    have : m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    unfold radLt
    conv_lhs => rw [this]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hma, ha⟩, hpz p hp⟩
  · intro h; exact h.trans h1

/-- Facts on `δ ∈ 𝒟`. -/
lemma c_Dfacts (y : ℝ) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) :
    δ ≠ 0 ∧ δ ≠ 1 ∧ Squarefree δ ∧ δ ∣ primorialLt (y ^ UU) ∧ (∀ p ∈ δ.primeFactors, (p : ℝ) < y ^ UU) ∧
      y ≤ (δ : ℝ) * (δ.minFac : ℝ) ^ 2 := by
  obtain ⟨hdvd, h1, hchi, hodd, hω⟩ := c_mem y δ h
  have hPne : primorialLt (y ^ UU) ≠ 0 := by
    unfold primorialLt
    exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hPne (zero_dvd_iff.1 hdvd)
  obtain ⟨hsq, hpz⟩ := c_primorial (y ^ UU) δ hdvd hδ0
  obtain ⟨hc1, hc0⟩ := c_chi y mm δ h1 hchi
  exact ⟨hδ0, h1, hsq, hdvd, hpz, c_y_le y δ hsq h1 hc1 hc0⟩

/-- Elements of `ltSet (√(y/δ))` are below `p(δ)`, hence coprime to `δ`. -/
lemma c_small (y : ℝ) (hy : 1 < y) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) (d : ℕ)
    (hd : d ∈ ltSet (Real.sqrt (y / δ))) : (d : ℝ) < δ.minFac ∧ Nat.Coprime d δ := by
  obtain ⟨hδ0, h1, hsq, hdvd, hpz, hyle⟩ := c_Dfacts y δ h
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
  unfold ltSet at hd
  rw [Finset.mem_filter, Finset.mem_range] at hd
  have hdlt := hd.2.2
  have hsq_le : Real.sqrt (y / δ) ≤ (δ.minFac : ℝ) := by
    apply Real.sqrt_le_iff.2
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rw [div_le_iff₀ hδpos]; linarith
  have hlt : (d : ℝ) < δ.minFac := lt_of_lt_of_le hdlt hsq_le
  refine ⟨hlt, ?_⟩
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq hqδ hqd
  have h2 : δ.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqδ
  have h3 : q ≤ d := Nat.le_of_dvd (by omega) hqd
  have h2' : (δ.minFac : ℝ) ≤ q := by exact_mod_cast h2
  have h3' : (q : ℝ) ≤ d := by exact_mod_cast h3
  linarith

lemma c_sqf_lcm (d1 d2 : ℕ) (h1 : Squarefree d1) (h2 : Squarefree d2) : Squarefree (Nat.lcm d1 d2) := by
  have h10 := h1.ne_zero
  have h20 := h2.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero h10 h20)]
  intro p
  rw [Nat.factorization_lcm h10 h20, Finsupp.sup_apply]
  have a1 := (Nat.squarefree_iff_factorization_le_one h10).1 h1 p
  have a2 := (Nat.squarefree_iff_factorization_le_one h20).1 h2 p
  exact max_le a1 a2

lemma c_coprime_lcm (d1 d2 δ : ℕ) (h1 : Nat.Coprime d1 δ) (h2 : Nat.Coprime d2 δ) :
    Nat.Coprime (Nat.lcm d1 d2) δ :=
  Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul d1 d2) (Nat.Coprime.mul_left h1 h2)

lemma c_sqrt_lt (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : 1 ≤ δ) : Real.sqrt (y / δ) < y ^ UU := by
  have hδ' : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have h1 : Real.sqrt (y / δ) ≤ Real.sqrt y := by
    apply Real.sqrt_le_sqrt
    exact div_le_self (by linarith) hδ'
  have h2 : Real.sqrt y = y ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
  have h3 : y ^ ((1 : ℝ) / 2) < y ^ UU := by
    apply Real.rpow_lt_rpow_of_exponent_lt hy
    unfold UU; norm_num
  linarith


lemma c_lcm_dvdP (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm)
    (d1 d2 : ℕ) (h1 : d1 ∈ ltSet (Real.sqrt (y / δ))) (h2 : d2 ∈ ltSet (Real.sqrt (y / δ)))
    (s1 : Squarefree d1) (s2 : Squarefree d2) :
    Squarefree (Nat.lcm d1 d2 * δ) ∧ Nat.Coprime (Nat.lcm d1 d2) δ ∧ Nat.lcm d1 d2 * δ ∣ primorialLt (y ^ UU) := by
  obtain ⟨hδ0, hδ1, hsqδ, hdvd, hpz, hyle⟩ := c_Dfacts y δ hδ
  obtain ⟨hlt1, hc1⟩ := c_small y hy δ hδ d1 h1
  obtain ⟨hlt2, hc2⟩ := c_small y hy δ hδ d2 h2
  have hzlt := c_sqrt_lt y hy δ (Nat.one_le_iff_ne_zero.2 hδ0)
  have hℓsq : Squarefree (Nat.lcm d1 d2) := c_sqf_lcm d1 d2 s1 s2
  have hℓc : Nat.Coprime (Nat.lcm d1 d2) δ := c_coprime_lcm d1 d2 δ hc1 hc2
  have hsq : Squarefree (Nat.lcm d1 d2 * δ) := Nat.squarefree_mul_iff.2 ⟨hℓc, hℓsq, hsqδ⟩
  have hd1 : (d1 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at h1; rw [Finset.mem_filter] at h1; exact h1.2.2
  have hd2 : (d2 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at h2; rw [Finset.mem_filter] at h2; exact h2.2.2
  have hzp : ∀ p ∈ (Nat.lcm d1 d2 * δ).primeFactors, (p : ℝ) < y ^ UU := by
    intro p hp
    rw [Nat.primeFactors_mul hℓsq.ne_zero hδ0, Finset.mem_union] at hp
    rcases hp with hp | hp
    · have hpℓ := Nat.dvd_of_mem_primeFactors hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have : p ∣ d1 * d2 := hpℓ.trans (Nat.lcm_dvd_mul d1 d2)
      rcases (Nat.Prime.dvd_mul hpp).1 this with h | h
      · have : (p : ℝ) ≤ d1 := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s1.ne_zero) h
        linarith
      · have : (p : ℝ) ≤ d2 := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s2.ne_zero) h
        linarith
    · exact hpz p hp
  exact ⟨hsq, hℓc, c_dvd_primorial _ _ hsq hzp⟩

/-- The geometric tail induction. -/
lemma c_tail (t : ℕ → ℝ) : ∀ (Q : Finset ℕ),
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


lemma c_minFac_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (q : ℕ) (hq : q ∈ E) (hmin : ∀ x ∈ E, q ≤ x) :
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

lemma c_rho (y : ℝ) (hy : 1 < y) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
    (hc1 : chiProp y mm (δ / δ.minFac)) (hν : δ.primeFactors.card ≤ 51) (hν2 : 2 ≤ δ.primeFactors.card) :
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
    have hmf := c_minFac_prod hTp q hqT (fun x hx => (Finset.mem_filter.1 hx).2)
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
      have : (T.card : ℝ) ≤ 51 := by
        have : T.card ≤ 51 := by omega
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
  have hmain := c_tail t Q htail 2 ρ hsum
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


theorem c_ydelta (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm) :
    y ^ ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84) ≤ y / δ := by
  classical
  obtain ⟨hdvd, h1, hchi, hodd, hω⟩ := c_mem y δ hδ
  have hPne : primorialLt (y ^ UU) ≠ 0 := by
    unfold primorialLt
    exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hPne (zero_dvd_iff.1 hdvd)
  obtain ⟨hsq, hpz⟩ := c_primorial (y ^ UU) δ hdvd hδ0
  obtain ⟨hc1, hc0⟩ := c_chi y mm δ h1 hchi
  have hcard : δ.primeFactors.card ≤ 51 := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hω
    unfold mm at hω
    have : (δ.primeFactors.card : ℝ) < 52 := by norm_num at hω; linarith
    have : δ.primeFactors.card < 52 := by exact_mod_cast this
    omega
  by_cases h2 : 2 ≤ δ.primeFactors.card
  · exact c_rho y hy δ hsq h1 hc1 hcard h2
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
      have : (2 / 3 : ℝ) ^ 84 ≤ 8 / 103 := by norm_num
      linarith
    calc y ^ ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84) ≤ y ^ ((1 : ℝ) - UU) :=
          Real.rpow_le_rpow_of_exponent_le hy.le hcc
      _ = y / y ^ UU := hyU
      _ ≤ y / δ := by
          apply div_le_div_of_nonneg_left (by linarith) hδpos hδy.le

end KappaOmega2.S11c
