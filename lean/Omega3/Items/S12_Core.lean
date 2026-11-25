import Omega3.Statements
import Palprimes.Sieve.SelbergSum

namespace Omega3.S12c

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-! Shared core for S12 / M01 / S11: facts on `𝒟`, supports of `lamA`, divisibility into `radLt`. -/

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

end Omega3.S12c
