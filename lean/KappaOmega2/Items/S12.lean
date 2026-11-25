import KappaOmega2.Statements
import KappaOmega2.Items.S12_Core

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves KappaOmega2.S12c
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma s12_sqf_lcm (d1 d2 : ℕ) (h1 : Squarefree d1) (h2 : Squarefree d2) : Squarefree (Nat.lcm d1 d2) := by
  have h10 := h1.ne_zero
  have h20 := h2.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero h10 h20)]
  intro p
  rw [Nat.factorization_lcm h10 h20, Finsupp.sup_apply]
  have a1 := (Nat.squarefree_iff_factorization_le_one h10).1 h1 p
  have a2 := (Nat.squarefree_iff_factorization_le_one h20).1 h2 p
  exact max_le a1 a2

lemma s12_coprime_lcm (d1 d2 δ : ℕ) (h1 : Nat.Coprime d1 δ) (h2 : Nat.Coprime d2 δ) :
    Nat.Coprime (Nat.lcm d1 d2) δ :=
  Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul d1 d2) (Nat.Coprime.mul_left h1 h2)

lemma s12_sqrt_lt (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : 1 ≤ δ) : Real.sqrt (y / δ) < y ^ UU := by
  have hδ' : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
  have h1 : Real.sqrt (y / δ) ≤ Real.sqrt y := by
    apply Real.sqrt_le_sqrt
    exact div_le_self (by linarith) hδ'
  have h2 : Real.sqrt y = y ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
  have h3 : y ^ ((1 : ℝ) / 2) < y ^ UU := by
    apply Real.rpow_lt_rpow_of_exponent_lt hy
    unfold UU; norm_num
  linarith

lemma s12_pair (y : ℝ) (hy : 1 < y) (a : ℕ) (ha : a ≠ 0) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm)
    (d1 d2 : ℕ) (h1 : d1 ∈ ltSet (Real.sqrt (y / δ))) (h2 : d2 ∈ ltSet (Real.sqrt (y / δ)))
    (s1 : Squarefree d1) (s2 : Squarefree d2) :
    (Nat.lcm d1 d2 * δ ∣ a) ↔
      (δ ∣ radLt a (y ^ UU) ∧ Nat.lcm d1 d2 ∣ radLt a (y ^ UU) / δ) := by
  obtain ⟨hδ0, hδ1, hsqδ, hdvd, hpz, hyle⟩ := c_Dfacts y δ hδ
  obtain ⟨hlt1, hc1⟩ := c_small y hy δ hδ d1 h1
  obtain ⟨hlt2, hc2⟩ := c_small y hy δ hδ d2 h2
  have hzlt := s12_sqrt_lt y hy δ (Nat.one_le_iff_ne_zero.2 hδ0)
  set ℓ := Nat.lcm d1 d2 with hℓ
  have hℓsq : Squarefree ℓ := s12_sqf_lcm d1 d2 s1 s2
  have hℓc : Nat.Coprime ℓ δ := s12_coprime_lcm d1 d2 δ hc1 hc2
  have hsq : Squarefree (ℓ * δ) := Nat.squarefree_mul_iff.2 ⟨hℓc, hℓsq, hsqδ⟩
  have hd1 : (d1 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at h1; rw [Finset.mem_filter] at h1; exact h1.2.2
  have hd2 : (d2 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at h2; rw [Finset.mem_filter] at h2; exact h2.2.2
  have hzp : ∀ p ∈ (ℓ * δ).primeFactors, (p : ℝ) < y ^ UU := by
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
  have hdP : ℓ * δ ∣ primorialLt (y ^ UU) := c_dvd_primorial _ _ hsq hzp
  have hA := c_rad_dvd a ha (y ^ UU)
  constructor
  · intro hdiv
    have hA' : ℓ * δ ∣ radLt a (y ^ UU) := (c_dvd_rad a ha _ _ hdP).1 hdiv
    refine ⟨(dvd_mul_left δ ℓ).trans hA', ?_⟩
    apply Nat.dvd_div_of_mul_dvd
    rw [mul_comm]; exact hA'
  · rintro ⟨hδA, hℓA⟩
    have : ℓ * δ ∣ radLt a (y ^ UU) / δ * δ := Nat.mul_dvd_mul_right hℓA δ
    rw [Nat.div_mul_cancel hδA] at this
    exact this.trans hA.1

lemma s12_delta (b : ℕ) (B : BandData) (y : ℝ) (hy : 1 < y) (a : ℕ) (ha : a ≠ 0) (δ : ℕ)
    (hδ : δ ∈ Dset y (y ^ UU) mm) :
    ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ ∣ a then LamD b B y δ d1 * LamD b B y δ d2 else 0) =
      if δ ∣ radLt a (y ^ UU) then (∑ d ∈ (radLt a (y ^ UU) / δ).divisors, LamD b B y δ d) ^ 2 else 0 := by
  classical
  obtain ⟨hδ0, hδ1, hsqδ, hdvd, hpz, hyle⟩ := c_Dfacts y δ hδ
  set A := radLt a (y ^ UU) with hAdef
  set L := ltSet (Real.sqrt (y / δ)) with hL
  set Λ : ℕ → ℝ := LamD b B y δ with hΛ
  have hsupp : ∀ d, Λ d ≠ 0 → Squarefree d ∧ d ∈ L := by
    intro d hd
    have := c_supp b (etaOf B y δ) (y / δ) d hd
    refine ⟨this.1, ?_⟩
    rw [hL]; unfold ltSet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_ceil.2 this.2.2, this.2.1, this.2.2⟩
  have hA0 : A ≠ 0 := (c_rad_dvd a ha _).2.2
  have hterm : ∀ d1 ∈ L, ∀ d2 ∈ L, (if Nat.lcm d1 d2 * δ ∣ a then Λ d1 * Λ d2 else 0) =
      if δ ∣ A then (if (d1 ∣ A / δ ∧ d2 ∣ A / δ) then Λ d1 * Λ d2 else 0) else 0 := by
    intro d1 hd1 d2 hd2
    by_cases hz : Λ d1 * Λ d2 = 0
    · simp [hz]
    · have h1 : Λ d1 ≠ 0 := fun h => hz (by rw [h, zero_mul])
      have h2 : Λ d2 ≠ 0 := fun h => hz (by rw [h, mul_zero])
      have hpair := s12_pair y hy a ha δ hδ d1 d2 hd1 hd2 (hsupp d1 h1).1 (hsupp d2 h2).1
      by_cases hδA : δ ∣ A
      · by_cases hl : Nat.lcm d1 d2 ∣ A / δ
        · have := hpair.2 ⟨hδA, hl⟩
          rw [if_pos this, if_pos hδA, if_pos (Nat.lcm_dvd_iff.1 hl)]
        · have : ¬ Nat.lcm d1 d2 * δ ∣ a := fun h => hl (hpair.1 h).2
          rw [if_neg this, if_pos hδA, if_neg (fun h => hl (Nat.lcm_dvd_iff.2 h))]
      · have : ¬ Nat.lcm d1 d2 * δ ∣ a := fun h => hδA (hpair.1 h).1
        rw [if_neg this, if_neg hδA]
  rw [Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => hterm d1 hd1 d2 hd2))]
  by_cases hδA : δ ∣ A
  · simp only [if_pos hδA]
    set M := A / δ with hM
    have hM0 : M ≠ 0 := by
      intro h; rw [hM] at h
      exact hA0 (by
        have := Nat.div_mul_cancel hδA
        rw [h, zero_mul] at this; exact this.symm)
    set F := L.filter (fun d => d ∣ M) with hF
    have hsum1 : ∑ d1 ∈ L, ∑ d2 ∈ L, (if (d1 ∣ M ∧ d2 ∣ M) then Λ d1 * Λ d2 else 0) = (∑ d ∈ F, Λ d) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, hF, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d1 _
      by_cases h1 : d1 ∣ M
      · simp only [if_pos h1]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d2 _
        by_cases h2 : d2 ∣ M
        · simp [h1, h2]
        · simp [h2]
      · simp only [if_neg h1]
        apply Finset.sum_eq_zero
        intro d2 _
        simp [h1]
    have hsum2 : ∑ d ∈ F, Λ d = ∑ d ∈ M.divisors, Λ d := by
      apply Finset.sum_subset
      · intro d hd
        rw [hF, Finset.mem_filter] at hd
        exact Nat.mem_divisors.2 ⟨hd.2, hM0⟩
      · intro d hd hdF
        by_contra hne
        apply hdF
        rw [hF, Finset.mem_filter]
        exact ⟨(hsupp d hne).2, (Nat.mem_divisors.1 hd).1⟩
    rw [hsum1, hsum2]
  · simp only [if_neg hδA]
    simp

lemma s12_rad_idem (a : ℕ) (z : ℝ) : radLt (radLt a z) z = radLt a z := by
  classical
  have hP : ∀ p ∈ a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  have h1 : radLt a z = ∏ p ∈ a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p := by
    unfold radLt; congr
  rw [h1]
  unfold radLt
  rw [Nat.primeFactors_prod hP]
  congr 1
  exact Finset.filter_true_of_mem (fun p hp => (Finset.mem_filter.1 hp).2)

theorem itemS12 : ItemS12 := by
  classical
  intro b B ε y a hb hy ha1
  have ha : a ≠ 0 := by omega
  set z := y ^ UU with hz
  set A := radLt a z with hAdef
  obtain ⟨hAa, hAP, hA0⟩ := c_rad_dvd a ha z
  unfold cSieve
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- part 1
  have hpart1 : ∑ n ∈ a.divisors, (if n ∣ primorialLt z then (μ n : ℝ) * chi y mm n * phiW W1 (wy y) n else 0) =
      Sig1 y z mm W1 (wy y) A := by
    unfold Sig1
    rw [hAdef, s12_rad_idem, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hna, _⟩, hnP⟩
      exact ⟨(c_dvd_rad a ha z n hnP).1 hna, hA0⟩
    · rintro ⟨hnA, _⟩
      exact ⟨⟨hnA.trans hAa, ha⟩, hnA.trans hAP⟩
  -- part 2
  have hpart2 : ∑ n ∈ a.divisors, ∑ δ ∈ Dset y z mm, phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) =
      ∑ δ ∈ (Dset y z mm).filter (· ∣ A), phiW W1 (wy y) δ * (∑ d ∈ (A / δ).divisors, LamD b B y δ d) ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro δ hδ
    rw [← Finset.mul_sum]
    have hswap : ∑ n ∈ a.divisors, ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) =
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ ∣ a then LamD b B y δ d1 * LamD b B y δ d2 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d1 _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d2 _
      rw [Finset.sum_ite_eq]
      by_cases h : Nat.lcm d1 d2 * δ ∣ a
      · have : Nat.lcm d1 d2 * δ ∈ a.divisors := Nat.mem_divisors.2 ⟨h, ha⟩
        rw [if_pos this, if_pos h]
      · have : Nat.lcm d1 d2 * δ ∉ a.divisors := fun h' => h (Nat.mem_divisors.1 h').1
        rw [if_neg this, if_neg h]
    rw [hswap, s12_delta b B y hy a ha δ hδ, ← hz, ← hAdef]
    by_cases h : δ ∣ A
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; simp
  rw [hpart1, hpart2]

end KappaOmega2
