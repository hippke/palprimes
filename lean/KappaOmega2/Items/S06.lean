import KappaOmega2.Statements

namespace KappaOmega2

open Finset Palprimes.Greaves

theorem itemS06 : ItemS06 := by
  unfold ItemS06
  intro z₁ c K f Λ M hc hK hΛ1 hΛ hf hM
  have hM0 : M ≠ 0 := by omega
  set S := M.primeFactors.filter (fun p : ℕ => (p : ℝ) < z₁) with hSdef
  have hAdef : radLt M z₁ = ∏ p ∈ S, p := rfl
  have hS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hPF : (radLt M z₁).primeFactors = S := by
    rw [hAdef]
    exact Nat.primeFactors_prod hS
  have hAdvd : radLt M z₁ ∣ M := by
    rw [hAdef]
    exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd M)
  have key : ∀ x, x ∣ M → x ≠ 1 → Λ x ≠ 0 →
      ∃ p, p.Prime ∧ p ∣ x ∧ p ∣ M ∧ (p : ℝ) < z₁ := by
    intro x hxM hx1 hΛx
    have hxz := (hΛ x hΛx).2
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hxM
      exact hM0 (Nat.eq_zero_of_zero_dvd hxM)
    refine ⟨x.minFac, Nat.minFac_prime hx1, Nat.minFac_dvd x, (Nat.minFac_dvd x).trans hxM, ?_⟩
    have hle : x.minFac ≤ x := Nat.minFac_le (Nat.pos_of_ne_zero hx0)
    have hle' : ((x.minFac : ℕ) : ℝ) ≤ x := by exact_mod_cast hle
    linarith
  by_cases hA1 : radLt M z₁ = 1
  · have hsum : ∑ d ∈ M.divisors, Λ d = 1 := by
      rw [Finset.sum_eq_single 1]
      · exact hΛ1
      · intro b hb hb1
        by_contra hne
        obtain ⟨p, hp, _, hpM, hpz⟩ := key b (Nat.dvd_of_mem_divisors hb) hb1 hne
        have hmem : p ∈ S :=
          Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpM, hM0⟩, hpz⟩
        have h1 : p ∣ radLt M z₁ := by
          rw [hAdef]
          exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
        rw [hA1] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      · intro h1
        exact absurd (Nat.one_mem_divisors.mpr hM0) h1
    have hLam : LamA (radLt M z₁) c f = c := by
      unfold LamA
      rw [if_pos hA1]
    rw [hLam, hsum]
    nlinarith
  · by_cases hAp : (radLt M z₁).Prime
    · have hSA : S = {radLt M z₁} := by
        rw [← hPF, hAp.primeFactors]
      have hAmem : radLt M z₁ ∈ S := by
        rw [hSA]
        exact Finset.mem_singleton_self _
      have hAz : ((radLt M z₁ : ℕ) : ℝ) < z₁ := (Finset.mem_filter.mp hAmem).2
      have hAM : radLt M z₁ ∈ M.divisors := Nat.mem_divisors.mpr ⟨hAdvd, hM0⟩
      have hzero : ∀ x ∈ M.divisors, x ∉ ({1, radLt M z₁} : Finset ℕ) → Λ x = 0 := by
        intro x hx hxn
        by_contra hne
        have hxM := Nat.dvd_of_mem_divisors hx
        have hx1 : x ≠ 1 := fun h => hxn (by rw [h]; simp)
        have hxA : x ≠ radLt M z₁ := fun h => hxn (by rw [h]; simp)
        have hsq := (hΛ x hne).1
        have hxz := (hΛ x hne).2
        have hx0 : x ≠ 0 := by
          intro h
          rw [h] at hxM
          exact hM0 (Nat.eq_zero_of_zero_dvd hxM)
        have hq : ∀ q ∈ x.primeFactors, q = radLt M z₁ := by
          intro q hq
          have hqp := Nat.prime_of_mem_primeFactors hq
          have hqx := Nat.dvd_of_mem_primeFactors hq
          have hqle : q ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hqx
          have hqz : (q : ℝ) < z₁ := by
            have : (q : ℝ) ≤ x := by exact_mod_cast hqle
            linarith
          have hqS : q ∈ S :=
            Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqp, hqx.trans hxM, hM0⟩, hqz⟩
          rw [hSA, Finset.mem_singleton] at hqS
          exact hqS
        have hgt : 1 < x := by omega
        obtain ⟨q0, hq0⟩ := Nat.nonempty_primeFactors.mpr hgt
        have hset : x.primeFactors = {radLt M z₁} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨?_, hq⟩
          rw [hq q0 hq0] at hq0
          exact hq0
        apply hxA
        rw [← Nat.prod_primeFactors_of_squarefree hsq, hset, Finset.prod_singleton]
      have hsub : ({1, radLt M z₁} : Finset ℕ) ⊆ M.divisors := by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Nat.one_mem_divisors.mpr hM0
        · exact hAM
      have hsum : ∑ d ∈ M.divisors, Λ d = Λ 1 + Λ (radLt M z₁) := by
        have hs := Finset.sum_subset hsub (f := Λ) (fun x hx hxn => hzero x hx hxn)
        rw [← hs, Finset.sum_pair hAp.one_lt.ne]
      have hLam : LamA (radLt M z₁) c f = f (radLt M z₁) := by
        unfold LamA
        rw [if_neg hA1, if_pos hAp]
      have hfA := hf (radLt M z₁) hAp hAz
      rw [hΛ1] at hfA
      rw [hLam, hsum, hΛ1]
      exact hfA
    · have hLam : LamA (radLt M z₁) c f = 0 := by
        unfold LamA
        rw [if_neg hA1, if_neg hAp]
      rw [hLam]
      have hK0 : 0 ≤ K * c := mul_nonneg (by linarith) hc
      exact mul_nonneg hK0 (sq_nonneg _)

end KappaOmega2
