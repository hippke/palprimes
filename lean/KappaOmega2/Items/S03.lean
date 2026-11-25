import KappaOmega2.Statements

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

lemma S03_prod_sqf (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Squarefree (∏ p ∈ S, p) := by
  have h := Nat.squarefree_prod_primeFactors (∏ p ∈ S, p)
  rwa [Nat.primeFactors_prod hS] at h

lemma S03_mu_eq (t : ℕ) (ht : Squarefree t) : (μ t : ℝ) = (-1) ^ t.primeFactors.card := by
  have h0 : t ≠ 0 := ht.ne_zero
  rw [ArithmeticFunction.moebius_apply_of_squarefree ht,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h0).mpr ht,
    ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  push_cast
  rfl

lemma S03_chi01 (y m : ℝ) (d : ℕ) : chi y m d = 0 ∨ chi y m d = 1 := by
  unfold chi
  split_ifs <;> simp

lemma S03_chi_mono (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) : chi y m δ ≤ chi y m (δ / δ.minFac) := by
  unfold chi
  split_ifs with h1 h2
  · norm_num
  · exfalso
    apply h2
    unfold chiProp at *
    intro h hh h1' hc
    exact h1 h (Nat.divisors_subset_of_dvd hδ0 (Nat.div_dvd_of_dvd (Nat.minFac_dvd δ)) hh) h1' hc
  · norm_num
  · norm_num

lemma S03_chibar_01 (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) (hδ1 : δ ≠ 1) :
    chibar y m δ = 0 ∨ chibar y m δ = 1 := by
  unfold chibar
  rw [if_neg hδ1]
  have hm := S03_chi_mono y m δ hδ0
  rcases S03_chi01 y m (δ / δ.minFac) with ha | ha <;> rcases S03_chi01 y m δ with hb | hb <;>
    (rw [ha, hb] at hm ⊢; first | (norm_num at hm; done) | norm_num)

lemma S03_powerset_nonneg (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (hc : 0 ≤ c) (hw : ∀ p, 0 ≤ w p) :
    0 ≤ ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (c - ∑ p ∈ T, w p) := by
  rcases S.eq_empty_or_nonempty with hS | ⟨a, ha⟩
  · subst hS
    simpa using hc
  · rw [← Finset.insert_erase ha]
    set s := S.erase a with hs
    have has : a ∉ s := Finset.notMem_erase a S
    have hsplit := Finset.sum_powerset_insert has
      (f := fun T : Finset ℕ => (-1 : ℝ) ^ T.card * (c - ∑ p ∈ T, w p))
    rw [hsplit]
    have hterm : ∀ T ∈ s.powerset,
        (-1 : ℝ) ^ (insert a T).card * (c - ∑ p ∈ insert a T, w p) =
          -((-1 : ℝ) ^ T.card * (c - ∑ p ∈ T, w p)) + (-1 : ℝ) ^ T.card * w a := by
      intro T hT
      have haT : a ∉ T := fun h => has (Finset.mem_powerset.mp hT h)
      rw [Finset.card_insert_of_notMem haT, Finset.sum_insert haT, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul]
    have hcount : ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card = if s = ∅ then 1 else 0 := by
      have h := congrArg (Int.cast : ℤ → ℝ) (Finset.sum_powerset_neg_one_pow_card (x := s))
      push_cast at h
      rw [h]
    rw [hcount]
    have hwa := hw a
    split_ifs <;> linarith

lemma S03_inner (W1' : ℝ) (w : ℕ → ℝ) (A δ : ℕ) (hw : ∀ p, 0 ≤ w p) (hδ0 : δ ≠ 0)
    (hφ : 0 ≤ W1' - ∑ p ∈ δ.primeFactors, w p) : 0 ≤ innerS W1' w A δ := by
  unfold innerS
  set B := radLt A (δ.minFac : ℝ) with hBdef
  have hBpf : B.primeFactors = A.primeFactors.filter (fun p : ℕ => (p : ℝ) < (δ.minFac : ℝ)) := by
    rw [hBdef]
    unfold radLt
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hBsq : Squarefree B := by
    rw [hBdef]
    unfold radLt
    apply S03_prod_sqf
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hB0 : B ≠ 0 := hBsq.ne_zero
  have hprimesB : ∀ p ∈ B.primeFactors, p < δ.minFac := by
    intro p hp
    rw [hBpf] at hp
    have h := (Finset.mem_filter.mp hp).2
    exact_mod_cast h
  have hdisj : ∀ t ∈ B.divisors, Disjoint t.primeFactors δ.primeFactors := by
    intro t ht
    rw [Finset.disjoint_left]
    intro p hp hq
    have hpB : p ∈ B.primeFactors :=
      Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hB0 hp
    have h1 := hprimesB p hpB
    have h2 : δ.minFac ≤ p :=
      Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
        (Nat.dvd_of_mem_primeFactors hq)
    omega
  have hterm : ∀ t ∈ B.divisors, (μ t : ℝ) * phiW W1' w (t * δ) =
      (-1 : ℝ) ^ t.primeFactors.card * ((W1' - ∑ p ∈ δ.primeFactors, w p) - ∑ p ∈ t.primeFactors, w p) := by
    intro t ht
    have htsq : Squarefree t := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht) hBsq
    have ht0 : t ≠ 0 := htsq.ne_zero
    rw [S03_mu_eq t htsq]
    congr 1
    unfold phiW
    rw [Nat.primeFactors_mul ht0 hδ0, Finset.sum_union (hdisj t ht)]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ t ∈ B.divisors, (-1 : ℝ) ^ t.primeFactors.card *
        ((W1' - ∑ p ∈ δ.primeFactors, w p) - ∑ p ∈ t.primeFactors, w p) =
      ∑ T ∈ B.primeFactors.powerset, (-1 : ℝ) ^ T.card *
        ((W1' - ∑ p ∈ δ.primeFactors, w p) - ∑ p ∈ T, w p) := by
    apply Finset.sum_nbij' (fun t : ℕ => t.primeFactors) (fun T : Finset ℕ => ∏ p ∈ T, p)
    · intro t ht
      exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hB0)
    · intro T hT
      have hTB : (∏ p ∈ T, p) ∣ ∏ p ∈ B.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hT)
      rw [Nat.prod_primeFactors_of_squarefree hBsq] at hTB
      exact Nat.mem_divisors.mpr ⟨hTB, hB0⟩
    · intro t ht
      have htsq : Squarefree t := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht) hBsq
      exact Nat.prod_primeFactors_of_squarefree htsq
    · intro T hT
      apply Nat.primeFactors_prod
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hT hp)
    · intro t _
      rfl
  rw [hbij]
  exact S03_powerset_nonneg B.primeFactors _ w hφ hw

lemma S03_rad_dvd_primorial (A : ℕ) (z : ℝ) : radLt A z ∣ primorialLt z := by
  unfold radLt primorialLt
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hpz : (p : ℝ) < z := (Finset.mem_filter.mp hp).2
  unfold primesBelow
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hpp, hpz⟩
  have := (Nat.lt_ceil).mpr hpz
  omega

theorem itemS03 : ItemS03 := by
  unfold ItemS03
  intro y z m W1' w A hm hy hsqA hAz hw hH
  unfold Sig4
  apply Finset.sum_nonneg
  intro δ hδ
  rw [Finset.mem_filter, Nat.mem_divisors] at hδ
  obtain ⟨⟨hdiv, _⟩, hev, h2⟩ := hδ
  have hRsq : Squarefree (radLt A z) := by
    unfold radLt
    apply S03_prod_sqf
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hδsq : Squarefree δ := Squarefree.squarefree_of_dvd hdiv hRsq
  have hδ0 : δ ≠ 0 := hδsq.ne_zero
  have hδ1 : δ ≠ 1 := by
    intro h
    have h0 : ω δ = 0 := by
      rw [h]
      simp
    omega
  have hP0 : primorialLt z ≠ 0 := by
    unfold primorialLt
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    unfold primesBelow at hp
    exact (Finset.mem_filter.mp hp).2.1.ne_zero
  have hδprim : δ ∈ (primorialLt z).divisors :=
    Nat.mem_divisors.mpr ⟨hdiv.trans (S03_rad_dvd_primorial A z), hP0⟩
  have hμ1 : (μ δ : ℝ) = 1 := by
    rw [S03_mu_eq δ hδsq]
    have hcard : Even δ.primeFactors.card := by
      rw [← ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
      exact hev
    rw [hcard.neg_one_pow]
  rcases S03_chibar_01 y m δ hδ0 hδ1 with hc | hc
  · simp [hc]
  · have hle := hH δ hδprim hev h2 hc
    rw [hc, hμ1]
    simp only [one_mul]
    exact S03_inner W1' w A δ hw hδ0 (by linarith)

end KappaOmega2
