import Omega3.Statements

/-!
# S04 helpers (some copied from S03 and S13 with new names)
-/

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma S04_prod_sqf (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Squarefree (∏ p ∈ S, p) := by
  have h := Nat.squarefree_prod_primeFactors (∏ p ∈ S, p)
  rwa [Nat.primeFactors_prod hS] at h

lemma S04_mu_eq (t : ℕ) (ht : Squarefree t) : (μ t : ℝ) = (-1) ^ t.primeFactors.card := by
  have h0 : t ≠ 0 := ht.ne_zero
  rw [ArithmeticFunction.moebius_apply_of_squarefree ht,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h0).mpr ht,
    ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  push_cast
  rfl

lemma S04_chi01 (y m : ℝ) (d : ℕ) : chi y m d = 0 ∨ chi y m d = 1 := by
  unfold chi
  split_ifs <;> simp

lemma S04_chi_mono (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) : chi y m δ ≤ chi y m (δ / δ.minFac) := by
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

lemma S04_chibar_01 (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) (hδ1 : δ ≠ 1) :
    chibar y m δ = 0 ∨ chibar y m δ = 1 := by
  unfold chibar
  rw [if_neg hδ1]
  have hm := S04_chi_mono y m δ hδ0
  rcases S04_chi01 y m (δ / δ.minFac) with ha | ha <;> rcases S04_chi01 y m δ with hb | hb <;>
    (rw [ha, hb] at hm ⊢; first | (norm_num at hm; done) | norm_num)

lemma S04_chi (y m : ℝ) (δ : ℕ) (h1 : δ ≠ 1) (h : chibar y m δ = 1) :
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

/-- The violating divisor contains `p(δ)`, so `y ≤ δ p(δ)²` (S13's argument, general `m`). -/
lemma S04_y_le (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) (h1 : δ ≠ 1)
    (hc1 : chiProp y m (δ / δ.minFac)) (hc0 : ¬ chiProp y m δ) :
    y ≤ (δ : ℝ) * (δ.minFac : ℝ) ^ 2 := by
  classical
  unfold chiProp at hc0
  push Not at hc0
  obtain ⟨h, hh, hne, hcond, hge⟩ := hc0
  rw [Nat.mem_divisors] at hh
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

/-- For a prime `p` with `χ̄(p) = 1`: `y ≤ p³` and `1 ≤ 1/m`. -/
lemma S04_chibar_prime (y m : ℝ) (p : ℕ) (hp : p.Prime) (h : chibar y m p = 1) :
    y ≤ (p : ℝ) ^ 3 ∧ (1 : ℝ) ≤ 1 / m := by
  classical
  obtain ⟨_, hc0⟩ := S04_chi y m p hp.ne_one h
  unfold chiProp at hc0
  push Not at hc0
  obtain ⟨h', hh, hne, hcond, hge⟩ := hc0
  rw [Nat.Prime.divisors hp] at hh
  simp at hh
  rcases hh with rfl | rfl
  · exact absurd rfl hne
  · rw [Nat.Prime.minFac_eq hp] at hge
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp] at hcond
    refine ⟨by nlinarith, ?_⟩
    rcases hcond with he | hl
    · exact absurd he (by decide)
    · exact_mod_cast hl

/-! ## The value `Λ` of a set of primes -/

/-- `val(P) = φ` (`P = ∅`), `w(q)` (`P = {q}`), `0` otherwise. -/
noncomputable def S04val (c : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  if P = ∅ then c else if P.card = 1 then ∑ p ∈ P, w p else 0

lemma S04_powerset (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (c - ∑ p ∈ T, w p) = S04val c w S := by
  rcases S.eq_empty_or_nonempty with hS | ⟨a, ha⟩
  · subst hS
    simp [S04val]
  · have hS0 : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩
    set s := S.erase a with hs
    have has : a ∉ s := Finset.notMem_erase a S
    have hSeq : S = insert a s := (Finset.insert_erase ha).symm
    have hval : S04val c w S = if s = ∅ then w a else 0 := by
      unfold S04val
      rw [if_neg hS0]
      by_cases hs0 : s = ∅
      · rw [if_pos hs0, hSeq, hs0]; simp
      · rw [if_neg hs0, if_neg]
        rw [hSeq, Finset.card_insert_of_notMem has]
        have : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs0)
        omega
    rw [hval, hSeq]
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
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
    have hcount : ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card = if s = ∅ then 1 else 0 := by
      have h := congrArg (Int.cast : ℤ → ℝ) (Finset.sum_powerset_neg_one_pow_card (x := s))
      push_cast at h
      rw [h]
    rw [hcount]
    split_ifs <;> ring

lemma S04_LamA_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℝ) (w : ℕ → ℝ) :
    LamA (∏ p ∈ P, p) c w = S04val c w P := by
  classical
  have hpf : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hP
  unfold LamA S04val
  by_cases h0 : P = ∅
  · subst h0; simp
  · rw [if_neg h0]
    have hne1 : (∏ p ∈ P, p) ≠ 1 := by
      intro h; rw [h] at hpf; simp at hpf; exact h0 hpf.symm
    rw [if_neg hne1]
    by_cases h1 : P.card = 1
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.1 h1
      subst hq
      simp only [Finset.prod_singleton, Finset.sum_singleton, if_pos h1]
      rw [if_pos (hP q (Finset.mem_singleton_self q))]
    · rw [if_neg h1, if_neg]
      intro hpr
      apply h1
      rw [← hpf, Nat.Prime.primeFactors hpr]; rfl

lemma S04_val_nonneg (c : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) (hc : 0 ≤ c) (hw : ∀ p, 0 ≤ w p) :
    0 ≤ S04val c w P := by
  unfold S04val
  split_ifs
  · exact hc
  · exact Finset.sum_nonneg (fun p _ => hw p)
  · exact le_rfl

lemma S04_val_mono (c : ℝ) (w : ℕ → ℝ) (P Q : Finset ℕ) (hPQ : P ⊆ Q) (hc : 0 ≤ c) (hw : ∀ p, 0 ≤ w p)
    (hwq : ∀ q ∈ Q, w q ≤ c) : S04val c w Q ≤ S04val c w P := by
  unfold S04val
  by_cases hQ : Q = ∅
  · have : P = ∅ := Finset.subset_empty.mp (hQ ▸ hPQ)
    rw [if_pos hQ, if_pos this]
  · rw [if_neg hQ]
    by_cases hQ1 : Q.card = 1
    · rw [if_pos hQ1]
      obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hQ1
      subst hq
      rcases Finset.subset_singleton_iff.mp hPQ with hP | hP
      · rw [if_pos hP, Finset.sum_singleton]; exact hwq q (Finset.mem_singleton_self q)
      · subst hP; simp
    · rw [if_neg hQ1]
      have := S04_val_nonneg c w P hc hw
      unfold S04val at this
      exact this

/-! ## `radLt` -/

lemma S04_rad_pf (a : ℕ) (z : ℝ) :
    (radLt a z).primeFactors = a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) := by
  classical
  unfold radLt
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma S04_rad_eq (a : ℕ) (z : ℝ) :
    radLt a z = ∏ p ∈ a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p := by
  classical
  unfold radLt; rfl

lemma S04_rad_sqf (a : ℕ) (z : ℝ) : Squarefree (radLt a z) := by
  classical
  unfold radLt
  apply S04_prod_sqf
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma S04_rad_self (A : ℕ) (z : ℝ) (hA : Squarefree A) (hz : ∀ p ∈ A.primeFactors, (p : ℝ) < z) :
    radLt A z = A := by
  classical
  rw [S04_rad_eq, Finset.filter_true_of_mem hz, Nat.prod_primeFactors_of_squarefree hA]

lemma S04_LamA_rad (a : ℕ) (z c : ℝ) (w : ℕ → ℝ) :
    LamA (radLt a z) c w = S04val c w (a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)) := by
  classical
  rw [S04_rad_eq]
  apply S04_LamA_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- The inner sum is `val` of the primes of `A` below `p(δ)`. -/
lemma S04_inner (W1' : ℝ) (w : ℕ → ℝ) (A δ : ℕ) (hδ0 : δ ≠ 0) :
    innerS W1' w A δ = S04val (phiW W1' w δ) w (radLt A (δ.minFac : ℝ)).primeFactors := by
  unfold innerS
  set B := radLt A (δ.minFac : ℝ) with hBdef
  have hBpf := S04_rad_pf A (δ.minFac : ℝ)
  rw [← hBdef] at hBpf
  have hBsq : Squarefree B := S04_rad_sqf A _
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
      (-1 : ℝ) ^ t.primeFactors.card * (phiW W1' w δ - ∑ p ∈ t.primeFactors, w p) := by
    intro t ht
    have htsq : Squarefree t := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht) hBsq
    have ht0 : t ≠ 0 := htsq.ne_zero
    rw [S04_mu_eq t htsq]
    congr 1
    unfold phiW
    rw [Nat.primeFactors_mul ht0 hδ0, Finset.sum_union (hdisj t ht)]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ t ∈ B.divisors, (-1 : ℝ) ^ t.primeFactors.card *
        (phiW W1' w δ - ∑ p ∈ t.primeFactors, w p) =
      ∑ T ∈ B.primeFactors.powerset, (-1 : ℝ) ^ T.card * (phiW W1' w δ - ∑ p ∈ T, w p) := by
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
  rw [hbij, S04_powerset]

lemma S04_dvd_primorial (A : ℕ) (z : ℝ) (hA : Squarefree A) (hz : ∀ p ∈ A.primeFactors, (p : ℝ) < z) :
    A ∣ primorialLt z := by
  rw [← Nat.prod_primeFactors_of_squarefree hA]
  unfold primorialLt
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [mem_primesBelow]
  exact ⟨Nat.prime_of_mem_primeFactors hp, hz p hp⟩

end Omega3
