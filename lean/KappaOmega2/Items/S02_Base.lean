import KappaOmega2.Statements

/-!
# S02 helpers: copies (from S03, S04 with new names), Jurkat–Richert telescoping of `χ_y`, `χ̄ = 0` above `1/m`
-/

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma S02_prod_sqf (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : Squarefree (∏ p ∈ S, p) := by
  have h := Nat.squarefree_prod_primeFactors (∏ p ∈ S, p)
  rwa [Nat.primeFactors_prod hS] at h

lemma S02_mu_eq (t : ℕ) (ht : Squarefree t) : (μ t : ℝ) = (-1) ^ t.primeFactors.card := by
  have h0 : t ≠ 0 := ht.ne_zero
  rw [ArithmeticFunction.moebius_apply_of_squarefree ht,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h0).mpr ht,
    ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  push_cast
  rfl

lemma S02_chi01 (y m : ℝ) (d : ℕ) : chi y m d = 0 ∨ chi y m d = 1 := by
  unfold chi
  split_ifs <;> simp

lemma S02_chi_mono (y m : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) : chi y m δ ≤ chi y m (δ / δ.minFac) := by
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

lemma S02_chi_one (y m : ℝ) : chi y m 1 = 1 := by
  classical
  unfold chi; rw [if_pos]
  intro h hh hne
  simp at hh; exact absurd hh hne

/-- `χ̄(p) = [y ≤ p³]` for primes when `m ≤ 1`. -/
lemma S02_chibar_prime (y m : ℝ) (hm0 : 0 < m) (hm : m ≤ 1) (p : ℕ) (hp : p.Prime) :
    chibar y m p = if y ≤ (p : ℝ) ^ 3 then 1 else 0 := by
  classical
  unfold chibar
  rw [if_neg hp.ne_one, Nat.Prime.minFac_eq hp, Nat.div_self hp.pos, S02_chi_one]
  have hiff : chiProp y m p ↔ (p : ℝ) ^ 3 < y := by
    unfold chiProp
    rw [Nat.Prime.divisors hp]
    constructor
    · intro h
      have := h p (by simp) hp.ne_one (Or.inr (by
        rw [ArithmeticFunction.cardDistinctFactors_apply_prime hp]
        push_cast; rw [le_div_iff₀ hm0]; linarith))
      rw [Nat.Prime.minFac_eq hp] at this
      nlinarith
    · intro h h' hh hne _
      simp at hh
      rcases hh with rfl | rfl
      · exact absurd rfl hne
      · rw [Nat.Prime.minFac_eq hp]; nlinarith
  unfold chi
  by_cases hy : y ≤ (p : ℝ) ^ 3
  · rw [if_pos hy, if_neg (fun h => absurd (hiff.1 h) (not_lt.2 hy))]; ring
  · rw [if_neg hy, if_pos (hiff.2 (not_le.1 hy))]; ring

/-! ## `val` of a set of primes, `radLt` -/

/-- `val(P) = φ` (`P = ∅`), `w(q)` (`P = {q}`), `0` otherwise. -/
noncomputable def S02val (c : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) : ℝ :=
  if P = ∅ then c else if P.card = 1 then ∑ p ∈ P, w p else 0

lemma S02_powerset (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (c - ∑ p ∈ T, w p) = S02val c w S := by
  rcases S.eq_empty_or_nonempty with hS | ⟨a, ha⟩
  · subst hS
    simp [S02val]
  · have hS0 : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩
    set s := S.erase a with hs
    have has : a ∉ s := Finset.notMem_erase a S
    have hSeq : S = insert a s := (Finset.insert_erase ha).symm
    have hval : S02val c w S = if s = ∅ then w a else 0 := by
      unfold S02val
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

lemma S02_LamA_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℝ) (w : ℕ → ℝ) :
    LamA (∏ p ∈ P, p) c w = S02val c w P := by
  classical
  have hpf : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hP
  unfold LamA S02val
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

lemma S02_rad_pf (a : ℕ) (z : ℝ) :
    (radLt a z).primeFactors = a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) := by
  classical
  unfold radLt
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma S02_rad_eq (a : ℕ) (z : ℝ) :
    radLt a z = ∏ p ∈ a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p := by
  classical
  unfold radLt; rfl

lemma S02_rad_sqf (a : ℕ) (z : ℝ) : Squarefree (radLt a z) := by
  classical
  unfold radLt
  apply S02_prod_sqf
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma S02_rad_self (A : ℕ) (z : ℝ) (hA : Squarefree A) (hz : ∀ p ∈ A.primeFactors, (p : ℝ) < z) :
    radLt A z = A := by
  classical
  rw [S02_rad_eq, Finset.filter_true_of_mem hz, Nat.prod_primeFactors_of_squarefree hA]

/-- The inner sum is `val` of the primes of `A` below `p(δ)`. -/
lemma S02_inner (W1' : ℝ) (w : ℕ → ℝ) (A δ : ℕ) (hδ0 : δ ≠ 0) :
    innerS W1' w A δ = S02val (phiW W1' w δ) w (radLt A (δ.minFac : ℝ)).primeFactors := by
  unfold innerS
  set B := radLt A (δ.minFac : ℝ) with hBdef
  have hBpf := S02_rad_pf A (δ.minFac : ℝ)
  rw [← hBdef] at hBpf
  have hBsq : Squarefree B := S02_rad_sqf A _
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
    rw [S02_mu_eq t htsq]
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
  rw [hbij, S02_powerset]

/-- `Σ_{d ∣ A} μ(d)φ(d) = Λ{A, W(1), w}` for squarefree `A`. -/
lemma S02_sum_muphi (W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) (hA : Squarefree A) :
    ∑ d ∈ A.divisors, (μ d : ℝ) * phiW W1' w d = LamA A W1' w := by
  have hA0 : A ≠ 0 := hA.ne_zero
  have hterm : ∀ t ∈ A.divisors, (μ t : ℝ) * phiW W1' w t =
      (-1 : ℝ) ^ t.primeFactors.card * (W1' - ∑ p ∈ t.primeFactors, w p) := by
    intro t ht
    have htsq : Squarefree t := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht) hA
    rw [S02_mu_eq t htsq]; rfl
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ t ∈ A.divisors, (-1 : ℝ) ^ t.primeFactors.card * (W1' - ∑ p ∈ t.primeFactors, w p) =
      ∑ T ∈ A.primeFactors.powerset, (-1 : ℝ) ^ T.card * (W1' - ∑ p ∈ T, w p) := by
    apply Finset.sum_nbij' (fun t : ℕ => t.primeFactors) (fun T : Finset ℕ => ∏ p ∈ T, p)
    · intro t ht
      exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hA0)
    · intro T hT
      have hTB : (∏ p ∈ T, p) ∣ ∏ p ∈ A.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hT)
      rw [Nat.prod_primeFactors_of_squarefree hA] at hTB
      exact Nat.mem_divisors.mpr ⟨hTB, hA0⟩
    · intro t ht
      have htsq : Squarefree t := Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht) hA
      exact Nat.prod_primeFactors_of_squarefree htsq
    · intro T hT
      apply Nat.primeFactors_prod
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hT hp)
    · intro t _
      rfl
  rw [hbij, S02_powerset, ← S02_LamA_prod A.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp),
    Nat.prod_primeFactors_of_squarefree hA]

/-! ## Telescoping of `χ_y` along the heads `δ` of `d` (`d/δ` has only primes `< p(δ)`) -/

/-- Heads of `d`: divisors `δ ≠ 1` with every prime of `d/δ` below `p(δ)`. -/
noncomputable def S02heads (d : ℕ) : Finset ℕ :=
  open Classical in d.divisors.filter (fun δ : ℕ => δ ≠ 1 ∧ ∀ q ∈ (d / δ).primeFactors, q < δ.minFac)

lemma S02_mem_heads (d δ : ℕ) :
    δ ∈ S02heads d ↔ (δ ∣ d ∧ d ≠ 0) ∧ δ ≠ 1 ∧ ∀ q ∈ (d / δ).primeFactors, q < δ.minFac := by
  classical
  unfold S02heads
  rw [Finset.mem_filter, Nat.mem_divisors]

/-- Primes of a squarefree `d` other than `p(d)` are `> p(d)`; divisors `≠ 1` of `d/p(d)` have `p(δ) > p(d)`. -/
lemma S02_minFac_lt (d δ : ℕ) (hsq : Squarefree d) (h1 : d ≠ 1) (hδ : δ ∣ d / d.minFac) (hδ1 : δ ≠ 1) :
    d.minFac < δ.minFac := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hp : d.minFac.Prime := Nat.minFac_prime h1
  have hd' : d / d.minFac ∣ d := Nat.div_dvd_of_dvd (Nat.minFac_dvd d)
  have hq : δ.minFac.Prime := Nat.minFac_prime hδ1
  have hqd' : δ.minFac ∣ d / d.minFac := (Nat.minFac_dvd δ).trans hδ
  have hle : d.minFac ≤ δ.minFac := Nat.minFac_le_of_dvd hq.two_le (hqd'.trans hd')
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    rw [← h] at hqd'
    have : d.minFac * d.minFac ∣ d := by
      have := Nat.mul_dvd_mul_left d.minFac hqd'
      rwa [Nat.mul_div_cancel' (Nat.minFac_dvd d)] at this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq _ this))

lemma S02_heads_step (d : ℕ) (hsq : Squarefree d) (h1 : d ≠ 1) :
    S02heads d = insert d (S02heads (d / d.minFac)) ∧ d ∉ S02heads (d / d.minFac) := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  set p := d.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpd : p ∣ d := Nat.minFac_dvd d
  set d' := d / p with hd'def
  have hdd' : d = p * d' := (Nat.mul_div_cancel' hpd).symm
  have hd'0 : d' ≠ 0 := by intro h; rw [h, mul_zero] at hdd'; exact hd0 hdd'
  have hd'lt : d' < d := by
    rw [hdd']; have := hp.one_lt; have := Nat.pos_of_ne_zero hd'0; nlinarith
  have hnot : d ∉ S02heads d' := by
    intro h
    have := ((S02_mem_heads d' d).1 h).1.1
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hd'0) this) (not_le.2 hd'lt)
  refine ⟨?_, hnot⟩
  ext δ
  rw [Finset.mem_insert, S02_mem_heads, S02_mem_heads]
  constructor
  · rintro ⟨⟨hδd, -⟩, hδ1, hcond⟩
    by_cases hδeq : δ = d
    · left; exact hδeq
    · right
      have hδ0 : δ ≠ 0 := by rintro rfl; exact hd0 (Nat.eq_zero_of_zero_dvd hδd)
      have hnp : ¬ p ∣ δ := by
        intro hpδ
        have hmf : δ.minFac = p := by
          apply le_antisymm
          · exact Nat.minFac_le_of_dvd hp.two_le hpδ
          · exact Nat.minFac_le_of_dvd (Nat.minFac_prime hδ1).two_le ((Nat.minFac_dvd δ).trans hδd)
        have hq0 : d / δ ≠ 0 := by
          intro h0
          have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hδd) (Nat.pos_of_ne_zero hδ0)
          omega
        have hempty : (d / δ).primeFactors = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro q hq
          have h1q := hcond q hq
          rw [hmf] at h1q
          have hqd : q ∣ d := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hδd)
          have := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le hqd
          omega
        rw [Nat.primeFactors_eq_empty] at hempty
        rcases hempty with h | h
        · exact hq0 h
        · apply hδeq
          have := Nat.div_mul_cancel hδd
          rw [h, one_mul] at this
          exact this
      have hcop : Nat.Coprime δ p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnp).symm
      have hδd' : δ ∣ d' := hcop.dvd_of_dvd_mul_left (hdd' ▸ hδd)
      refine ⟨⟨hδd', hd'0⟩, hδ1, ?_⟩
      intro q hq
      apply hcond q
      have hsub : d' / δ ∣ d / δ := by
        rw [hdd', Nat.mul_div_assoc p hδd']; exact Dvd.intro_left p rfl
      have hq0 : d / δ ≠ 0 := by
        intro h0
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hδd) (Nat.pos_of_ne_zero hδ0)
        omega
      exact Nat.primeFactors_mono hsub hq0 hq
  · rintro (rfl | ⟨⟨hδd', -⟩, hδ1, hcond⟩)
    · refine ⟨⟨dvd_rfl, hd0⟩, h1, ?_⟩
      rw [Nat.div_self (Nat.pos_of_ne_zero hd0)]; simp
    · refine ⟨⟨hδd'.trans (Nat.div_dvd_of_dvd hpd), hd0⟩, hδ1, ?_⟩
      have hlt := S02_minFac_lt d δ hsq h1 hδd' hδ1
      intro q hq
      have hdiv : d / δ = p * (d' / δ) := by rw [hdd', Nat.mul_div_assoc p hδd']
      rw [hdiv] at hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqdvd := Nat.dvd_of_mem_primeFactors hq
      rcases (Nat.Prime.dvd_mul hqp).1 hqdvd with hqp' | hqd
      · rw [(Nat.prime_dvd_prime_iff_eq hqp hp).1 hqp']; exact hlt
      · have hd'δ0 : d' / δ ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hdiv
          have hδ0 : δ ≠ 0 := by rintro rfl; exact hd'0 (Nat.eq_zero_of_zero_dvd hδd')
          have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (hδd'.trans (Nat.div_dvd_of_dvd hpd)))
            (Nat.pos_of_ne_zero hδ0)
          omega
        exact hcond q (Nat.mem_primeFactors.2 ⟨hqp, hqd, hd'δ0⟩)

lemma S02_chi_tel (y m : ℝ) : ∀ d : ℕ, Squarefree d →
    chi y m d = 1 - ∑ δ ∈ S02heads d, chibar y m δ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hsq
    by_cases h1 : d = 1
    · subst h1
      have : S02heads 1 = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro δ hδ
        obtain ⟨⟨hδ1', -⟩, hδ1, -⟩ := (S02_mem_heads 1 δ).1 hδ
        exact hδ1 (Nat.dvd_one.1 hδ1')
      rw [this, Finset.sum_empty, S02_chi_one]; ring
    · obtain ⟨heq, hnot⟩ := S02_heads_step d hsq h1
      have hd0 : d ≠ 0 := hsq.ne_zero
      have hp : d.minFac.Prime := Nat.minFac_prime h1
      have hlt : d / d.minFac < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.one_lt
      have hsq' : Squarefree (d / d.minFac) := hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.minFac_dvd d))
      rw [heq, Finset.sum_insert hnot]
      have := ih (d / d.minFac) hlt hsq'
      unfold chibar at this ⊢
      rw [if_neg h1]
      linarith

/-- Exchange of the double sum over `d ∣ A` and its heads `δ`, with `d = tδ`, `t ∣ (A, P(p(δ)))`. -/
lemma S02_swap (A : ℕ) (hA : Squarefree A) (f g : ℕ → ℝ) :
    ∑ d ∈ A.divisors, f d * ∑ δ ∈ S02heads d, g δ =
      ∑ δ ∈ A.divisors.filter (· ≠ 1), g δ * ∑ t ∈ (radLt A (δ.minFac : ℝ)).divisors, f (t * δ) := by
  classical
  have hA0 : A ≠ 0 := hA.ne_zero
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := A.divisors.filter (· ≠ 1))
    (s' := fun δ => A.divisors.filter (fun d => δ ∈ S02heads d))]
  · apply Finset.sum_congr rfl
    intro δ hδ
    rw [Finset.mem_filter, Nat.mem_divisors] at hδ
    obtain ⟨⟨hδA, -⟩, hδ1⟩ := hδ
    have hδ0 : δ ≠ 0 := by rintro rfl; exact hA0 (Nat.eq_zero_of_zero_dvd hδA)
    set C := radLt A (δ.minFac : ℝ) with hC
    have hCsq : Squarefree C := S02_rad_sqf A _
    have hC0 : C ≠ 0 := hCsq.ne_zero
    have hCpf : C.primeFactors = A.primeFactors.filter (fun p : ℕ => (p : ℝ) < (δ.minFac : ℝ)) :=
      S02_rad_pf A _
    have hCA : C ∣ A := by
      rw [hC, S02_rad_eq]
      calc (∏ p ∈ A.primeFactors.filter (fun p : ℕ => (p : ℝ) < (δ.minFac : ℝ)), p) ∣ ∏ p ∈ A.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
        _ = A := Nat.prod_primeFactors_of_squarefree hA
    have hcop : ∀ t ∈ C.divisors, Nat.Coprime t δ := by
      intro t ht
      have ht0 : t ≠ 0 := by rintro rfl; exact hC0 (Nat.eq_zero_of_zero_dvd (Nat.dvd_of_mem_divisors ht))
      rw [← Nat.disjoint_primeFactors ht0 hδ0, Finset.disjoint_left]
      intro q hqt hqδ
      have hqC := Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hC0 hqt
      rw [hCpf, Finset.mem_filter] at hqC
      have h1 : q < δ.minFac := by exact_mod_cast hqC.2
      have h2 := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hqδ).two_le (Nat.dvd_of_mem_primeFactors hqδ)
      omega
    rw [← Finset.sum_mul, ← Finset.mul_sum, mul_comm]
    congr 1
    apply Finset.sum_nbij' (fun d => d / δ) (fun t => t * δ)
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdA, -⟩, hh⟩ := hd
      obtain ⟨⟨hδd, hd0⟩, -, hcond⟩ := (S02_mem_heads d δ).1 hh
      rw [Nat.mem_divisors]
      refine ⟨?_, hC0⟩
      have hsqq : Squarefree (d / δ) := (hA.squarefree_of_dvd hdA).squarefree_of_dvd (Nat.div_dvd_of_dvd hδd)
      rw [← Nat.prod_primeFactors_of_squarefree hsqq, hC, S02_rad_eq]
      apply Finset.prod_dvd_prod_of_subset
      intro q hq
      rw [Finset.mem_filter]
      refine ⟨Nat.primeFactors_mono ((Nat.div_dvd_of_dvd hδd).trans hdA) hA0 hq, ?_⟩
      exact_mod_cast hcond q hq
    · intro t ht
      rw [Finset.mem_filter, Nat.mem_divisors]
      have htC := Nat.dvd_of_mem_divisors ht
      have htδA : t * δ ∣ A := (hcop t ht).mul_dvd_of_dvd_of_dvd (htC.trans hCA) hδA
      refine ⟨⟨htδA, hA0⟩, ?_⟩
      rw [S02_mem_heads]
      have ht0 : t ≠ 0 := by rintro rfl; exact hC0 (Nat.eq_zero_of_zero_dvd htC)
      refine ⟨⟨Dvd.intro_left t rfl, mul_ne_zero ht0 hδ0⟩, hδ1, ?_⟩
      rw [Nat.mul_div_cancel t (Nat.pos_of_ne_zero hδ0)]
      intro q hq
      have hqC := Nat.primeFactors_mono htC hC0 hq
      rw [hCpf, Finset.mem_filter] at hqC
      exact_mod_cast hqC.2
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨⟨hδd, -⟩, -, -⟩ := (S02_mem_heads d δ).1 hd.2
      exact Nat.div_mul_cancel hδd
    · intro t _
      exact Nat.mul_div_cancel t (Nat.pos_of_ne_zero hδ0)
    · intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨⟨hδd, -⟩, -, -⟩ := (S02_mem_heads d δ).1 hd.2
      rw [Nat.div_mul_cancel hδd]
  · intro d δ
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hd, hh⟩
      obtain ⟨⟨hδd, -⟩, hδ1, -⟩ := (S02_mem_heads d δ).1 hh
      refine ⟨⟨hd, hh⟩, ?_, hδ1⟩
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hδd.trans hd.1, hA0⟩
    · rintro ⟨⟨hd, hh⟩, -, -⟩
      exact ⟨hd, hh⟩

/-! ## `χ̄ = 0` for odd `ν(δ) > 1/m` -/

lemma S02_chibar_zero (y m : ℝ) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1) (hodd : ¬ Even (ω δ))
    (hbig : ¬ ((ω δ : ℝ) ≤ 1 / m)) : chibar y m δ = 0 := by
  classical
  have hδ0 : δ ≠ 0 := hsq.ne_zero
  set p := δ.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpδ : p ∣ δ := Nat.minFac_dvd δ
  have key : chiProp y m (δ / p) → chiProp y m δ := by
    intro hc h hh hne hcond
    rw [Nat.mem_divisors] at hh
    have hh0 : h ≠ 0 := by rintro rfl; exact hδ0 (Nat.eq_zero_of_zero_dvd hh.1)
    have hhsq : Squarefree h := hsq.squarefree_of_dvd hh.1
    by_cases hph : p ∣ h
    · have hhδ : h ≠ δ := by
        rintro rfl
        rcases hcond with he | hl
        · exact hodd he
        · exact hbig hl
      -- a prime of δ not in h
      obtain ⟨q, hqδ, hqh⟩ : ∃ q ∈ δ.primeFactors, q ∉ h.primeFactors := by
        by_contra hcon
        push Not at hcon
        apply hhδ
        apply Nat.dvd_antisymm hh.1
        rw [← Nat.prod_primeFactors_of_squarefree hsq, ← Nat.prod_primeFactors_of_squarefree hhsq]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hcon
      have hqp := Nat.prime_of_mem_primeFactors hqδ
      have hqdvd := Nat.dvd_of_mem_primeFactors hqδ
      have hqne : q ≠ p := by
        rintro rfl; exact hqh (Nat.mem_primeFactors.2 ⟨hp, hph, hh0⟩)
      have hpq : p < q := lt_of_le_of_ne (Nat.minFac_le_of_dvd hqp.two_le hqdvd) (Ne.symm hqne)
      have hqnh : ¬ q ∣ h := fun hd => hqh (Nat.mem_primeFactors.2 ⟨hqp, hd, hh0⟩)
      set h1' := h / p with hh1'
      have hheq : h = p * h1' := (Nat.mul_div_cancel' hph).symm
      have hh1'0 : h1' ≠ 0 := by intro hz; rw [hz, mul_zero] at hheq; exact hh0 hheq
      have hh1'dvd : h1' ∣ δ / p := by rw [hh1']; exact Nat.div_dvd_div hph hh.1
      have hqδp : q ∣ δ / p := by
        apply Nat.dvd_div_of_mul_dvd
        exact ((Nat.coprime_primes hp hqp).2 (Ne.symm hqne)).mul_dvd_of_dvd_of_dvd hpδ hqdvd
      have hcop1 : Nat.Coprime h1' q := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hqp]
        intro hd; exact hqnh (hd.trans (Nat.div_dvd_of_dvd hph))
      set h' := h1' * q with hh'
      have hh'dvd : h' ∣ δ / p := hcop1.mul_dvd_of_dvd_of_dvd hh1'dvd hqδp
      have hh'1 : h' ≠ 1 := by
        intro he; have := Nat.eq_one_of_mul_eq_one_left he; exact hqp.ne_one this
      have hδp0 : δ / p ≠ 0 := by
        intro hz
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) hpδ) hp.pos
        omega
      -- ω h' = ω h
      have hpnh1 : ¬ p ∣ h1' := by
        intro hd
        have : p * p ∣ h := by rw [hheq]; exact Nat.mul_dvd_mul_left p hd
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hhsq _ this))
      have hcopp : Nat.Coprime h1' p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpnh1))
      have hω : ω h' = ω h := by
        have hd1 : Disjoint h1'.primeFactors q.primeFactors :=
          (Nat.disjoint_primeFactors hh1'0 hqp.ne_zero).2 hcop1
        have hd2 : Disjoint p.primeFactors h1'.primeFactors :=
          (Nat.disjoint_primeFactors hp.ne_zero hh1'0).2 hcopp.symm
        rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
          ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, hh', hheq,
          Nat.primeFactors_mul hh1'0 hqp.ne_zero, Nat.primeFactors_mul hp.ne_zero hh1'0,
          Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
          Nat.Prime.primeFactors hqp, Nat.Prime.primeFactors hp]
        simp only [Finset.card_singleton]
        omega
      have hc' := hc h' (Nat.mem_divisors.2 ⟨hh'dvd, hδp0⟩) hh'1 (by rw [hω]; exact hcond)
      have hmfh : h.minFac = p := by
        apply le_antisymm
        · exact Nat.minFac_le_of_dvd hp.two_le hph
        · have hne1 : h ≠ 1 := hne
          exact Nat.minFac_le_of_dvd (Nat.minFac_prime hne1).two_le ((Nat.minFac_dvd h).trans hh.1)
      have hmfh' : p ≤ h'.minFac := by
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime hh'1).two_le
          ((Nat.minFac_dvd h').trans (hh'dvd.trans (Nat.div_dvd_of_dvd hpδ)))
      rw [hmfh]
      have hlt : h ≤ h' := by
        rw [hheq, hh', mul_comm h1' q]
        exact Nat.mul_le_mul_right h1' hpq.le
      have hlt' : (h : ℝ) ≤ h' := by exact_mod_cast hlt
      have hmf' : (p : ℝ) ≤ h'.minFac := by exact_mod_cast hmfh'
      have hp0 : (0 : ℝ) ≤ p := by positivity
      calc (h : ℝ) * (p : ℝ) ^ 2 ≤ (h' : ℝ) * (h'.minFac : ℝ) ^ 2 := by gcongr
        _ < y := hc'
    · have hcop : Nat.Coprime h p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hph).symm
      have hhd : h ∣ δ / p := by
        apply Nat.dvd_div_of_mul_dvd
        rw [mul_comm]
        exact hcop.mul_dvd_of_dvd_of_dvd hh.1 hpδ
      have hδp0 : δ / p ≠ 0 := by
        intro hz
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) hpδ) hp.pos
        omega
      exact hc h (Nat.mem_divisors.2 ⟨hhd, hδp0⟩) hne hcond
  unfold chibar
  rw [if_neg h1]
  have hm := S02_chi_mono y m δ hδ0
  unfold chi at hm ⊢
  by_cases ha : chiProp y m (δ / δ.minFac)
  · rw [if_pos ha, if_pos (key ha)]; ring
  · rw [if_neg ha] at hm ⊢
    by_cases hb : chiProp y m δ
    · rw [if_pos hb] at hm; norm_num at hm
    · rw [if_neg hb]; ring

end KappaOmega2
