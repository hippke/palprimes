import KappaOmega2.Statements
import KappaOmega2.Items.S11_Core

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves KappaOmega2.S11c
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma s11_etaOf (B : BandData) (y : ℝ) (δ : ℕ) : etaOf B y δ ∈ ([] :: B.etas) := by
  classical
  unfold etaOf
  split_ifs with h
  · by_cases hi : Nat.find h < B.etas.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact List.mem_cons_of_mem _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact List.mem_cons_self
  · exact List.mem_cons_self

lemma s11_Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf
  split_ifs with h1 h2 h3
  · exact le_rfl
  · apply le_min
    · have : 0 ≤ t ^ 2 := sq_nonneg t
      unfold kSq; linarith
    · linarith
  · unfold mm at *; linarith
  · unfold W1; norm_num

lemma s11_Wf_le (t : ℝ) : Wf t ≤ W1 := by
  unfold Wf
  split_ifs with h1 h2 h3
  · unfold W1; norm_num
  · refine le_trans (min_le_right _ _) ?_
    unfold mm W1; linarith
  · unfold mm UU W1 at *; linarith
  · exact le_rfl

lemma s11_wy_nonneg (y : ℝ) (p : ℕ) : 0 ≤ wy y p := s11_Wf_nonneg _

lemma s11_wy_le (y : ℝ) (p : ℕ) : wy y p ≤ W1 := s11_Wf_le _

lemma s11_W1_nonneg : 0 ≤ W1 := by unfold W1; norm_num

lemma s11_phi_abs (y : ℝ) (n : ℕ) : |phiW W1 (wy y) n| ≤ W1 * (1 + (ω n : ℝ)) := by
  unfold phiW
  have h1 : ∑ p ∈ n.primeFactors, wy y p ≤ ∑ p ∈ n.primeFactors, W1 :=
    Finset.sum_le_sum (fun p _ => s11_wy_le y p)
  have h2 : 0 ≤ ∑ p ∈ n.primeFactors, wy y p := Finset.sum_nonneg (fun p _ => s11_wy_nonneg y p)
  have h3 : ∑ p ∈ n.primeFactors, W1 = (ω n : ℝ) * W1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  have := s11_W1_nonneg
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (ω n)]

lemma s11_chi_le (y : ℝ) (hy : 1 < y) (n : ℕ) (hsq : Squarefree n) (hn1 : n ≠ 1)
    (hchi : chiProp y mm n) : (n : ℝ) ≤ y := by
  classical
  have hn0 : n ≠ 0 := hsq.ne_zero
  obtain ⟨p, hpdef⟩ : ∃ p, n.minFac = p := ⟨_, rfl⟩
  have hp : p.Prime := hpdef ▸ Nat.minFac_prime hn1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
  by_cases hA : Even (ω n) ∨ (ω n : ℝ) ≤ 1 / mm
  · have := hchi n (Nat.mem_divisors.2 ⟨dvd_rfl, hn0⟩) hn1 hA
    rw [hpdef] at this
    have h4 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h5 : (n : ℝ) * 1 ≤ n * (p : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
    linarith
  · push Not at hA
    obtain ⟨hodd, hbig⟩ := hA
    have hodd' : ¬ Even (ω n) := by simpa using hodd
    have hpd : p ∣ n := hpdef ▸ Nat.minFac_dvd n
    obtain ⟨h, hh⟩ := hpd
    have hh0 : h ≠ 0 := by rintro rfl; simp at hh; exact hn0 hh
    have hcop : Nat.Coprime p h := by
      have := hsq; rw [hh] at this
      exact (Nat.squarefree_mul_iff.1 this).1
    have hpnh : ¬ p ∣ h := fun hd => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hd)
    have hω : ω n = ω h + 1 := by
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
        ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, hh,
        Nat.primeFactors_mul hp.ne_zero hh0, hp.primeFactors]
      have : p ∉ h.primeFactors := fun hm => hpnh (Nat.dvd_of_mem_primeFactors hm)
      rw [← Finset.insert_eq, Finset.card_insert_of_notMem this]
    have hωe : Even (ω h) := by
      rw [hω] at hodd'
      by_contra hne
      exact hodd' (by rcases Nat.not_even_iff_odd.1 hne with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩)
    have hh1 : h ≠ 1 := by
      rintro rfl
      rw [hω] at hbig
      simp at hbig
      unfold mm at hbig
      norm_num at hbig
    have hhn : h ∣ n := ⟨p, by rw [hh]; ring⟩
    have hq : h.minFac.Prime := Nat.minFac_prime hh1
    have hqn : h.minFac ∣ n := (Nat.minFac_dvd h).trans hhn
    have hpq : p ≤ h.minFac := hpdef ▸ Nat.minFac_le_of_dvd hq.two_le hqn
    have hlt := hchi h (Nat.mem_divisors.2 ⟨hhn, hn0⟩) hh1 (Or.inl hωe)
    have hpq' : (p : ℝ) ≤ h.minFac := by exact_mod_cast hpq
    have hq1 : (1 : ℝ) ≤ h.minFac := by exact_mod_cast hq.one_lt.le
    have hh' : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh0
    have hnp : (n : ℝ) = p * h := by rw [hh]; push_cast; ring
    rw [hnp]
    have e1 : (p : ℝ) * h ≤ (h.minFac : ℝ) * h := mul_le_mul_of_nonneg_right hpq' hh'.le
    have e2 : (h.minFac : ℝ) * h ≤ (h : ℝ) * (h.minFac : ℝ) ^ 2 := by nlinarith
    linarith

/-! ### Counting pairs with prescribed lcm -/

lemma s11_card_divisors_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).divisors.card = 2 ^ P.card := by
  have h := sum_divisors_primes P hP (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powerset] at h
  exact_mod_cast h

lemma s11_sum_card_divisors (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ d ∈ (∏ p ∈ P, p).divisors, (d.divisors.card : ℝ) = 3 ^ P.card := by
  rw [sum_divisors_primes P hP (fun d => (d.divisors.card : ℝ))]
  have : ∀ t ∈ P.powerset, ((∏ p ∈ t, p).divisors.card : ℝ) = 2 ^ t.card * 1 ^ (P.card - t.card) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [s11_card_divisors_prod t (fun p hp => hP p (ht hp))]
    push_cast; ring
  rw [Finset.sum_congr rfl this]
  have := Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 P
  rw [this]; norm_num

lemma s11_pairs (m : ℕ) (hm : Squarefree m) :
    (((m.divisors ×ˢ m.divisors).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = m)).card : ℝ) ≤ 3 ^ m.primeFactors.card := by
  classical
  have hm0 : m ≠ 0 := hm.ne_zero
  have hP : ∀ p ∈ m.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hmeq : m = ∏ p ∈ m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hm).symm
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  calc ∑ d1 ∈ m.divisors, ∑ d2 ∈ m.divisors, (if Nat.lcm d1 d2 = m then (1 : ℝ) else 0)
      ≤ ∑ d1 ∈ m.divisors, (d1.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro d1 hd1
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hd10 : d1 ≠ 0 := (Nat.pos_of_mem_divisors hd1).ne'
        have : (m.divisors.filter (fun d2 => Nat.lcm d1 d2 = m)).card ≤ d1.divisors.card := by
          apply Finset.card_le_card_of_injOn (fun d2 => Nat.gcd d1 d2)
          · intro d2 _
            rw [Finset.mem_coe, Nat.mem_divisors]
            exact ⟨Nat.gcd_dvd_left _ _, hd10⟩
          · intro d2 hd2 d2' hd2' he
            simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter] at hd2 hd2'
            have e1 := Nat.gcd_mul_lcm d1 d2
            have e2 := Nat.gcd_mul_lcm d1 d2'
            rw [hd2.2] at e1
            rw [hd2'.2] at e2
            simp only at he
            rw [he] at e1
            have : d1 * d2 = d1 * d2' := by rw [← e1, ← e2]
            exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd10) this
        exact_mod_cast this
    _ = 3 ^ m.primeFactors.card := by
        conv_lhs => rw [hmeq]
        rw [s11_sum_card_divisors _ hP]

lemma s11_sub (δ δ' ℓ n : ℕ) (hδ : Squarefree δ) (hδ' : Squarefree δ') (h : ℓ * δ = n) (hd' : δ' ∣ n)
    (hℓ : ∀ q, q.Prime → q ∣ ℓ → q < δ.minFac) (hle : δ.minFac ≤ δ'.minFac) :
    δ'.primeFactors ⊆ δ.primeFactors := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hqn : q ∣ ℓ * δ := h ▸ hqd.trans hd'
  rcases (Nat.Prime.dvd_mul hqp).1 hqn with h1 | h1
  · exfalso
    have := hℓ q hqp h1
    have h2 : δ'.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqd
    omega
  · exact Nat.mem_primeFactors.2 ⟨hqp, h1, hδ.ne_zero⟩

lemma s11_uniq (δ δ' ℓ ℓ' n : ℕ) (hδ : Squarefree δ) (hδ' : Squarefree δ') (h : ℓ * δ = n) (h' : ℓ' * δ' = n)
    (hℓ : ∀ q, q.Prime → q ∣ ℓ → q < δ.minFac) (hℓ' : ∀ q, q.Prime → q ∣ ℓ' → q < δ'.minFac)
    (hc : δ.primeFactors.card = δ'.primeFactors.card) : δ = δ' := by
  have key : δ.primeFactors = δ'.primeFactors := by
    rcases le_total δ.minFac δ'.minFac with hle | hle
    · have hsub := s11_sub δ δ' ℓ n hδ hδ' h (h' ▸ dvd_mul_left δ' ℓ') hℓ hle
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · have hsub := s11_sub δ' δ ℓ' n hδ' hδ h' (h ▸ dvd_mul_left δ ℓ) hℓ' hle
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← Nat.prod_primeFactors_of_squarefree hδ, ← Nat.prod_primeFactors_of_squarefree hδ', key]

lemma s11_inner (L : Finset ℕ) (Λ : ℕ → ℝ) (C : ℝ) (δ n : ℕ) (hn : Squarefree n)
    (hC : ∀ d, |Λ d| ≤ C) :
    |∑ d1 ∈ L, ∑ d2 ∈ L, (if Nat.lcm d1 d2 * δ = n then Λ d1 * Λ d2 else 0)| ≤
      C ^ 2 * 3 ^ n.primeFactors.card := by
  classical
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hn0 : n ≠ 0 := hn.ne_zero
  have h1 : |∑ d1 ∈ L, ∑ d2 ∈ L, (if Nat.lcm d1 d2 * δ = n then Λ d1 * Λ d2 else 0)| ≤
      ∑ d1 ∈ L, ∑ d2 ∈ L, (if Nat.lcm d1 d2 * δ = n then C ^ 2 else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d1 _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d2 _ => ?_)
    by_cases h : Nat.lcm d1 d2 * δ = n
    · rw [if_pos h, if_pos h, abs_mul]
      calc |Λ d1| * |Λ d2| ≤ C * C := mul_le_mul (hC d1) (hC d2) (abs_nonneg _) hC0
        _ = C ^ 2 := by ring
    · rw [if_neg h, if_neg h]; simp
  refine h1.trans ?_
  have h2 : ∑ d1 ∈ L, ∑ d2 ∈ L, (if Nat.lcm d1 d2 * δ = n then C ^ 2 else 0) =
      C ^ 2 * (((L ×ˢ L).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 * δ = n)).card : ℝ) := by
    rw [Finset.card_filter, Finset.sum_product]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d1 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d2 _
    split_ifs <;> simp
  rw [h2]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases hδn : δ ∣ n
  · obtain ⟨m, hm⟩ := hδn
    have hδ0 : δ ≠ 0 := by rintro rfl; simp at hm; exact hn0 hm
    have hmn : m ∣ n := ⟨δ, by rw [hm]; ring⟩
    have hmsq : Squarefree m := hn.squarefree_of_dvd hmn
    have hsub : (L ×ˢ L).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 * δ = n) ⊆
        (m.divisors ×ˢ m.divisors).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = m) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hl : Nat.lcm p.1 p.2 = m := by
        have : Nat.lcm p.1 p.2 * δ = m * δ := by rw [hp.2, hm]; ring
        exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hδ0) this
      rw [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
      refine ⟨⟨⟨?_, hmsq.ne_zero⟩, ⟨?_, hmsq.ne_zero⟩⟩, hl⟩
      · rw [← hl]; exact Nat.dvd_lcm_left _ _
      · rw [← hl]; exact Nat.dvd_lcm_right _ _
    calc (((L ×ˢ L).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 * δ = n)).card : ℝ)
        ≤ (((m.divisors ×ˢ m.divisors).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 = m)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ 3 ^ m.primeFactors.card := s11_pairs m hmsq
      _ ≤ 3 ^ n.primeFactors.card := by
          apply pow_le_pow_right₀ (by norm_num)
          exact Finset.card_le_card (Nat.primeFactors_mono hmn hn0)
  · have : (L ×ˢ L).filter (fun p : ℕ × ℕ => Nat.lcm p.1 p.2 * δ = n) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro p _ h
      exact hδn ⟨Nat.lcm p.1 p.2, by rw [← h]; ring⟩
    rw [this]; simp

lemma s11_T1_supp (y : ℝ) (hy : 1 < y) (n : ℕ)
    (h : (if n ∣ primorialLt (y ^ UU) then (μ n : ℝ) * chi y mm n * phiW W1 (wy y) n else 0) ≠ 0) :
    Squarefree n ∧ 1 ≤ n ∧ (n : ℝ) ≤ y ∧ n ∣ primorialLt (y ^ UU) := by
  classical
  by_cases hnP : n ∣ primorialLt (y ^ UU)
  · rw [if_pos hnP] at h
    have hμ : (μ n : ℝ) ≠ 0 := by
      intro h0; apply h; rw [h0]; ring
    have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 (by exact_mod_cast hμ)
    have hchi : chi y mm n ≠ 0 := by
      intro h0; apply h; rw [h0]; ring
    have hcp : chiProp y mm n := by
      unfold chi at hchi
      by_contra hn
      rw [if_neg hn] at hchi; exact hchi rfl
    refine ⟨hsq, Nat.one_le_iff_ne_zero.2 hsq.ne_zero, ?_, hnP⟩
    by_cases hn1 : n = 1
    · rw [hn1]; simpa using hy.le
    · exact s11_chi_le y hy n hsq hn1 hcp
  · rw [if_neg hnP] at h; exact absurd rfl h

lemma s11_T2_pairs (b : ℕ) (B : BandData) (y : ℝ) (hy : 1 < y) (n : ℕ)
    (h : ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) ≠ 0) :
    ∃ δ ∈ Dset y (y ^ UU) mm, ∃ d1 ∈ ltSet (Real.sqrt (y / δ)), ∃ d2 ∈ ltSet (Real.sqrt (y / δ)),
      Nat.lcm d1 d2 * δ = n ∧ LamD b B y δ d1 ≠ 0 ∧ LamD b B y δ d2 ≠ 0 := by
  classical
  obtain ⟨δ, hδ, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h2 : ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) ≠ 0 := by
    intro h0; apply h1; rw [h0, mul_zero]
  obtain ⟨d1, hd1, h3⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  obtain ⟨d2, hd2, h4⟩ := Finset.exists_ne_zero_of_sum_ne_zero h3
  by_cases hc : Nat.lcm d1 d2 * δ = n
  · rw [if_pos hc] at h4
    refine ⟨δ, hδ, d1, hd1, d2, hd2, hc, ?_, ?_⟩
    · intro h0; apply h4; rw [h0, zero_mul]
    · intro h0; apply h4; rw [h0, mul_zero]
  · rw [if_neg hc] at h4; exact absurd rfl h4

lemma s11_T2_supp (b : ℕ) (B : BandData) (y : ℝ) (hy : 1 < y) (n : ℕ) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm)
    (d1 d2 : ℕ) (hd1 : d1 ∈ ltSet (Real.sqrt (y / δ))) (hd2 : d2 ∈ ltSet (Real.sqrt (y / δ)))
    (hn : Nat.lcm d1 d2 * δ = n) (h1 : LamD b B y δ d1 ≠ 0) (h2 : LamD b B y δ d2 ≠ 0) :
    Squarefree n ∧ 1 ≤ n ∧ (n : ℝ) ≤ y ∧ n ∣ primorialLt (y ^ UU) := by
  obtain ⟨hδ0, hδ1, hsqδ, hdvd, hpz, hyle⟩ := c_Dfacts y δ hδ
  have s1 := c_supp b (etaOf B y δ) (y / δ) d1 h1
  have s2 := c_supp b (etaOf B y δ) (y / δ) d2 h2
  obtain ⟨hsq, hc, hdP⟩ := c_lcm_dvdP y hy δ hδ d1 d2 hd1 hd2 s1.1 s2.1
  rw [hn] at hsq hdP
  refine ⟨hsq, Nat.one_le_iff_ne_zero.2 hsq.ne_zero, ?_, hdP⟩
  have hd1' : (d1 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at hd1; rw [Finset.mem_filter] at hd1; exact hd1.2.2
  have hd2' : (d2 : ℝ) < Real.sqrt (y / δ) := by
    unfold ltSet at hd2; rw [Finset.mem_filter] at hd2; exact hd2.2.2
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
  have hl : (Nat.lcm d1 d2 : ℝ) ≤ d1 * d2 := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero s1.1.ne_zero) (Nat.pos_of_ne_zero s2.1.ne_zero)) (Nat.lcm_dvd_mul d1 d2)
  have hsqrt : Real.sqrt (y / δ) * Real.sqrt (y / δ) = y / δ := Real.mul_self_sqrt (by positivity)
  have hdd : (d1 : ℝ) * d2 < y / δ := by
    rw [← hsqrt]
    exact mul_lt_mul'' hd1' hd2' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [← hn]
  push_cast
  calc (Nat.lcm d1 d2 : ℝ) * δ ≤ (d1 * d2) * δ := mul_le_mul_of_nonneg_right hl hδpos.le
    _ ≤ y / δ * δ := mul_le_mul_of_nonneg_right hdd.le hδpos.le
    _ = y := by field_simp

lemma s11_primes_lt (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm) (d1 d2 : ℕ)
    (hd1 : d1 ∈ ltSet (Real.sqrt (y / δ))) (hd2 : d2 ∈ ltSet (Real.sqrt (y / δ)))
    (s1 : Squarefree d1) (s2 : Squarefree d2) :
    ∀ q, q.Prime → q ∣ Nat.lcm d1 d2 → q < δ.minFac := by
  intro q hq hql
  obtain ⟨hlt1, _⟩ := c_small y hy δ hδ d1 hd1
  obtain ⟨hlt2, _⟩ := c_small y hy δ hδ d2 hd2
  have : q ∣ d1 * d2 := hql.trans (Nat.lcm_dvd_mul d1 d2)
  rcases (Nat.Prime.dvd_mul hq).1 this with h | h
  · have : (q : ℝ) ≤ d1 := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s1.ne_zero) h
    have : (q : ℝ) < δ.minFac := by linarith
    exact_mod_cast this
  · have : (q : ℝ) ≤ d2 := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero s2.ne_zero) h
    have : (q : ℝ) < δ.minFac := by linarith
    exact_mod_cast this

lemma s11_T2_bound (b : ℕ) (B : BandData) (y : ℝ) (hy : 1 < y) (n : ℕ) (hn : Squarefree n) (C : ℝ)
    (hCb : ∀ δ ∈ Dset y (y ^ UU) mm, ∀ d, |LamD b B y δ d| ≤ C) :
    |∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0)| ≤
      86 * (86 * W1) * C ^ 2 * 3 ^ n.primeFactors.card := by
  classical
  set D := Dset y (y ^ UU) mm with hD
  set G := D.filter (fun δ : ℕ => ∃ d1 ∈ ltSet (Real.sqrt (y / (δ : ℝ))), ∃ d2 ∈ ltSet (Real.sqrt (y / (δ : ℝ))),
    Nat.lcm d1 d2 * δ = n) with hG
  have hW1 := s11_W1_nonneg
  have hC0 : ∀ δ : ℕ, δ ∈ D → 0 ≤ C := fun δ hδ => le_trans (abs_nonneg _) (hCb δ hδ 0)
  -- terms outside G vanish
  have hout : ∀ δ : ℕ, δ ∈ D → δ ∉ G → phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) = 0 := by
    intro δ hδ hnG
    have : ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro d1 hd1
      apply Finset.sum_eq_zero; intro d2 hd2
      rw [if_neg]
      intro hc
      exact hnG (Finset.mem_filter.2 ⟨hδ, d1, hd1, d2, hd2, hc⟩)
    rw [this, mul_zero]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hout]
  have hphi : ∀ δ ∈ D, |phiW W1 (wy y) δ| ≤ 86 * W1 := by
    intro δ hδ
    have h1 := s11_phi_abs y δ
    obtain ⟨_, _, _, _, hω⟩ := c_mem y δ hδ
    unfold mm at hω
    have : (ω δ : ℝ) ≤ 85 := by linarith
    nlinarith
  have hGcard : G.card ≤ 86 := by
    have : G.card ≤ (Finset.range 86).card := by
      apply Finset.card_le_card_of_injOn (fun δ => δ.primeFactors.card)
      · intro δ hδ
        rw [Finset.mem_coe, Finset.mem_filter] at hδ
        obtain ⟨_, _, _, _, hω⟩ := c_mem y δ hδ.1
        unfold mm at hω
        rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hω
        have : (δ.primeFactors.card : ℝ) ≤ 85 := by linarith
        have : δ.primeFactors.card ≤ 85 := by exact_mod_cast this
        simp only [Finset.coe_range, Set.mem_Iio]; omega
      · intro δ hδ δ' hδ' he
        simp only [Finset.mem_coe, hG, Finset.mem_filter] at hδ hδ'
        obtain ⟨hδD, d1, hd1, d2, hd2, hc⟩ := hδ
        obtain ⟨hδD', d1', hd1', d2', hd2', hc'⟩ := hδ'
        obtain ⟨hδ0, _, hsqδ, _⟩ := c_Dfacts y δ hδD
        obtain ⟨hδ0', _, hsqδ', _⟩ := c_Dfacts y δ' hδD'
        by_cases hz : δ = δ'
        · exact hz
        · -- need squarefree d's: they divide the squarefree n
          have hl1 : Nat.lcm d1 d2 ∣ n := ⟨δ, by rw [← hc]⟩
          have hl1' : Nat.lcm d1' d2' ∣ n := ⟨δ', by rw [← hc']⟩
          have s1 : Squarefree d1 := hn.squarefree_of_dvd ((Nat.dvd_lcm_left d1 d2).trans hl1)
          have s2 : Squarefree d2 := hn.squarefree_of_dvd ((Nat.dvd_lcm_right d1 d2).trans hl1)
          have s1' : Squarefree d1' := hn.squarefree_of_dvd ((Nat.dvd_lcm_left d1' d2').trans hl1')
          have s2' : Squarefree d2' := hn.squarefree_of_dvd ((Nat.dvd_lcm_right d1' d2').trans hl1')
          exact s11_uniq δ δ' (Nat.lcm d1 d2) (Nat.lcm d1' d2') n hsqδ hsqδ' hc hc'
            (s11_primes_lt y hy δ hδD d1 d2 hd1 hd2 s1 s2) (s11_primes_lt y hy δ' hδD' d1' d2' hd1' hd2' s1' s2') he
    simpa using this
  calc |∑ δ ∈ G, phiW W1 (wy y) δ * ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0)|
      ≤ ∑ δ ∈ G, (86 * W1) * (C ^ 2 * 3 ^ n.primeFactors.card) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun δ hδ => ?_)
        have hδD := (Finset.mem_filter.1 hδ).1
        rw [abs_mul]
        exact mul_le_mul (hphi δ hδD) (s11_inner _ _ C δ n hn (hCb δ hδD)) (abs_nonneg _) (by positivity)
    _ = (G.card : ℝ) * ((86 * W1) * (C ^ 2 * 3 ^ n.primeFactors.card)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 86 * ((86 * W1) * (C ^ 2 * 3 ^ n.primeFactors.card)) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hGcard) (by positivity)
    _ = 86 * (86 * W1) * C ^ 2 * 3 ^ n.primeFactors.card := by ring

lemma s11_card_le (n : ℕ) : (1 + (ω n : ℝ)) ≤ 3 ^ n.primeFactors.card := by
  rw [← ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  generalize ω n = k
  induction k with
  | zero => simp
  | succ k ih => push_cast; rw [pow_succ]; nlinarith [Nat.cast_nonneg (α := ℝ) k]

set_option maxRecDepth 20000 in
theorem itemS11 : ItemS11 := by
  classical
  intro b hb B hB hA ε hε0 hε1
  obtain ⟨C, x₀, hC⟩ := hA
  set c0 : ℝ := (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 with hc0def
  have hc0 : 0 < c0 := by positivity
  set X : ℝ := max x₀ 2 with hX
  have hX2 : 2 ≤ X := le_max_right _ _
  set y₀ : ℝ := X ^ (1 / c0) with hy₀
  have hy₀1 : 1 < y₀ := Real.one_lt_rpow (by linarith) (by positivity)
  refine ⟨W1 * (1 + 2 * 86 ^ 2 * C ^ 2), y₀, ?_⟩
  intro y hy n hne
  have hy1 : 1 < y := lt_of_lt_of_le hy₀1 hy
  have hyc : X ≤ y ^ c0 := by
    calc X = (X ^ (1 / c0)) ^ c0 := by
          rw [← Real.rpow_mul (by linarith)]; field_simp; simp
      _ ≤ y ^ c0 := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hy hc0.le
  have hxδ : ∀ δ ∈ Dset y (y ^ UU) mm, x₀ ≤ y / δ := fun δ hδ =>
    (le_max_left x₀ 2).trans (hyc.trans (c_ydelta y hy1 δ hδ))
  have hCb : ∀ δ ∈ Dset y (y ^ UU) mm, ∀ d, |LamD b B y δ d| ≤ C := by
    intro δ hδ d
    obtain ⟨_, hb', _⟩ := hC (y / δ) (hxδ δ hδ) (etaOf B y δ) (s11_etaOf B y δ)
    exact hb' d
  have hC0 : 0 ≤ C := by
    obtain ⟨_, hb', _⟩ := hC (max x₀ 2) (le_max_left _ _) [] List.mem_cons_self
    exact le_trans (abs_nonneg _) (hb' 0)
  unfold cSieve at hne ⊢
  set T1 : ℝ := (if n ∣ primorialLt (y ^ UU) then (μ n : ℝ) * chi y mm n * phiW W1 (wy y) n else 0) with hT1def
  set T2 : ℝ := ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0) with hT2def
  have hsupp : Squarefree n ∧ 1 ≤ n ∧ (n : ℝ) ≤ y ∧ n ∣ primorialLt (y ^ UU) := by
    by_cases hT1 : T1 = 0
    · have hT2 : T2 ≠ 0 := fun h => hne (by rw [hT1, h]; ring)
      obtain ⟨δ, hδ, d1, hd1, d2, hd2, hc, h1, h2⟩ := s11_T2_pairs b B y hy1 n hT2
      exact s11_T2_supp b B y hy1 n δ hδ d1 d2 hd1 hd2 hc h1 h2
    · exact s11_T1_supp y hy1 n hT1
  refine ⟨hsupp, ?_⟩
  have hW1 := s11_W1_nonneg
  have h3 : (3 : ℝ) ^ ω n = 3 ^ n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  rw [h3]
  have hT1b : |T1| ≤ W1 * 3 ^ n.primeFactors.card := by
    by_cases hnP : n ∣ primorialLt (y ^ UU)
    · rw [hT1def, if_pos hnP, abs_mul, abs_mul]
      have h1 : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have h2 : |chi y mm n| ≤ 1 := by
        unfold chi; split_ifs <;> simp
      have h4 := s11_phi_abs y n
      have h5 := s11_card_le n
      calc |(μ n : ℝ)| * |chi y mm n| * |phiW W1 (wy y) n| ≤ 1 * 1 * (W1 * (1 + (ω n : ℝ))) :=
            mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h4 (abs_nonneg _) (by norm_num)
        _ ≤ W1 * 3 ^ n.primeFactors.card := by
            have := mul_le_mul_of_nonneg_left h5 hW1
            linarith
    · rw [hT1def, if_neg hnP, abs_zero]; positivity
  have hT2b := s11_T2_bound b B y hy1 n hsupp.1 C hCb
  have hpow : (0 : ℝ) ≤ 3 ^ n.primeFactors.card := by positivity
  calc |T1 - (1 + ε) * T2| ≤ |T1| + |(1 + ε) * T2| := abs_sub _ _
    _ = |T1| + (1 + ε) * |T2| := by rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 + ε by linarith)]
    _ ≤ W1 * 3 ^ n.primeFactors.card + 2 * (86 * (86 * W1) * C ^ 2 * 3 ^ n.primeFactors.card) := by
        have := abs_nonneg T2
        nlinarith
    _ = W1 * (1 + 2 * 86 ^ 2 * C ^ 2) * 3 ^ n.primeFactors.card := by ring

end KappaOmega2
