import KappaOmega2.Statements
import KappaOmega2.Items.S04_Base

/-!
# S04: `Σ₂ + Σ₃ ≥ −Σ_{δ ∈ 𝒟, δ ∣ A} Λ{(A/δ, P(√(y/δ))), φ(δ), w}` (plan in `S04_PLAN.md`)
-/

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma S04_memD (y z m : ℝ) (δ : ℕ) :
    δ ∈ Dset y z m ↔ (δ ∣ primorialLt z ∧ primorialLt z ≠ 0) ∧ δ ≠ 1 ∧ chibar y m δ = 1 ∧ Odd (ω δ) ∧
      (ω δ : ℝ) ≤ 1 / m := by
  classical
  unfold Dset
  rw [Finset.mem_filter, Nat.mem_divisors]

lemma S04_primorial_ne (z : ℝ) : primorialLt z ≠ 0 := by
  unfold primorialLt
  exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)

lemma S04_sqrt_le (y : ℝ) (δ p : ℕ) (hδ : 0 < δ) (h : y ≤ (δ : ℝ) * (p : ℝ) ^ 2) :
    Real.sqrt (y / δ) ≤ p := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have : y / δ ≤ (p : ℝ) ^ 2 := by rw [div_le_iff₀ hδR]; linarith
  calc Real.sqrt (y / δ) ≤ Real.sqrt ((p : ℝ) ^ 2) := Real.sqrt_le_sqrt this
    _ = p := Real.sqrt_sq (by positivity)

lemma S04_Ssv_eq (a : ℕ) (z : ℝ) :
    Ssv a z = if a.primeFactors.filter (fun q : ℕ => (q : ℝ) < z) = ∅ then 1 else 0 := by
  classical
  unfold Ssv
  congr 1
  apply propext
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h q hq; exact not_lt.2 (h q hq)
  · intro h q hq; exact not_lt.1 (h hq)

theorem itemS04 : ItemS04 := by
  classical
  intro y z m W1' w A hm hy hA hz hw hD
  have hrad := S04_rad_self A z hA hz
  have hA0 : A ≠ 0 := hA.ne_zero
  have hAP := S04_dvd_primorial A z hA hz
  have hPne := S04_primorial_ne z
  set D := Dset y z m with hDdef
  set L : ℕ → ℝ := fun δ => LamA (radLt (A / δ) (Real.sqrt (y / δ))) (phiW W1' w δ) w with hL
  set F3 := A.divisors.filter (fun δ : ℕ => Odd (ω δ) ∧ 3 ≤ ω δ ∧ (ω δ : ℝ) ≤ 1 / m) with hF3
  -- decomposition of the sum over 𝒟
  have hsplit : ∑ δ ∈ D.filter (· ∣ A), L δ =
      ∑ p ∈ A.primeFactors, (if p ∈ D then L p else 0) + ∑ δ ∈ F3, (if δ ∈ D then L δ else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext δ
      simp only [Finset.mem_filter, Finset.mem_union, hF3, Nat.mem_divisors]
      constructor
      · rintro ⟨hδD, hδA⟩
        have hδD' := (S04_memD y z m δ).1 hδD
        obtain ⟨-, hδ1, -, hodd, hωm⟩ := hδD'
        have hδsq : Squarefree δ := hA.squarefree_of_dvd hδA
        have hω' : ω δ = δ.primeFactors.card := ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors
        obtain ⟨k, hk⟩ := hodd
        by_cases h1 : ω δ = 1
        · left
          rw [hω'] at h1
          obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
          have hpδ : δ = p := by
            have := Nat.prod_primeFactors_of_squarefree hδsq
            rw [hp] at this; simpa using this.symm
          have hpp : p.Prime := by
            have : p ∈ δ.primeFactors := by rw [hp]; simp
            exact Nat.prime_of_mem_primeFactors this
          refine ⟨Nat.mem_primeFactors.2 ⟨by rw [hpδ]; exact hpp, hδA, hA0⟩, hδD⟩
        · right
          exact ⟨⟨⟨hδA, hA0⟩, ⟨k, hk⟩, by omega, hωm⟩, hδD⟩
      · rintro (⟨hp, hpD⟩ | ⟨⟨⟨hδA, _⟩, _⟩, hδD⟩)
        · exact ⟨hpD, Nat.dvd_of_mem_primeFactors hp⟩
        · exact ⟨hδD, hδA⟩
    · rw [Finset.disjoint_left]
      intro δ h1 h2
      rw [Finset.mem_filter] at h1 h2
      have hpp := Nat.prime_of_mem_primeFactors h1.1
      have := (Finset.mem_filter.mp h2.1).2.2.1
      rw [ArithmeticFunction.cardDistinctFactors_apply_prime hpp] at this
      omega
  -- Σ₂ termwise
  have h2 : ∀ p ∈ A.primeFactors, -(if p ∈ D then L p else 0) ≤
      -(chibar y m p) * (phiW W1' w p * Ssv (A / p) (Real.sqrt (y / p)) +
        ∑ q ∈ (A / p).primeFactors.filter (fun q : ℕ => q < p ∧ (q : ℝ) ^ 2 * p < y),
          w q * Ssv (A / (p * q)) p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpA := Nat.dvd_of_mem_primeFactors hp
    rcases S04_chibar_01 y m p hpp.ne_zero hpp.ne_one with h0 | h1
    · have hpD : p ∉ D := by
        intro hpD
        have := ((S04_memD y z m p).1 hpD).2.2.1
        rw [h0] at this; norm_num at this
      rw [if_neg hpD, h0]; simp
    · obtain ⟨hyp3, hm1⟩ := S04_chibar_prime y m p hpp h1
      have hpD : p ∈ D := by
        rw [hDdef, S04_memD]
        refine ⟨⟨hpA.trans hAP, hPne⟩, hpp.ne_one, h1, ?_, ?_⟩
        · rw [ArithmeticFunction.cardDistinctFactors_apply_prime hpp]; decide
        · rw [ArithmeticFunction.cardDistinctFactors_apply_prime hpp]; exact_mod_cast hm1
      rw [if_pos hpD, h1]
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hsle : Real.sqrt (y / p) ≤ p :=
        S04_sqrt_le y p p hpp.pos (by nlinarith)
      have hiff : ∀ q : ℕ, ((q : ℝ) < Real.sqrt (y / p) ↔ (q : ℝ) ^ 2 * p < y) := by
        intro q
        rw [Real.lt_sqrt (by positivity), lt_div_iff₀ hpR]
      set PB := (A / p).primeFactors.filter (fun q : ℕ => (q : ℝ) < Real.sqrt (y / p)) with hPB
      have hLp : L p = S04val (phiW W1' w p) w PB := by
        rw [hL]; exact S04_LamA_rad _ _ _ _
      rw [hLp, S04_Ssv_eq]
      rw [← hPB]
      set QS := (A / p).primeFactors.filter (fun q : ℕ => q < p ∧ (q : ℝ) ^ 2 * p < y) with hQS
      have hQSPB : QS ⊆ PB := by
        intro q hq
        rw [hQS, Finset.mem_filter] at hq
        rw [hPB, Finset.mem_filter]
        exact ⟨hq.1, (hiff q).2 hq.2.2⟩
      suffices H : phiW W1' w p * (if PB = ∅ then 1 else 0) + ∑ q ∈ QS, w q * Ssv (A / (p * q)) p ≤
          S04val (phiW W1' w p) w PB by linarith
      by_cases hPB0 : PB = ∅
      · have hQS0 : QS = ∅ := Finset.subset_empty.mp (hPB0 ▸ hQSPB)
        rw [if_pos hPB0, hQS0]
        unfold S04val; rw [if_pos hPB0]; simp
      · rw [if_neg hPB0, mul_zero, zero_add]
        by_cases hc1 : PB.card = 1
        · obtain ⟨q₀, hq₀⟩ := Finset.card_eq_one.1 hc1
          have hval : S04val (phiW W1' w p) w PB = w q₀ := by
            unfold S04val; rw [if_neg hPB0, if_pos hc1, hq₀, Finset.sum_singleton]
          rw [hval]
          have hsub : QS ⊆ {q₀} := hq₀ ▸ hQSPB
          have hS1 : ∀ q, w q * Ssv (A / (p * q)) p ≤ w q := by
            intro q
            unfold Ssv; split_ifs <;> simp [hw q]
          calc ∑ q ∈ QS, w q * Ssv (A / (p * q)) p ≤ ∑ q ∈ ({q₀} : Finset ℕ), w q * Ssv (A / (p * q)) p := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro q _ _
                unfold Ssv; split_ifs <;> simp [hw q]
            _ ≤ w q₀ := by rw [Finset.sum_singleton]; exact hS1 q₀
        · have hval : S04val (phiW W1' w p) w PB = 0 := by
            unfold S04val; rw [if_neg hPB0, if_neg hc1]
          rw [hval]
          have hcard : 1 < PB.card := by
            have : 0 < PB.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hPB0)
            omega
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro q hq
          have hqPB := hQSPB hq
          obtain ⟨q', hq'PB, hq'ne⟩ := Finset.exists_mem_ne hcard q
          rw [hPB, Finset.mem_filter] at hq'PB hqPB
          have hqp := Nat.prime_of_mem_primeFactors hqPB.1
          have hq'p := Nat.prime_of_mem_primeFactors hq'PB.1
          have hAp0 : A / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hpA) hpp.pos)
          have hcop : Nat.Coprime q q' := (Nat.coprime_primes hqp hq'p).2 (Ne.symm hq'ne)
          have hmul : q * q' ∣ A / p :=
            hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hqPB.1) (Nat.dvd_of_mem_primeFactors hq'PB.1)
          have hq'dvd : q' ∣ A / (p * q) := by
            rw [← Nat.div_div_eq_div_mul]
            exact Nat.dvd_div_of_mul_dvd hmul
          have hne0 : A / (p * q) ≠ 0 := by
            intro h0
            rw [h0] at hq'dvd
            rw [← Nat.div_div_eq_div_mul] at h0
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero hAp0) (Nat.dvd_of_mem_primeFactors hqPB.1)
            have := Nat.div_pos this hqp.pos
            omega
          have hS0 : Ssv (A / (p * q)) p = 0 := by
            unfold Ssv
            rw [if_neg]
            intro hall
            have := hall q' (Nat.mem_primeFactors.2 ⟨hq'p, hq'dvd, hne0⟩)
            linarith [hq'PB.2]
          rw [hS0, mul_zero]
  -- Σ₃ termwise
  have h3 : ∀ δ ∈ F3, -(if δ ∈ D then L δ else 0) ≤ (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ := by
    intro δ hδ
    rw [hF3, Finset.mem_filter, Nat.mem_divisors] at hδ
    obtain ⟨⟨hδA, -⟩, hodd, h3ω, hωm⟩ := hδ
    have hδsq : Squarefree δ := hA.squarefree_of_dvd hδA
    have hδ0 : δ ≠ 0 := hδsq.ne_zero
    have hω' : ω δ = δ.primeFactors.card := ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors
    have hδ1 : δ ≠ 1 := by rintro rfl; simp at h3ω
    have hμ : (μ δ : ℝ) = -1 := by
      rw [S04_mu_eq δ hδsq, ← hω']; exact hodd.neg_one_pow
    rcases S04_chibar_01 y m δ hδ0 hδ1 with h0 | h1
    · have hδD : δ ∉ D := by
        intro hδD
        have := ((S04_memD y z m δ).1 hδD).2.2.1
        rw [h0] at this; norm_num at this
      rw [if_neg hδD, h0]; simp
    · have hδD : δ ∈ D := by
        rw [hDdef, S04_memD]
        exact ⟨⟨hδA.trans hAP, hPne⟩, hδ1, h1, hodd, hωm⟩
      rw [if_pos hδD, hμ, h1, S04_inner W1' w A δ hδ0, S04_rad_pf]
      obtain ⟨hφ0, hwφ⟩ := hD δ hδD hδA
      obtain ⟨hc1, hc0⟩ := S04_chi y m δ hδ1 h1
      have hyle := S04_y_le y m δ hδ0 hδ1 hc1 hc0
      have hsle := S04_sqrt_le y δ δ.minFac (Nat.pos_of_ne_zero hδ0) hyle
      have hLδ : L δ = S04val (phiW W1' w δ) w
          ((A / δ).primeFactors.filter (fun q : ℕ => (q : ℝ) < Real.sqrt (y / δ))) := by
        rw [hL]; exact S04_LamA_rad _ _ _ _
      rw [hLδ]
      have hmono := S04_val_mono (phiW W1' w δ) w
        ((A / δ).primeFactors.filter (fun q : ℕ => (q : ℝ) < Real.sqrt (y / δ)))
        (A.primeFactors.filter (fun p : ℕ => (p : ℝ) < (δ.minFac : ℝ)))
        (by
          intro q hq
          rw [Finset.mem_filter] at hq ⊢
          refine ⟨Nat.primeFactors_mono (Nat.div_dvd_of_dvd hδA) hA0 hq.1, ?_⟩
          linarith [hq.2])
        hφ0 hw
        (by
          intro q hq
          rw [Finset.mem_filter] at hq
          apply hwφ h3ω q (Nat.prime_of_mem_primeFactors hq.1)
          exact_mod_cast hq.2)
      linarith
  -- assemble
  rw [hsplit]
  unfold Sig2 Sig3
  rw [hrad, neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  exact add_le_add (Finset.sum_le_sum h2) (Finset.sum_le_sum h3)

end KappaOmega2
