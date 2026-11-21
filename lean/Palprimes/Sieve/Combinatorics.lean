import Palprimes.Defs
import Palprimes.Sieve.SelbergSum

/-! # Combinatorial skeleton of the weighted sieve (M13)

- `card_sift_eq`: inclusion–exclusion over subsets of the sifting primes.
- `buchstab_le`: one Buchstab step (least prime factor).
- `exists_good_of_weighted`: positive weighted sum selects a good element. -/

open Finset Real

namespace Palprimes

/-- Sifting primes below `t` that do not divide `B`. -/
def PB (B t : ℕ) : Finset ℕ := (range t).filter (fun q => q.Prime ∧ ¬ q ∣ B)

theorem PB_prime {B t q : ℕ} (h : q ∈ PB B t) : q.Prime := (mem_filter.1 h).2.1

theorem card_sift_eq (A s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) :
    (#(A.filter (fun n => ∀ q ∈ s, ¬ q ∣ n)) : ℝ) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) * (#(A.filter ((∏ q ∈ t, q) ∣ ·)) : ℝ) := by
  classical
  have hind : ∀ m : ℕ, (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) else 0) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ (#t) * (if (∏ q ∈ t, q) ∣ m then 1 else 0) := by
    intro m
    have h1 : (if ∀ q ∈ s, ¬ q ∣ m then (1 : ℝ) else 0) =
        ∏ q ∈ s, (1 + (-(if q ∣ m then (1 : ℝ) else 0))) := by
      rw [← Finset.prod_boole]
      apply Finset.prod_congr rfl; intro q _
      split_ifs <;> simp_all
    rw [h1, Finset.prod_one_add]
    apply Finset.sum_congr rfl; intro t ht
    rw [mem_powerset] at ht
    rw [Finset.prod_neg, Finset.prod_boole]
    congr 1
    have := prod_dvd_iff_primes t (fun q hq => hs q (ht hq)) m
    simp only [this]
  rw [Finset.card_filter, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hind]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Inclusion–exclusion lower bound: main term `X Π(1 − 1/q)` minus the remainders over divisors of `P`. -/
theorem card_sift_ge (A s : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) :
    (#A : ℝ) * ∏ q ∈ s, (1 - 1 / (q : ℝ)) -
        ∑ d ∈ (∏ q ∈ s, q).divisors, |(#(A.filter (d ∣ ·)) : ℝ) - (#A : ℝ) / d| ≤
      (#(A.filter (fun n => ∀ q ∈ s, ¬ q ∣ n)) : ℝ) := by
  rw [card_sift_eq A s hs, beta_eq, Finset.mul_sum,
    sum_divisors_primes s hs (fun d => |(#(A.filter (d ∣ ·)) : ℝ) - (#A : ℝ) / d|)]
  rw [sub_le_iff_le_add, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro t _
  have h := le_abs_self ((-1 : ℝ) ^ (#t) *
    ((#A : ℝ) / ((∏ q ∈ t, q : ℕ) : ℝ) - (#(A.filter ((∏ q ∈ t, q) ∣ ·)) : ℝ)))
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_sub_comm] at h
  have e : (#A : ℝ) * ((-1 : ℝ) ^ (#t) * (1 / ((∏ q ∈ t, q : ℕ) : ℝ))) =
      (-1 : ℝ) ^ (#t) * (#(A.filter ((∏ q ∈ t, q) ∣ ·)) : ℝ) +
      (-1 : ℝ) ^ (#t) * ((#A : ℝ) / ((∏ q ∈ t, q : ℕ) : ℝ) - (#(A.filter ((∏ q ∈ t, q) ∣ ·)) : ℝ)) := by
    ring
  rw [e]; linarith

/-- **Buchstab step.** Elements free of `PB B W` but not of `PB B Z` have a least prime factor `p`
in `PB B Z \ PB B W`, and are then free of `PB B p`. -/
theorem buchstab_le (A : Finset ℕ) (B W Z : ℕ) (hWZ : W ≤ Z) :
    #(A.filter (fun n => ∀ q ∈ PB B W, ¬ q ∣ n)) ≤
      #(A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)) +
      ∑ p ∈ PB B Z \ PB B W, #(A.filter (fun n => p ∣ n ∧ ∀ q ∈ PB B p, ¬ q ∣ n)) := by
  classical
  set E : ℕ → Finset ℕ := fun p => A.filter (fun n => p ∣ n ∧ ∀ q ∈ PB B p, ¬ q ∣ n)
  have hsub : A.filter (fun n => ∀ q ∈ PB B W, ¬ q ∣ n) ⊆
      A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n) ∪ (PB B Z \ PB B W).biUnion E := by
    intro n hn
    rw [mem_filter] at hn
    by_cases hZ : ∀ q ∈ PB B Z, ¬ q ∣ n
    · exact mem_union_left _ (mem_filter.2 ⟨hn.1, hZ⟩)
    · push_neg at hZ
      set F := (PB B Z).filter (· ∣ n)
      have hF : F.Nonempty := by
        obtain ⟨q, hq, hqn⟩ := hZ; exact ⟨q, mem_filter.2 ⟨hq, hqn⟩⟩
      set p := F.min' hF
      have hpF : p ∈ F := Finset.min'_mem F hF
      rw [mem_filter] at hpF
      apply mem_union_right
      rw [mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · rw [mem_sdiff]; refine ⟨hpF.1, fun hpW => hn.2 p hpW hpF.2⟩
      · refine mem_filter.2 ⟨hn.1, hpF.2, fun q hq hqn => ?_⟩
        have hqp : q < p := by simp only [PB, mem_filter, mem_range] at hq; exact hq.1
        have hqZ : q ∈ PB B Z := by
          simp only [PB, mem_filter, mem_range] at hq hpF ⊢
          exact ⟨lt_trans hq.1 hpF.1.1, hq.2⟩
        have := Finset.min'_le F q (mem_filter.2 ⟨hqZ, hqn⟩)
        omega
  calc _ ≤ #(A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n) ∪ (PB B Z \ PB B W).biUnion E) := card_le_card hsub
    _ ≤ _ := le_trans (card_union_le _ _) (Nat.add_le_add_left card_biUnion_le _)

/-- **Selection.** If the weighted sum `Σ (λ − pen)` beats `λ` times the bad count, a good element
with `pen < λ` exists. -/
theorem exists_good_of_weighted (S0 : Finset ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (pen : ℕ → ℝ) (lam : ℝ) (hpen : ∀ n ∈ S0, 0 ≤ pen n)
    (h : lam * (#(S0.filter bad) : ℝ) < ∑ n ∈ S0, (lam - pen n)) :
    ∃ n ∈ S0, ¬ bad n ∧ pen n < lam := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ n ∈ S0, (lam - pen n) ≤ lam * (#(S0.filter bad) : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S0 bad]
    have h2 : ∑ n ∈ S0.filter (fun n => ¬ bad n), (lam - pen n) ≤ 0 := by
      apply Finset.sum_nonpos; intro n hn
      rw [mem_filter] at hn
      linarith [hne n hn.1 hn.2]
    have h3 : ∑ n ∈ S0.filter bad, (lam - pen n) ≤ ∑ n ∈ S0.filter bad, lam := by
      apply Finset.sum_le_sum; intro n hn
      linarith [hpen n (mem_filter.1 hn).1]
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    linarith
  linarith

/-- Numbers coprime to `s` up to `K` are `Pset`-factored or have a prime factor in `Q`. -/
theorem HB_le_factored_add (s Pset Q : Finset ℕ) (K : ℕ)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ K → q ∉ s → q ∈ Pset ∨ q ∈ Q)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ∉ s) (hs : ∀ q ∈ s, q.Prime) :
    HB s K ≤ ∑ n ∈ (Icc 1 K).filter (fun n => n ∈ Nat.factoredNumbers Pset), (1 : ℝ) / n +
      ∑ q ∈ Q, (1 / (q : ℝ)) * HB s (K / q) := by
  classical
  unfold HB
  set H := (Icc 1 K).filter (fun m => ∀ q ∈ s, ¬ q ∣ m)
  have hpt : ∀ n ∈ H, (1 : ℝ) / n ≤
      (if n ∈ Nat.factoredNumbers Pset then (1 : ℝ) / n else 0) +
        ∑ q ∈ Q, (if q ∣ n then (1 : ℝ) / n else 0) := by
    intro n hn
    simp only [H, mem_filter, mem_Icc] at hn
    have hpos : (0 : ℝ) ≤ 1 / n := by positivity
    have hsum0 : 0 ≤ ∑ q ∈ Q, (if q ∣ n then (1 : ℝ) / n else 0) :=
      Finset.sum_nonneg (fun q _ => by split_ifs <;> positivity)
    by_cases hf : n ∈ Nat.factoredNumbers Pset
    · rw [if_pos hf]; linarith
    · rw [if_neg hf, zero_add]
      have hn0 : n ≠ 0 := by omega
      rw [Nat.mem_factoredNumbers_iff_primeFactors_subset] at hf
      push_neg at hf
      obtain ⟨r, hr, hrP⟩ := Finset.not_subset.1 (hf hn0)
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrn := Nat.dvd_of_mem_primeFactors hr
      have hrK : r ≤ K := le_trans (Nat.le_of_dvd (by omega) hrn) hn.1.2
      have hrs : r ∉ s := fun h => hn.2 r h hrn
      have hrQ : r ∈ Q := (hcover r hrp hrK hrs).resolve_left hrP
      calc (1 : ℝ) / n = (if r ∣ n then (1 : ℝ) / n else 0) := by rw [if_pos hrn]
        _ ≤ _ := Finset.single_le_sum (f := fun q => if q ∣ n then (1 : ℝ) / n else 0)
              (fun q _ => by split_ifs <;> positivity) hrQ
  calc ∑ n ∈ H, (1 : ℝ) / n ≤ ∑ n ∈ H, ((if n ∈ Nat.factoredNumbers Pset then (1 : ℝ) / n else 0) +
        ∑ q ∈ Q, (if q ∣ n then (1 : ℝ) / n else 0)) := Finset.sum_le_sum hpt
    _ = ∑ n ∈ H.filter (fun n => n ∈ Nat.factoredNumbers Pset), (1 : ℝ) / n +
          ∑ q ∈ Q, ∑ n ∈ H.filter (q ∣ ·), (1 : ℝ) / n := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_comm]
        congr 1; apply Finset.sum_congr rfl; intro q _; rw [← Finset.sum_filter]
    _ ≤ _ := by
        apply add_le_add
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn; simp only [H, mem_filter] at hn ⊢; exact ⟨hn.1.1, hn.2⟩
          · intro n _ _; positivity
        · apply Finset.sum_le_sum; intro q hq
          have hqp := (hQ q hq).1
          have hq0 : 0 < q := hqp.pos
          -- `n = q m`
          have hsub : H.filter (q ∣ ·) ⊆ ((Icc 1 (K / q)).filter (fun m => ∀ r ∈ s, ¬ r ∣ m)).image (q * ·) := by
            intro n hn
            simp only [H, mem_filter, mem_Icc] at hn
            obtain ⟨⟨⟨h1, h2⟩, hco⟩, m, rfl⟩ := hn
            rw [mem_image]
            refine ⟨m, ?_, rfl⟩
            simp only [mem_filter, mem_Icc]
            refine ⟨⟨?_, ?_⟩, fun r hr hrm => hco r hr (dvd_mul_of_dvd_right hrm q)⟩
            · rcases Nat.eq_zero_or_pos m with h | h
              · subst h; simp at h1
              · exact h
            · rw [Nat.le_div_iff_mul_le hq0, mul_comm]; exact h2
          calc ∑ n ∈ H.filter (q ∣ ·), (1 : ℝ) / n
              ≤ ∑ n ∈ ((Icc 1 (K / q)).filter (fun m => ∀ r ∈ s, ¬ r ∣ m)).image (q * ·), (1 : ℝ) / n :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
            _ = ∑ m ∈ (Icc 1 (K / q)).filter (fun m => ∀ r ∈ s, ¬ r ∣ m), (1 : ℝ) / ((q * m : ℕ) : ℝ) := by
                rw [Finset.sum_image]
                intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hq0 hab
            _ = _ := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
                push_cast; rw [one_div_mul_one_div]

end Palprimes
