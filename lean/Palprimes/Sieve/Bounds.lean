import Palprimes.Sieve.Combinatorics
import Palprimes.Sieve.PrimeSums

/-! # Analytic lower bounds for the Selberg sums (sieve route, M13) -/

open Finset Real

namespace Palprimes

/-- The Selberg sum `S = Σ_{l | P, l² ≤ y} 1/φ(l)` of `selberg_concrete`. -/
noncomputable def selS (Pset : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ y), (1 : ℝ) / (Nat.totient l)

/-- `β_B = Π_{q | B}(1 − 1/q)`. -/
noncomputable def betaB (B : ℕ) : ℝ := ∏ q ∈ B.primeFactors, (1 - 1 / (q : ℝ))

/-- The constant of `HB_approx` for `s = B.primeFactors`. -/
noncomputable def CsB (B : ℕ) : ℝ :=
  2 ^ (#B.primeFactors) * (2 + 2 * Real.log (∏ q ∈ B.primeFactors, q : ℕ))

theorem CsB_nonneg (B : ℕ) : 0 ≤ CsB B := by
  unfold CsB
  have : 0 ≤ Real.log (∏ q ∈ B.primeFactors, q : ℕ) := by
    apply Real.log_nonneg
    have : 1 ≤ ∏ q ∈ B.primeFactors, q :=
      Finset.one_le_prod (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_lt.le)
    exact_mod_cast this
  positivity

theorem PB_primes (B t : ℕ) : ∀ q ∈ PB B t, q.Prime := fun _ h => PB_prime h

/-- Part A of the smooth bound. -/
theorem selS_ge_A (B t K : ℕ) (hB : 1 ≤ B) (hK : 1 ≤ K) (y : ℝ) (hKy : (K : ℝ) ^ 2 ≤ y) :
    betaB B * (Real.log K - ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B),
        (1 / (q : ℝ)) * (Real.log K - Real.log q)) -
      CsB B * (1 + ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ))) ≤
      selS (PB B t) y := by
  classical
  set s := B.primeFactors
  set Q := (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B)
  have hs : ∀ q ∈ s, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hB0 : B ≠ 0 := by omega
  have hsdvd : ∀ q, q.Prime → (q ∈ s ↔ q ∣ B) := fun q hq => by
    simp only [s, Nat.mem_primeFactors]; exact ⟨fun h => h.2.1, fun h => ⟨hq, h, hB0⟩⟩
  have h1 := factored_le_selbergS (PB B t) (PB_primes B t) K y hKy
  have h2 := HB_le_factored_add s (PB B t) Q K
    (fun q hq hqK hqs => by
      by_cases hqt : q < t
      · left; simp only [PB, mem_filter, mem_range]
        exact ⟨hqt, hq, fun h => hqs ((hsdvd q hq).2 h)⟩
      · right; simp only [Q, mem_filter, mem_Icc]
        exact ⟨⟨not_lt.1 hqt, hqK⟩, hq, fun h => hqs ((hsdvd q hq).2 h)⟩)
    (fun q hq => by
      simp only [Q, mem_filter] at hq
      exact ⟨hq.2.1, fun h => hq.2.2 ((hsdvd q hq.2.1).1 h)⟩) hs
  have hA := HB_approx s hs K hK
  have hβ0 : 0 ≤ betaB B := Finset.prod_nonneg (fun q hq => by
    have : (1 : ℝ) < q := by exact_mod_cast (hs q hq).one_lt
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
    linarith)
  have hQb : ∑ q ∈ Q, (1 / (q : ℝ)) * HB s (K / q) ≤
      ∑ q ∈ Q, (1 / (q : ℝ)) * (betaB B * (Real.log K - Real.log q) + CsB B) := by
    apply Finset.sum_le_sum; intro q hq
    simp only [Q, mem_filter, mem_Icc] at hq
    have hq0 : 0 < q := hq.2.1.pos
    have hKq : 1 ≤ K / q := Nat.div_pos hq.1.2 hq0
    have hA' := HB_approx s hs (K / q) hKq
    have hlog : Real.log ((K / q : ℕ) : ℝ) ≤ Real.log K - Real.log q := by
      rw [← Real.log_div (by exact_mod_cast (by omega : K ≠ 0)) (by exact_mod_cast hq0.ne')]
      apply Real.log_le_log (by exact_mod_cast hKq)
      rw [le_div_iff₀ (by exact_mod_cast hq0)]; exact_mod_cast Nat.div_mul_le_self K q
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := (abs_le.1 hA').2
    have : betaB B * Real.log ((K / q : ℕ) : ℝ) ≤ betaB B * (Real.log K - Real.log q) :=
      mul_le_mul_of_nonneg_left hlog hβ0
    unfold betaB CsB at *
    linarith
  have hlo := (abs_le.1 hA).1
  unfold selS
  have e1 : ∑ q ∈ Q, (1 / (q : ℝ)) * (betaB B * (Real.log K - Real.log q) + CsB B) =
      betaB B * ∑ q ∈ Q, (1 / (q : ℝ)) * (Real.log K - Real.log q) + CsB B * ∑ q ∈ Q, (1 / (q : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _; ring
  unfold betaB CsB at e1 hQb ⊢
  nlinarith [h1, h2, hQb, e1, hlo]

/-- Split off the prime `t` itself. -/
theorem sum_Q_split (B t K : ℕ) (f : ℕ → ℝ) (hf0 : ∀ q, 0 ≤ f q) :
    ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), f q ≤
      f t + ∑ q ∈ (Ioc t K).filter Nat.Prime, f q := by
  classical
  have hsub : (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B) ⊆ insert t ((Ioc t K).filter Nat.Prime) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    rcases eq_or_lt_of_le hq.1.1 with h | h
    · rw [h]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.2 ⟨mem_Ioc.2 ⟨h, hq.1.2⟩, hq.2.1⟩)
  calc _ ≤ ∑ q ∈ insert t ((Ioc t K).filter Nat.Prime), f q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hf0 q)
    _ ≤ _ := by
        have ht : t ∉ (Ioc t K).filter Nat.Prime := by simp
        rw [Finset.sum_insert ht]

/-- Part B: the weighted prime sum over `[t, K]` by the inner grid. -/
theorem sum_Q_log_le (C₂ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (B t K : ℕ) (ht : 2 ≤ t) (v : ℝ) (hv : 0 ≤ v) (hK : (K : ℝ) ≤ (t : ℝ) ^ v) (hK1 : 1 ≤ K)
    (c : ℕ → ℝ) (n : ℕ) (hc0 : c 0 = 1) (hmono : Monotone c) (hvn : v ≤ c n) :
    ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ)) * (Real.log K - Real.log q) ≤
      Real.log t * (v / t + ∑ j ∈ range n, max (v - c j) 0 *
        (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))) := by
  classical
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have hlogK : Real.log K ≤ v * Real.log t := by
    rw [← Real.log_rpow (by linarith)]; exact Real.log_le_log (by exact_mod_cast hK1) hK
  set f : ℕ → ℝ := fun q => if q ≤ K ∧ 1 ≤ q then (1 / (q : ℝ)) * (Real.log K - Real.log q) else 0
  have hf0 : ∀ q, 0 ≤ f q := by
    intro q; simp only [f]; split_ifs with h
    · have : Real.log q ≤ Real.log K := Real.log_le_log (by exact_mod_cast h.2) (by exact_mod_cast h.1)
      have : (0 : ℝ) ≤ 1 / q := by positivity
      nlinarith
    · exact le_rfl
  have heq : ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ)) * (Real.log K - Real.log q) =
      ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), f q := by
    apply Finset.sum_congr rfl; intro q hq
    simp only [mem_filter, mem_Icc] at hq
    simp only [f]; rw [if_pos ⟨hq.1.2, by omega⟩]
  rw [heq]
  refine le_trans (sum_Q_split B t K f hf0) ?_
  -- the term `q = t`
  have hft : f t ≤ Real.log t * (v / t) := by
    simp only [f]; split_ifs with h
    · have : Real.log K - Real.log t ≤ v * Real.log t := by
        have := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t) : (1 : ℝ) ≤ t); linarith
      have h0 : (0 : ℝ) ≤ 1 / t := by positivity
      calc 1 / (t : ℝ) * (Real.log K - Real.log t) ≤ 1 / t * (v * Real.log t) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    · have : 0 ≤ Real.log t * (v / t) := by positivity
      exact this
  -- the primes in `(t, K]` lie in the grid range `(t^{c 0}, t^{c n}]`
  have hrange : ∑ q ∈ (Ioc t K).filter Nat.Prime, f q ≤
      ∑ q ∈ (Ioc ⌊(t : ℝ) ^ (c 0)⌋₊ ⌊(t : ℝ) ^ (c n)⌋₊).filter Nat.Prime, f q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => hf0 q)
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq ⊢
    refine ⟨⟨?_, ?_⟩, hq.2⟩
    · rw [hc0, Real.rpow_one, Nat.floor_natCast]; exact hq.1.1
    · apply Nat.le_floor
      calc (q : ℝ) ≤ K := by exact_mod_cast hq.1.2
        _ ≤ (t : ℝ) ^ v := hK
        _ ≤ (t : ℝ) ^ (c n) := Real.rpow_le_rpow_of_exponent_le ht1.le hvn
  have hgrid := prime_grid_sum C₂ hC₂ (t : ℝ) ht1 c n (by rw [hc0]; norm_num) hmono
    (by rw [hc0, Real.rpow_one]; exact_mod_cast ht) f (fun j => Real.log t * max (v - c j) 0)
    (fun j _ => by positivity)
    (fun j _ q hq hlo hhi => by
      simp only [f]; split_ifs with h
      · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
        have hlq : c j * Real.log t < Real.log q := by
          rw [← Real.log_rpow (by linarith)]
          exact Real.log_lt_log (Real.rpow_pos_of_pos (by linarith) _) hlo
        have : Real.log K - Real.log q ≤ Real.log t * max (v - c j) 0 := by
          have := le_max_left (v - c j) 0
          nlinarith
        calc 1 / (q : ℝ) * (Real.log K - Real.log q) ≤ 1 / q * (Real.log t * max (v - c j) 0) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      · have : 0 ≤ Real.log t * max (v - c j) 0 / q := by positivity
        exact this)
  have e : ∑ j ∈ range n, Real.log t * max (v - c j) 0 *
        (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t)) =
      Real.log t * ∑ j ∈ range n, max (v - c j) 0 *
        (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [mul_add]
  linarith

theorem sum_Q_inv_le (C₂ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (B t K : ℕ) (ht : 2 ≤ t) (v : ℝ) (hK : (K : ℝ) ≤ (t : ℝ) ^ v)
    (c : ℕ → ℝ) (n : ℕ) (hc0 : c 0 = 1) (hmono : Monotone c) (hvn : v ≤ c n) :
    ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ)) ≤
      1 / t + ∑ j ∈ range n, (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t)) := by
  classical
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  refine le_trans (sum_Q_split B t K (fun q => 1 / (q : ℝ)) (fun q => by positivity)) ?_
  apply add_le_add le_rfl
  have hrange : ∑ q ∈ (Ioc t K).filter Nat.Prime, (1 / (q : ℝ)) ≤
      ∑ q ∈ (Ioc ⌊(t : ℝ) ^ (c 0)⌋₊ ⌊(t : ℝ) ^ (c n)⌋₊).filter Nat.Prime, (1 / (q : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ => by positivity)
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq ⊢
    refine ⟨⟨?_, ?_⟩, hq.2⟩
    · rw [hc0, Real.rpow_one, Nat.floor_natCast]; exact hq.1.1
    · apply Nat.le_floor
      calc (q : ℝ) ≤ K := by exact_mod_cast hq.1.2
        _ ≤ (t : ℝ) ^ v := hK
        _ ≤ (t : ℝ) ^ (c n) := Real.rpow_le_rpow_of_exponent_le ht1.le hvn
  have hgrid := prime_grid_sum C₂ hC₂ (t : ℝ) ht1 c n (by rw [hc0]; norm_num) hmono
    (by rw [hc0, Real.rpow_one]; exact_mod_cast ht) (fun q => 1 / (q : ℝ)) (fun _ => 1)
    (fun j _ => by norm_num) (fun j _ q _ _ _ => le_rfl)
  simp only [one_mul] at hgrid
  linarith

/-- `V(t) β_B` is the full Mertens product over primes `≤ t − 1` (for `t > B`). -/
theorem prod_PB_mul_beta (B t : ℕ) (hB : 1 ≤ B) (hBt : B < t) :
    (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * betaB B =
      ∏ p ∈ (Icc 1 ⌊(t : ℝ) - 1⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  classical
  have hfl : ⌊(t : ℝ) - 1⌋₊ = t - 1 := by
    rw [show (t : ℝ) - 1 = ((t - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; simp, Nat.floor_natCast]
  rw [hfl]
  have hdisj : Disjoint (PB B t) B.primeFactors := by
    rw [Finset.disjoint_left]; intro q hq hqB
    simp only [PB, mem_filter] at hq
    exact hq.2.2 (Nat.dvd_of_mem_primeFactors hqB)
  have hunion : PB B t ∪ B.primeFactors = (Icc 1 (t - 1)).filter Nat.Prime := by
    ext q
    simp only [PB, mem_union, mem_filter, mem_range, mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
      · exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
      · have := Nat.le_of_dvd (by omega) h2
        exact ⟨⟨h1.one_lt.le, by omega⟩, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hqB : q ∣ B
      · right; exact ⟨h3, hqB, by omega⟩
      · left; exact ⟨by omega, h3, hqB⟩
  unfold betaB
  rw [← Finset.prod_union hdisj, hunion]

theorem betaB_pos (B : ℕ) : 0 < betaB B := Finset.prod_pos (fun q hq => by
  have : (1 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt
  have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
  linarith)

theorem floor_ge_half (a : ℝ) (ha : 1 ≤ a) : a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one a
  have h2 : (1 : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast ha)
  linarith

/-- **Smooth bound, explicit form.** -/
theorem smooth_explicit (C₂ C₃ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B t : ℕ) (hB : 1 ≤ B) (hBt : B < t) (ht3 : 3 ≤ t) (hlt1 : 1 ≤ Real.log ((t : ℝ) - 1))
    (v : ℝ) (hv : 0 ≤ v) (y : ℝ) (hy : ((t : ℝ) ^ v) ^ 2 ≤ y)
    (c : ℕ → ℝ) (n : ℕ) (hc0 : c 0 = 1) (hmono : Monotone c) (hvn : v ≤ c n)
    (hX : 0 ≤ v - Real.log 2 / Real.log t - v / t - ∑ j ∈ range n, max (v - c j) 0 *
        (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))) :
    (Real.exp (-Real.eulerMascheroniConstant) - C₃ / Real.log ((t : ℝ) - 1)) *
        (v - Real.log 2 / Real.log t - v / t - ∑ j ∈ range n, max (v - c j) 0 *
          (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))) -
      (1 + |C₃|) * CsB B * (1 + 1 / t + ∑ j ∈ range n, (Real.log (c (j + 1) / c j) +
          C₂ / (c j * Real.log t))) / (betaB B * Real.log ((t : ℝ) - 1)) ≤
      (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y := by
  classical
  set X := v - Real.log 2 / Real.log t - v / t - ∑ j ∈ range n, max (v - c j) 0 *
      (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))
  set Y := 1 + 1 / (t : ℝ) + ∑ j ∈ range n, (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))
  set V := ∏ q ∈ PB B t, (1 - 1 / (q : ℝ))
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have htv : (1 : ℝ) ≤ (t : ℝ) ^ v := Real.one_le_rpow ht1.le hv
  set K := ⌊(t : ℝ) ^ v⌋₊
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast htv)
  have hKle : (K : ℝ) ≤ (t : ℝ) ^ v := Nat.floor_le (by linarith)
  have hKy : (K : ℝ) ^ 2 ≤ y := le_trans (pow_le_pow_left₀ (by positivity) hKle 2) hy
  have hA := selS_ge_A B t K hB hK1 y hKy
  have hB1 := sum_Q_log_le C₂ hC₂ B t K (by omega) v hv hKle hK1 c n hc0 hmono hvn
  have hB2 := sum_Q_inv_le C₂ hC₂ B t K (by omega) v hKle c n hc0 hmono hvn
  have hlogK : v * Real.log t - Real.log 2 ≤ Real.log K := by
    have h := floor_ge_half _ htv
    have h' : Real.log ((t : ℝ) ^ v / 2) ≤ Real.log K := Real.log_le_log (by positivity) h
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by linarith)] at h'
    exact h'
  have hβ := betaB_pos B
  have hCs := CsB_nonneg B
  -- `selS ≥ β log t X − Cs Y`
  have hS : betaB B * Real.log t * X - CsB B * Y ≤ selS (PB B t) y := by
    refine le_trans ?_ hA
    have h1 : Real.log t * X ≤ Real.log K - ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B),
        (1 / (q : ℝ)) * (Real.log K - Real.log q) := by
      have e : Real.log t * X = v * Real.log t - Real.log 2 - Real.log t * (v / t + ∑ j ∈ range n,
          max (v - c j) 0 * (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))) := by
        simp only [X]; field_simp; ring
      rw [e]; linarith
    have h2 : CsB B * (1 + ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ))) ≤
        CsB B * Y := by
      apply mul_le_mul_of_nonneg_left _ hCs; simp only [Y]; linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hβ.le
    linarith
  -- Mertens 3 at `t − 1`
  have hM := hC₃ ((t : ℝ) - 1) (by
    have : (3 : ℝ) ≤ t := by exact_mod_cast ht3
    linarith)
  rw [← prod_PB_mul_beta B t hB hBt] at hM
  have hlt1' : 0 < Real.log ((t : ℝ) - 1) := by linarith
  have hlogle : Real.log ((t : ℝ) - 1) ≤ Real.log t :=
    Real.log_le_log (by linarith [(by exact_mod_cast ht3 : (3 : ℝ) ≤ t)]) (by linarith)
  have hV0 : 0 ≤ V := Finset.prod_nonneg (fun q hq => by
    have : (1 : ℝ) < q := by exact_mod_cast (PB_prime hq).one_lt
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
    linarith)
  have hlow : Real.exp (-Real.eulerMascheroniConstant) - C₃ / Real.log ((t : ℝ) - 1) ≤
      V * betaB B * Real.log t := by
    have h := (abs_le.1 hM).1
    have : V * betaB B * Real.log ((t : ℝ) - 1) ≤ V * betaB B * Real.log t :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    linarith
  have hup : V * betaB B * Real.log ((t : ℝ) - 1) ≤ 1 + |C₃| := by
    have h := (abs_le.1 hM).2
    have h1 : Real.exp (-Real.eulerMascheroniConstant) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    have h2 : C₃ / Real.log ((t : ℝ) - 1) ≤ |C₃| := by
      rw [div_le_iff₀ hlt1']; nlinarith [le_abs_self C₃, abs_nonneg C₃]
    linarith
  have hY0 : 0 ≤ Y := by
    have h0 : (0:ℝ) ≤ ∑ q ∈ (Icc t K).filter (fun q => q.Prime ∧ ¬ q ∣ B), (1 / (q : ℝ)) :=
      Finset.sum_nonneg (fun q _ => by positivity)
    simp only [Y]; linarith [hB2]
  -- combine
  have hmain : (Real.exp (-Real.eulerMascheroniConstant) - C₃ / Real.log ((t : ℝ) - 1)) * X ≤
      V * (betaB B * Real.log t * X) := by
    have := mul_le_mul_of_nonneg_right hlow hX
    linarith
  have herr : V * (CsB B * Y) ≤ (1 + |C₃|) * CsB B * Y / (betaB B * Real.log ((t : ℝ) - 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hup (mul_nonneg hCs hY0)
    nlinarith
  have := mul_le_mul_of_nonneg_left hS hV0
  nlinarith

/-- **Rankin, explicit form** with `a = log k`. -/
theorem rankin_explicit (c₁ : ℝ)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (B t k : ℕ) (ht : 2 ≤ t) (hk : 2 ≤ k) (v : ℝ) (hv : 0 ≤ v) (y : ℝ) (hy : ((t : ℝ) ^ v) ^ 2 ≤ y) :
    1 - (k : ℝ) ^ (-v) * Real.exp (((k : ℝ) - 1) * (1 + c₁ / Real.log t)) ≤
      (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y := by
  classical
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (by omega : 1 < t)
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlk : 0 < Real.log k := Real.log_pos hk1
  have htv : 0 < (t : ℝ) ^ v := Real.rpow_pos_of_pos (by linarith) _
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hR := rankin_rel (PB B t) (PB_primes B t) (t : ℝ) (Real.log k) y ht1
    (fun q hq => by
      simp only [PB, mem_filter, mem_range] at hq; exact_mod_cast hq.1.le) hlk.le hy0
  rw [Real.exp_log (by linarith)] at hR
  set V := ∏ q ∈ PB B t, (1 - 1 / (q : ℝ))
  have hq1 : ∀ q ∈ PB B t, (1 : ℝ) < q := fun q hq => by exact_mod_cast (PB_prime hq).one_lt
  have hVinv : V * ∏ q ∈ PB B t, (1 + 1 / ((q : ℝ) - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one; intro q hq
    have := hq1 q hq
    have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (q : ℝ) ≠ 0 := by linarith
    field_simp; ring
  have hV0 : 0 ≤ V := Finset.prod_nonneg (fun q hq => by
    have := hq1 q hq
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith)
  -- the Rankin factor
  have hpow : y ^ (-(Real.log k / Real.log t / 2)) ≤ (k : ℝ) ^ (-v) := by
    have h1 : y ^ (-(Real.log k / Real.log t / 2)) ≤ (((t : ℝ) ^ v) ^ 2) ^ (-(Real.log k / Real.log t / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy (by
        have : 0 ≤ Real.log k / Real.log t / 2 := by positivity
        linarith)
    have h2 : (((t : ℝ) ^ v) ^ 2) ^ (-(Real.log k / Real.log t / 2)) = (k : ℝ) ^ (-v) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by
        exact Real.rpow_pos_of_pos (by linarith) _))
      rw [Real.log_rpow (by positivity), Real.log_pow, Real.log_rpow (by linarith),
        Real.log_rpow (by linarith)]
      field_simp; push_cast; ring
    linarith
  have hsum : ∑ q ∈ PB B t, Real.log q / q ≤ Real.log t + c₁ := by
    refine le_trans ?_ (hc₁ t ht1.le)
    rw [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [PB, mem_filter, mem_range] at hq
      simp only [mem_filter, mem_Icc]
      exact ⟨⟨hq.2.1.one_lt.le, hq.1.le⟩, hq.2.1⟩
    · intro q hq _
      simp only [mem_filter, mem_Icc] at hq
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq.1.1
      have := Real.log_nonneg this
      positivity
  have hexp : Real.exp (((k : ℝ) - 1) / Real.log t * ∑ q ∈ PB B t, Real.log q / q) ≤
      Real.exp (((k : ℝ) - 1) * (1 + c₁ / Real.log t)) := by
    apply Real.exp_le_exp.2
    have : ((k : ℝ) - 1) * (1 + c₁ / Real.log t) = ((k : ℝ) - 1) / Real.log t * (Real.log t + c₁) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hsum (by
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity)
  have hτ : y ^ (-(Real.log k / Real.log t / 2)) *
        Real.exp (((k : ℝ) - 1) / Real.log t * ∑ q ∈ PB B t, Real.log q / q) ≤
      (k : ℝ) ^ (-v) * Real.exp (((k : ℝ) - 1) * (1 + c₁ / Real.log t)) :=
    mul_le_mul hpow hexp (Real.exp_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have := mul_le_mul_of_nonneg_left hR hV0
  unfold selS
  rw [← mul_assoc, hVinv, one_mul] at this
  linarith

/-- The limit value `g_K(v) = v − Σ_j (v − c_j)⁺ log(c_{j+1}/c_j)` of the smooth bound. -/
noncomputable def gKc (c : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  v - ∑ j ∈ range n, max (v - c j) 0 * Real.log (c (j + 1) / c j)

theorem tendsto_inv_log_nat : Filter.Tendsto (fun t : ℕ => (Real.log t)⁻¹) Filter.atTop (nhds 0) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop

theorem tendsto_inv_log_nat_sub : Filter.Tendsto (fun t : ℕ => (Real.log ((t : ℝ) - 1))⁻¹)
    Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun t : ℕ => (t : ℝ) - 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop |>.congr (fun t => by ring)
  exact (Real.tendsto_log_atTop.comp h).inv_tendsto_atTop

theorem tendsto_inv_nat : Filter.Tendsto (fun t : ℕ => ((t : ℝ))⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- **Smooth bound, eventual form**: for every `g < g_K(v)` and `θ < 1`, eventually in `t`,
`V(t) S(t, y) ≥ θ e^{−γ} g` for all `y ≥ t^{2v}`. -/
theorem smooth_eventually (C₂ C₃ : ℝ)
    (hC₂ : ∀ a t : ℝ, 2 ≤ a → a ≤ t →
      |∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, (1 : ℝ) / p -
        (Real.log (Real.log t) - Real.log (Real.log a))| ≤ C₂ / Real.log a)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (v g θ : ℝ) (hv : 0 ≤ v) (hg : 0 < g) (hθ : θ < 1)
    (c : ℕ → ℝ) (n : ℕ) (hc0 : c 0 = 1) (hmono : Monotone c) (hvn : v ≤ c n)
    (hgK : g < gKc c n v) :
    ∀ᶠ t : ℕ in Filter.atTop, ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      θ * Real.exp (-Real.eulerMascheroniConstant) * g ≤
        (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y := by
  set e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  set G := gKc c n v
  -- the error terms as functions of `t`
  set ε₁ : ℕ → ℝ := fun t => Real.log 2 * (Real.log t)⁻¹ + v * ((t : ℝ))⁻¹ +
    ∑ j ∈ range n, max (v - c j) 0 * (C₂ / c j) * (Real.log t)⁻¹
  set Xf : ℕ → ℝ := fun t => v - Real.log 2 / Real.log t - v / t - ∑ j ∈ range n, max (v - c j) 0 *
      (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t))
  have hXf : ∀ t, Xf t = G - ε₁ t := by
    intro t; simp only [Xf, G, gKc, ε₁]
    rw [show ∑ j ∈ range n, max (v - c j) 0 * (Real.log (c (j + 1) / c j) + C₂ / (c j * Real.log t)) =
        ∑ j ∈ range n, max (v - c j) 0 * Real.log (c (j + 1) / c j) +
        ∑ j ∈ range n, max (v - c j) 0 * (C₂ / c j) * (Real.log t)⁻¹ by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
      rw [div_mul_eq_div_div, div_eq_mul_inv (C₂ / c j)]; ring]
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hε₁ : Filter.Tendsto ε₁ Filter.atTop (nhds 0) := by
    have h1 := tendsto_inv_log_nat
    have h2 := tendsto_inv_nat
    have : Filter.Tendsto ε₁ Filter.atTop (nhds (Real.log 2 * 0 + v * 0 +
        ∑ j ∈ range n, max (v - c j) 0 * (C₂ / c j) * 0)) := by
      apply Filter.Tendsto.add (Filter.Tendsto.add (h1.const_mul _) (h2.const_mul _))
      exact tendsto_finsetSum _ (fun j _ => h1.const_mul _)
    simpa using this
  set Yf : ℕ → ℝ := fun t => 1 + 1 / (t : ℝ) + ∑ j ∈ range n, (Real.log (c (j + 1) / c j) +
      C₂ / (c j * Real.log t))
  set Y0 := 1 + ∑ j ∈ range n, Real.log (c (j + 1) / c j)
  have hYf : Filter.Tendsto Yf Filter.atTop (nhds Y0) := by
    have h1 := tendsto_inv_log_nat
    have h2 := tendsto_inv_nat
    have e1 : ∀ t : ℕ, Yf t = (1 + ((t : ℝ))⁻¹ + ∑ j ∈ range n, Real.log (c (j + 1) / c j)) +
        ∑ j ∈ range n, (C₂ / c j) * (Real.log t)⁻¹ := by
      intro t; simp only [Yf]; rw [one_div, Finset.sum_add_distrib]
      have : ∑ j ∈ range n, C₂ / (c j * Real.log t) = ∑ j ∈ range n, (C₂ / c j) * (Real.log t)⁻¹ := by
        apply Finset.sum_congr rfl; intro j _; rw [div_mul_eq_div_div, div_eq_mul_inv (C₂ / c j)]
      rw [this]; ring
    have : Filter.Tendsto Yf Filter.atTop (nhds ((1 + 0 + ∑ j ∈ range n, Real.log (c (j + 1) / c j)) +
        ∑ j ∈ range n, (C₂ / c j) * 0)) := by
      rw [show Yf = fun t => _ from funext e1]
      exact ((tendsto_const_nhds.add h2).add tendsto_const_nhds).add
        (tendsto_finsetSum _ (fun j _ => h1.const_mul _))
    simpa [Y0] using this
  -- the explicit right-hand side tends to `e G`
  set Rf : ℕ → ℝ := fun t => (e - C₃ * (Real.log ((t : ℝ) - 1))⁻¹) * (G - ε₁ t) -
      (1 + |C₃|) * CsB B / betaB B * Yf t * (Real.log ((t : ℝ) - 1))⁻¹
  have hRf : Filter.Tendsto Rf Filter.atTop (nhds ((e - C₃ * 0) * (G - 0) -
      (1 + |C₃|) * CsB B / betaB B * Y0 * 0)) := by
    have h3 := tendsto_inv_log_nat_sub
    exact ((tendsto_const_nhds.sub (h3.const_mul _)).mul (tendsto_const_nhds.sub hε₁)).sub
      ((hYf.const_mul _).mul h3)
  simp only [mul_zero, sub_zero] at hRf
  have hlim : θ * e * g < e * G := by
    have : θ * g < G := by
      rcases le_or_gt θ 0 with h | h
      · nlinarith [hg, lt_trans hg hgK]
      · nlinarith
    nlinarith
  have hev1 := hRf.eventually (lt_mem_nhds hlim)
  have hev2 := (hε₁.const_sub G).eventually (lt_mem_nhds (by rw [sub_zero]; exact lt_trans hg hgK : (0 : ℝ) < G - 0))
  have hev3 : ∀ᶠ t : ℕ in Filter.atTop, B < t ∧ 3 ≤ t ∧ 1 ≤ Real.log ((t : ℝ) - 1) := by
    have hl : Filter.Tendsto (fun t : ℕ => Real.log ((t : ℝ) - 1)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp
        (Filter.tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop |>.congr (fun t => by ring))
    filter_upwards [Filter.eventually_gt_atTop B, Filter.eventually_ge_atTop 3,
      hl.eventually (Filter.eventually_ge_atTop 1)] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hev1, hev2, hev3] with t h1 h2 h3 y hy
  obtain ⟨hBt, ht3, hlt1⟩ := h3
  have hX : 0 ≤ Xf t := by rw [hXf]; linarith
  have hS := smooth_explicit C₂ C₃ hC₂ hC₃ B t hB hBt ht3 hlt1 v hv y hy c n hc0 hmono hvn hX
  have e1 : (e - C₃ / Real.log ((t : ℝ) - 1)) * Xf t -
      (1 + |C₃|) * CsB B * Yf t / (betaB B * Real.log ((t : ℝ) - 1)) = Rf t := by
    simp only [Rf]; rw [← hXf]
    have := betaB_pos B
    have : 0 < Real.log ((t : ℝ) - 1) := by linarith
    field_simp
  simp only [Xf, Yf] at e1
  rw [e1] at hS
  linarith

theorem rankin_eventually (c₁ : ℝ)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (B k : ℕ) (hk : 2 ≤ k) (v η : ℝ) (hv : 0 ≤ v) (hη : 0 < η) :
    ∀ᶠ t : ℕ in Filter.atTop, ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      1 - (k : ℝ) ^ (-v) * Real.exp (((k : ℝ) - 1) * (1 + η)) ≤
        (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y := by
  have h1 := (tendsto_inv_log_nat.const_mul c₁).eventually (gt_mem_nhds (by simpa using hη : c₁ * 0 < η))
  filter_upwards [h1, Filter.eventually_ge_atTop 2] with t h1 ht y hy
  refine le_trans ?_ (rankin_explicit c₁ hc₁ B t k ht hk v hv y hy)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have : Real.exp (((k : ℝ) - 1) * (1 + c₁ / Real.log t)) ≤ Real.exp (((k : ℝ) - 1) * (1 + η)) := by
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hk1
    rw [div_eq_mul_inv]; linarith
  have h0 : 0 ≤ (k : ℝ) ^ (-v) := Real.rpow_nonneg (by positivity) _
  nlinarith

/-- Two-sided Mertens 3 for `V(t) β_B`. -/
theorem mertens_two_sided (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ < 1) :
    ∀ᶠ t : ℕ in Filter.atTop,
      θ * Real.exp (-Real.eulerMascheroniConstant) ≤
          (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * betaB B * Real.log ((t : ℝ) - 1) ∧
      (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * betaB B * Real.log ((t : ℝ) - 1) ≤
          Real.exp (-Real.eulerMascheroniConstant) / θ := by
  set e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  have hgap1 : 0 < (1 - θ) * e := by nlinarith
  have hgap2 : 0 < e / θ - e := by
    rw [div_sub' hθ0.ne', lt_div_iff₀ hθ0]; nlinarith
  have h1 := (tendsto_inv_log_nat_sub.const_mul |C₃|).eventually
    (gt_mem_nhds (by simpa using lt_min hgap1 hgap2 : |C₃| * 0 < min ((1 - θ) * e) (e / θ - e)))
  filter_upwards [h1, Filter.eventually_gt_atTop B, Filter.eventually_ge_atTop 3] with t h1 hBt ht3
  have hM := hC₃ ((t : ℝ) - 1) (by
    have : (3 : ℝ) ≤ t := by exact_mod_cast ht3
    linarith)
  rw [← prod_PB_mul_beta B t hB hBt] at hM
  have hl : 0 < Real.log ((t : ℝ) - 1) := Real.log_pos (by
    have : (3 : ℝ) ≤ t := by exact_mod_cast ht3
    linarith)
  have hC : C₃ / Real.log ((t : ℝ) - 1) ≤ |C₃| * (Real.log ((t : ℝ) - 1))⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hm1 := min_le_left ((1 - θ) * e) (e / θ - e)
  have hm2 := min_le_right ((1 - θ) * e) (e / θ - e)
  have := abs_le.1 hM
  constructor <;> nlinarith

theorem V_PB_pos (B t : ℕ) : 0 < ∏ q ∈ PB B t, (1 - 1 / (q : ℝ)) := Finset.prod_pos (fun q hq => by
  have : (1 : ℝ) < q := by exact_mod_cast (PB_prime hq).one_lt
  have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
  linarith)

/-- `V · S ≤ 1`: the truncated Selberg sum is at most the full Euler product. -/
theorem V_mul_selS_le_one (B t : ℕ) (y : ℝ) :
    (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y ≤ 1 := by
  classical
  have hfull := sum_rpow_div_totient (PB B t) (PB_primes B t) 0
  simp only [Real.rpow_zero] at hfull
  have hle : selS (PB B t) y ≤ ∏ q ∈ PB B t, (1 + 1 / ((q : ℝ) - 1)) := by
    rw [← hfull]; unfold selS
    exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun l _ _ => by positivity)
  have hq1 : ∀ q ∈ PB B t, (1 : ℝ) < q := fun q hq => by exact_mod_cast (PB_prime hq).one_lt
  have hVinv : (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * ∏ q ∈ PB B t, (1 + 1 / ((q : ℝ) - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one; intro q hq
    have := hq1 q hq
    have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (q : ℝ) ≠ 0 := by linarith
    field_simp; ring
  have := mul_le_mul_of_nonneg_left hle (V_PB_pos B t).le
  linarith

/-- `S ≥ 1` (the term `l = 1`). -/
theorem one_le_selS (Pset : Finset ℕ) (hP : ∀ p ∈ Pset, p.Prime) (y : ℝ) (hy : 1 ≤ y) :
    1 ≤ selS Pset y := by
  classical
  unfold selS
  have h1 : 1 ∈ (∏ p ∈ Pset, p).divisors.filter (fun l : ℕ => ((l : ℕ) : ℝ) ^ 2 ≤ y) := by
    simp only [mem_filter, Nat.mem_divisors, Nat.cast_one, one_pow]
    exact ⟨⟨one_dvd _, (SelbergPort.prod_primes_squarefree Pset hP).ne_zero⟩, hy⟩
  calc (1 : ℝ) = 1 / (Nat.totient 1) := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun l : ℕ => (1 : ℝ) / (Nat.totient l))
        (fun l _ => by positivity) h1

/-- Rankin, eventually in `t` and uniformly in `k`, `v`. -/
theorem rankin_unif (c₁ : ℝ)
    (hc₁ : ∀ t : ℝ, 1 ≤ t → ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log t + c₁)
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ t : ℕ in Filter.atTop, ∀ k : ℕ, 2 ≤ k → ∀ v : ℝ, 0 ≤ v → ∀ y : ℝ, ((t : ℝ) ^ v) ^ 2 ≤ y →
      1 - (k : ℝ) ^ (-v) * Real.exp (((k : ℝ) - 1) * (1 + η)) ≤
        (∏ q ∈ PB B t, (1 - 1 / (q : ℝ))) * selS (PB B t) y := by
  have h1 := (tendsto_inv_log_nat.const_mul c₁).eventually (gt_mem_nhds (by simpa using hη : c₁ * 0 < η))
  filter_upwards [h1, Filter.eventually_ge_atTop 2] with t h1 ht k hk v hv y hy
  refine le_trans ?_ (rankin_explicit c₁ hc₁ B t k ht hk v hv y hy)
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have : Real.exp (((k : ℝ) - 1) * (1 + c₁ / Real.log t)) ≤ Real.exp (((k : ℝ) - 1) * (1 + η)) := by
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hk1
    rw [div_eq_mul_inv]; linarith
  have h0 : 0 ≤ (k : ℝ) ^ (-v) := Real.rpow_nonneg (by positivity) _
  nlinarith

end Palprimes
