import KappaOmega2.Statements

/-!
# M09: Greaves' Lemma 10 (exact identity, even `ν(n)`, `p < y`)

Proof. Put `q = p(n)`, `L = y/(pn)`.
* `n = 1`: the only divisor is `1`, `q(1) = 1 < y/p` since `p < y`, and `χ(1) = 1`.
* `nq < y/p` (i.e. `q < L`): write `n = q n'`. Toggling `q` in `d` does not change the condition `q(n/d) < L`
  (since `q < L`), and `μ(qd) = −μ(d)`, so `b(n) = Σ_{d ∣ n', q(n'/d) < L} μ(d)(χ(d) − χ(qd))`.
  For `d ≠ n'` some prime factor of `n'/d` exceeds `q`, so every `h ∣ qd` with `q ∣ h` has
  `h p(h)² ≤ qd q² < nq < y`, hence `χ(qd) = χ(d)`. Only `d = n'` remains: `μ(n') = −1` (`ω(n')` odd),
  giving `χ(n) − χ(n/q) = −χ̄(n)`.
* `nq ≥ y/p`: every prime of `n` is `≥ q ≥ L`, so only `d = n` passes the filter, and `χ(n) = 0` because
  `h = n` (even `ω`) has `n q² > n q p ≥ y`.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

namespace M09

theorem chiProp_of_dvd {y m : ℝ} {d e : ℕ} (he : e ∣ d) (hd : d ≠ 0) (h : chiProp y m d) :
    chiProp y m e := by
  intro k hk hk1 hc
  exact h k (Nat.mem_divisors.2 ⟨(Nat.mem_divisors.1 hk).1.trans he, hd⟩) hk1 hc

theorem qmax_one : qmax 1 = 1 := by simp [qmax]

theorem qmax_prime_mul {q k : ℕ} (hq : q.Prime) (hk : k ≠ 0) : qmax (q * k) = max q (qmax k) := by
  unfold qmax
  rw [Nat.primeFactors_mul hq.ne_zero hk, Finset.sup_union, hq.primeFactors, Finset.sup_singleton]
  simp only [id]
  rw [sup_assoc]

theorem minFac_le_qmax {k : ℕ} (hk1 : k ≠ 1) (hk0 : k ≠ 0) : k.minFac ≤ qmax k := by
  unfold qmax
  exact le_sup_of_le_left (Finset.le_sup (f := id)
    (Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hk1, Nat.minFac_dvd k, hk0⟩))

theorem chi_one (y m : ℝ) : chi y m 1 = 1 := by
  unfold chi
  rw [if_pos]
  intro h hh h1
  simp only [Nat.divisors_one, Finset.mem_singleton] at hh
  exact absurd hh h1

end M09

open M09

theorem itemM09 : ItemM09 := by
  intro y m p n hm hy hp hpy hn hpq hqy hev
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hn0 : n ≠ 0 := hn.ne_zero
  by_cases h1 : n = 1
  · subst h1
    rw [if_pos rfl]
    unfold bfun
    rw [Nat.divisors_one, Finset.filter_singleton, if_pos, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one, chi_one]
    · norm_num
    · rw [Nat.div_one, qmax_one, Nat.cast_one, mul_one]
      exact (one_lt_div hp0).2 hpy
  rw [if_neg h1]
  set q := n.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime h1
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hpq' : p < q := hpq q (Nat.mem_primeFactors.2 ⟨hq, hqn, hn0⟩)
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq'
  have hqmin : ∀ r : ℕ, r.Prime → r ∣ n → q ≤ r := fun r hr hrn => Nat.minFac_le_of_dvd hr.two_le hrn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hypos : 0 < y / p := div_pos hy hp0
  have hkey : ((n : ℝ) * q < y / p) ↔ ((q : ℝ) < y / (p * n)) := by
    rw [lt_div_iff₀ hp0, lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have hyp : y / p ≤ y := div_le_self hy.le hp1
  split_ifs with hc
  · -- main case `n q < y/p`
    have hqL : (q : ℝ) < y / (p * n) := hkey.1 hc
    obtain ⟨n', hn'⟩ := hqn
    have hn'0 : n' ≠ 0 := by rintro rfl; simp at hn'; exact hn0 hn'
    have hqn' : ¬ q ∣ n' := by
      intro hd
      have : q * q ∣ n := by rw [hn']; exact Nat.mul_dvd_mul_left q hd
      exact hq.one_lt.ne' (Nat.isUnit_iff.1 (hn q this))
    have hcop : Nat.Coprime q n' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqn'
    have hL1 : (1 : ℝ) < y / (p * n) := lt_of_le_of_lt (by exact_mod_cast hq.one_lt.le) hqL
    -- split the divisor sum along `n = q n'`
    have hsplit : ∀ F : ℕ → ℝ, ∑ d ∈ n.divisors, F d = ∑ d ∈ n'.divisors, (F d + F (q * d)) := by
      intro F
      rw [hn', Nat.Coprime.divisors_mul hcop, Finset.sum_map]
      trans ∑ x ∈ q.divisors ×ˢ n'.divisors, F (x.1 * x.2)
      · exact Finset.sum_attach (q.divisors ×ˢ n'.divisors) (fun x => F (x.1 * x.2))
      rw [Finset.sum_product, hq.divisors, Finset.sum_pair hq.one_lt.ne, ← Finset.sum_add_distrib]
      simp only [one_mul]
    unfold bfun
    rw [Finset.sum_filter, hsplit]
    -- `μ(n') = −1`
    have hsqn' : Squarefree n' := Squarefree.of_mul_right (hn' ▸ hn)
    have hωn : ω n = 1 + ω n' := by
      rw [hn', ArithmeticFunction.cardDistinctFactors_mul hcop,
        ArithmeticFunction.cardDistinctFactors_apply_prime hq]
    have hodd : Odd (ω n') := by
      rw [hωn, add_comm, Nat.even_add_one] at hev
      exact Nat.not_even_iff_odd.1 hev
    have hμn' : (μ n' : ℝ) = -1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsqn',
        ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn'0).2 hsqn', hodd.neg_one_pow]
      norm_num
    have hnq : n / q = n' := by rw [hn']; exact Nat.mul_div_cancel_left n' hq.pos
    have hchibar : chibar y m n = chi y m n' - chi y m n := by
      unfold chibar; rw [if_neg h1, ← hqdef, hnq]
    rw [hchibar]
    rw [Finset.sum_eq_single_of_mem n' (Nat.mem_divisors_self n' hn'0)]
    · -- the term `d = n'`
      have h1' : (qmax (n / n') : ℝ) < y / (p * n) := by
        have hnn : n / n' = q := by rw [hn']; exact Nat.mul_div_cancel q (Nat.pos_of_ne_zero hn'0)
        have hqq : qmax q = q := by
          unfold qmax; rw [hq.primeFactors, Finset.sup_singleton]; exact max_eq_left hq.one_lt.le
        rw [hnn, hqq]; exact hqL
      have h2' : (qmax (n / (q * n')) : ℝ) < y / (p * n) := by
        rw [← hn', Nat.div_self (Nat.pos_of_ne_zero hn0), qmax_one, Nat.cast_one]; exact hL1
      have hμn : (μ (q * n') : ℝ) = 1 := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
          ArithmeticFunction.moebius_apply_prime hq]
        push_cast; rw [hμn']; norm_num
      rw [if_pos h1', if_pos h2', hμn, hμn', ← hn']
      ring
    · -- the other terms vanish
      intro d hd hdn
      have hdn' : d ∣ n' := Nat.dvd_of_mem_divisors hd
      obtain ⟨k, hk⟩ := hdn'
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hn'0 hk
      have hd0 : d ≠ 0 := by rintro rfl; simp at hk; exact hn'0 hk
      have hk1 : k ≠ 1 := by rintro rfl; exact hdn (by rw [hk, mul_one])
      -- `n/d = q k`, `n/(q d) = k`
      have hnd : n / d = q * k := by
        rw [hn', hk, show q * (d * k) = d * (q * k) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
      have hnqd : n / (q * d) = k := by
        rw [hn', hk, ← mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (mul_ne_zero hq.ne_zero hd0))]
      have hcond : ((qmax (n / d) : ℝ) < y / (p * n)) ↔ ((qmax (n / (q * d)) : ℝ) < y / (p * n)) := by
        rw [hnd, hnqd, qmax_prime_mul hq hk0, Nat.cast_max]
        exact ⟨fun h => (max_lt_iff.1 h).2, fun h => max_lt hqL h⟩
      -- `χ(q d) = χ(d)`
      have hqk : q < k := by
        have hkn : k ∣ n := by rw [hn', hk]; exact Dvd.intro_left (q * d) (by ring)
        have h2 : q ≤ k.minFac := hqmin _ (Nat.minFac_prime hk1) ((Nat.minFac_dvd k).trans hkn)
        have h3 : k.minFac ≠ q := by
          intro he
          apply hqn'
          rw [hk, ← he]; exact Dvd.dvd.mul_left (Nat.minFac_dvd k) d
        exact lt_of_lt_of_le (lt_of_le_of_ne h2 (Ne.symm h3)) (Nat.minFac_le (Nat.pos_of_ne_zero hk0))
      have hchi : chi y m (q * d) = chi y m d := by
        unfold chi
        have : chiProp y m (q * d) ↔ chiProp y m d := by
          constructor
          · exact chiProp_of_dvd (Dvd.intro_left q rfl) (mul_ne_zero hq.ne_zero hd0)
          · intro hcd h hh hh1 hc'
            have hhd : h ∣ q * d := Nat.dvd_of_mem_divisors hh
            by_cases hqh : q ∣ h
            · have hmf : h.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqh
              have hle : h ≤ q * d := Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hq.ne_zero hd0)) hhd
              have hN : h * h.minFac ^ 2 < n * q := by
                have e1 : h * h.minFac ^ 2 ≤ (q * d) * q ^ 2 :=
                  Nat.mul_le_mul hle (Nat.pow_le_pow_left hmf 2)
                have e2 : (q * d) * q ^ 2 < n * q := by
                  rw [hn', hk]
                  have : (q * d) * q ^ 2 = (q * d * q) * q := by ring
                  rw [this, show q * (d * k) * q = (q * d * q) * k by ring]
                  exact Nat.mul_lt_mul_of_pos_left hqk
                    (Nat.mul_pos (Nat.mul_pos hq.pos (Nat.pos_of_ne_zero hd0)) hq.pos)
                omega
              have hN' : (h : ℝ) * (h.minFac : ℝ) ^ 2 < (n : ℝ) * q := by exact_mod_cast hN
              linarith
            · have hcop' : Nat.Coprime h q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqh).symm
              have hhd' : h ∣ d := hcop'.dvd_of_dvd_mul_left hhd
              exact hcd h (Nat.mem_divisors.2 ⟨hhd', hd0⟩) hh1 hc'
        split_ifs with e1 e2 e2
        · rfl
        · exact absurd (this.1 e1) e2
        · exact absurd (this.2 e2) e1
        · rfl
      have hμ : (μ (q * d) : ℝ) = -μ d := by
        have hcd : Nat.Coprime q d := Nat.Coprime.coprime_dvd_right (Dvd.intro k hk.symm) hcop
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcd,
          ArithmeticFunction.moebius_apply_prime hq]
        push_cast; ring
      by_cases hc1 : (qmax (n / d) : ℝ) < y / (p * n)
      · rw [if_pos hc1, if_pos (hcond.1 hc1), hμ, hchi]; ring
      · rw [if_neg hc1, if_neg (fun h => hc1 (hcond.2 h))]; ring
  · -- `n q ≥ y/p`: the sum vanishes
    have hqL : ¬ (q : ℝ) < y / (p * n) := fun h => hc (hkey.2 h)
    unfold bfun
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdn, hlt⟩ := hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdn
    have hdeq : d = n := by
      by_contra hne
      have hk0 : n / d ≠ 0 := by
        intro h0
        exact hn0 (by rw [← Nat.mul_div_cancel' hdvd, h0, mul_zero])
      have hk1 : n / d ≠ 1 := by
        intro h0
        exact hne (by have := Nat.mul_div_cancel' hdvd; rw [h0, mul_one] at this; exact this)
      have h2 : q ≤ (n / d).minFac :=
        hqmin _ (Nat.minFac_prime hk1) ((Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd hdvd))
      have h3 := minFac_le_qmax hk1 hk0
      have h4 : (q : ℝ) ≤ qmax (n / d) := by exact_mod_cast h2.trans h3
      exact hqL (lt_of_le_of_lt h4 hlt)
    subst hdeq
    have hchi0 : chi y m d = 0 := by
      unfold chi
      rw [if_neg]
      intro hcp
      have := hcp d (Nat.mem_divisors_self d hn0) h1 (Or.inl hev)
      rw [← hqdef] at this
      have hge : y / p ≤ (d : ℝ) * q := not_lt.1 hc
      have : (d : ℝ) * (q : ℝ) ^ 2 ≥ y := by
        have e1 : (d : ℝ) * (q : ℝ) ^ 2 = ((d : ℝ) * q) * q := by ring
        have e2 : y = (y / p) * p := by field_simp
        rw [e1]
        calc y = (y / p) * p := e2
          _ ≤ (y / p) * q := mul_le_mul_of_nonneg_left hpqR.le hypos.le
          _ ≤ ((d : ℝ) * q) * q := mul_le_mul_of_nonneg_right hge (by positivity)
      linarith
    rw [hchi0, mul_zero]

end KappaOmega2
