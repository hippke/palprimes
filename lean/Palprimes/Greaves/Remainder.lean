import Palprimes.Greaves.Sieve

/-! # Main term and remainder of Greaves' sieve sum

With `#𝒜_d = X/d + E(d)` for `(d, B) = 1` and `#𝒜_d = 0` otherwise,
`Σ_{T} term(T) #𝒜_{Π T} = X · MT + Σ_{T coprime} term(T) E(Π T)`, and the remainder is at most
`w(1) Σ_{q ≤ y, (q,B)=1} 3^{ω(q)} |E(q)|`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.Greaves

/-- `|w(1) − Σ_T w| ≤ 3^{|T|} w(1)` when `0 ≤ w ≤ w(1)`. -/
theorem abs_term_le (w : ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hwle : ∀ p, w p ≤ w 1) (σ : Bool) (z : ℝ)
    (T : Finset ℕ) : |term w σ z (w 1) T| ≤ 3 ^ T.card * w 1 := by
  classical
  unfold term
  have hw1 : 0 ≤ w 1 := le_trans (hw0 1) (hwle 1)
  split_ifs
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h1 : 0 ≤ ∑ p ∈ T, w p := Finset.sum_nonneg (fun p _ => hw0 p)
    have h2 : ∑ p ∈ T, w p ≤ T.card * w 1 := by
      calc ∑ p ∈ T, w p ≤ ∑ _p ∈ T, w 1 := Finset.sum_le_sum (fun p _ => hwle p)
        _ = T.card * w 1 := by rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (1 : ℝ) + T.card ≤ 3 ^ T.card := by
      have : 1 + T.card ≤ 3 ^ T.card := by
        induction T.card with
        | zero => simp
        | succ n ih => rw [pow_succ]; omega
      exact_mod_cast this
    rw [abs_le]; constructor <;> nlinarith
  · simp; positivity

/-- Products of distinct primes: `T ↦ Π T` is injective on sets of primes. -/
theorem prod_injOn (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (S.powerset : Set (Finset ℕ)) := by
  intro T1 hT1 T2 hT2 h
  simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hT1 hT2
  have hp1 : ∀ p ∈ T1, p.Prime := fun p hp => hS p (hT1 hp)
  have hp2 : ∀ p ∈ T2, p.Prime := fun p hp => hS p (hT2 hp)
  have e : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (∏ p ∈ T, p).primeFactors = T := by
    intro T hT
    exact Nat.primeFactors_prod hT
  rw [← e T1 hp1, ← e T2 hp2]
  exact congrArg Nat.primeFactors h

end Palprimes.Greaves
