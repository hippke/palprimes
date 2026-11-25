import Omega3.Statements

/-!
# M10 helpers: per-prime quantities of Greaves' Lemma 11 (see `M10_PLAN.md` §1)

`Hp b y p = Σ_{d | P(y^U), p | d} μ(d) γ(d)/d χ⁻_y(d) χ*_y(d₁)`, so `M*(y^U) = W(1) T⁻(y, y^U) − Σ_{p < y^U} w(p) H_p`.
`Ep b y p = γ(p)/p {σ⁺(y/p) − Σ_{n ∈ N_p} χ̄_y(n) γ(n)/n σ⁺(y/(pn))}` (the bracket of `E11`).
`DeltaP = −H_p − E_p`. `Rpm b η ζ plus` is the `t`-sum of Lemma 9 with a real lower prime bound `ζ`
(`T9sum b η s plus = Rpm b η (η^{1/s}) plus`, `rfl`).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3

open Palprimes Palprimes.Greaves

/-- `H_p`. -/
noncomputable def Hp (b : ℕ) (y : ℝ) (p : ℕ) : ℝ :=
  open Classical in
  ∑ d ∈ (primorialLt (y ^ UU)).divisors.filter (p ∣ ·), (μ d : ℝ) * rhoB b d / d *
    (if chiMinusProp y d then 1 else 0) * (if chiStarProp y mm (d1of d p) then 1 else 0)

/-- The `n`-set `N_p` of `E11`. -/
noncomputable def Nset (y : ℝ) (p : ℕ) : Finset ℕ :=
  open Classical in
  (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧ (n : ℝ) * n.minFac < y / p)

/-- `E_p`. -/
noncomputable def Ep (b : ℕ) (y : ℝ) (p : ℕ) : ℝ :=
  rhoB b p / p * (sigmaP b (y / p) - ∑ n ∈ Nset y p, chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)))

/-- `Δ_p = −H_p − E_p`. -/
noncomputable def DeltaP (b : ℕ) (y : ℝ) (p : ℕ) : ℝ := -Hp b y p - Ep b y p

/-- `S9(η, ζ, ±)`: squarefree `t ∣ P(η)`, all primes `> ζ`, all primes `< η/t`, parity. -/
noncomputable def S9 (η ζ : ℝ) (plus : Bool) : Finset ℕ :=
  open Classical in
  (primorialLt η).divisors.filter (fun t : ℕ => (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧
    (∀ q ∈ t.primeFactors, (q : ℝ) < η / t) ∧ (if plus then Even (ω t) else Odd (ω t)))

/-- `R^±(η, ζ) = Σ_{t ∈ S9(η, ζ, ±)} γ(t)/t σ⁺(η/t)`. -/
noncomputable def Rpm (b : ℕ) (η ζ : ℝ) (plus : Bool) : ℝ :=
  ∑ t ∈ S9 η ζ plus, rhoB b t / t * sigmaP b (η / t)

theorem T9sum_eq_Rpm (b : ℕ) (η s : ℝ) (plus : Bool) : T9sum b η s plus = Rpm b η (η ^ (1 / s)) plus := rfl

/-- The `d₁`-set: squarefree divisors of `P(y^U)` with all primes `> p`. -/
noncomputable def D1set (y : ℝ) (p : ℕ) : Finset ℕ :=
  open Classical in (primorialLt (y ^ UU)).divisors.filter (fun d : ℕ => ∀ q ∈ d.primeFactors, p < q)

end Omega3
