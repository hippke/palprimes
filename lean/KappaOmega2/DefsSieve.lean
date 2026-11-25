import KappaOmega2.Defs

/-!
# Ω ≤ 2 for κ-palindromes: definitions, part 2 (Greaves 1986 sieve at `R = 2`, Lemma A weights, bands, main term)

KappaOmega2 NOTE (omega-2, 2026-11-25). This file is the Omega3 file with the sieve constants changed to Greaves 1986 at `R = 2`
(`θ = 103/200`, `U = 99/103`, `V = m = 2/103`, `k² = 582/103`, no Σ₂ bands). Docstrings that still mention `θ = 0.340`,
`R = 3`, bands or `b ≥ 5` describe the Omega3 original; the definitions are those stated. The κ theorem uses only the
sieve part of this file and the Fejér items; its own sequence, level and squares are in `DefsK.lean`, `StatementsK.lean`.


Definitions only. Sources: Greaves, Acta Arith. 47 (1986) 71–96 (page renders `r167_greaves1986_fit/img/pg-04` to
`pg-13`, pp. 76–95), `r188_sieve_floor/proof.md` §7 (Lemma A), §8, `r182_sieve_refine/proof.md` §2 (Lemma 4 (ii′)),
`r183_omega3_dossier/DOSSIER.md` §3 (Selberg facts, Lemma 3′, Lemma 5′), `lean/omega3_p0/mainterm/NOTES.md` §6.

Conventions. `P(z)` = product of the primes `< z` (`primorialLt`), `(a, P(z))` = `radLt a z`. `S(a, z) = 1` iff `a` has
no prime factor `< z` (`Ssv`). `Λ{A, c, w}` (Greaves (2.9), (2.12)) is `LamA A c w`. All Greaves sums of §2–3 are
evaluated at the squarefree number `A = (a, P(z))` (see BLUEPRINT §2: (2.10), (2.15) and Lemma 2 fail for
non-squarefree `a`; the sieve only sees `A`).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

/-! ## Sieve notation -/

/-- `P(z) = Π_{p < z} p`. -/
noncomputable def primorialLt (z : ℝ) : ℕ := ∏ p ∈ primesBelow z, p

/-- `(a, P(z))`: product of the distinct primes `< z` dividing `a`. -/
noncomputable def radLt (a : ℕ) (z : ℝ) : ℕ :=
  open Classical in ∏ p ∈ a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), p

/-- Greaves' `S(a, z)` (2.8): `1` if `a` has no prime factor `< z`, else `0`. -/
noncomputable def Ssv (a : ℕ) (z : ℝ) : ℝ :=
  open Classical in if ∀ p ∈ a.primeFactors, z ≤ (p : ℝ) then 1 else 0

/-- Greaves' `Λ{A, c, w}` (2.9) for squarefree `A`: `c` if `A = 1`, `w(p)` if `A = p` is prime, `0` otherwise. -/
noncomputable def LamA (A : ℕ) (c : ℝ) (w : ℕ → ℝ) : ℝ :=
  open Classical in if A = 1 then c else if A.Prime then w A else 0

/-- `φ(d) = W(1) − Σ_{p ∣ d} w(p)` (2.6). -/
noncomputable def phiW (W1' : ℝ) (w : ℕ → ℝ) (d : ℕ) : ℝ := W1' - ∑ p ∈ d.primeFactors, w p

/-- Jurkat–Richert condition (2.19), (2.20): every divisor `h ≠ 1` of `d` with `ν(h)` even or `ν(h) ≤ 1/m`
has `h p(h)² < y`. -/
def chiProp (y m : ℝ) (d : ℕ) : Prop :=
  ∀ h ∈ d.divisors, h ≠ 1 → (Even (ω h) ∨ (ω h : ℝ) ≤ 1 / m) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < y

/-- Greaves' `χ_y(d)` (2.19)–(2.22). -/
noncomputable def chi (y m : ℝ) (d : ℕ) : ℝ := open Classical in if chiProp y m d then 1 else 0

/-- `χ̄_y(d) = χ_y(d/p(d)) − χ_y(d)` for `d > 1`, `χ̄_y(1) = 0` (2.3). -/
noncomputable def chibar (y m : ℝ) (d : ℕ) : ℝ := if d = 1 then 0 else chi y m (d / d.minFac) - chi y m d

/-- Greaves' `ν_{y,U}(a) ≤ 3` target: `w(p(a))` if `ν_{y,U}(a) ≤ 3`, else `0` (`nu` from Palprimes). -/
noncomputable def ptarget (y U : ℝ) (w : ℕ → ℝ) (a : ℕ) : ℝ := if nu a (y ^ U) ≤ 2 then w a.minFac else 0

/-! ## Greaves' Σ(a, z) and its decomposition (Lemma 2), evaluated at squarefree `A` -/

/-- `Λ₂{A, W(1), w}` (2.13). -/
noncomputable def Lam2 (y z W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  open Classical in
  ∑ p1 ∈ (primesBelow z).filter (· ∣ A),
    ∑ p2 ∈ (primesBelow (p1 : ℝ)).filter (fun p2 : ℕ => p2 ∣ A ∧ y ≤ (p2 : ℝ) ^ 2 * p1),
      ((W1' - w p1) * Ssv (A / (p1 * p2)) p2 - w p2 * Ssv (A / (p1 * p2)) p1)

/-- `Σ(A, z) = Λ{(A, P(z)), W(1), w} − Λ₂{(A, P(z)), W(1), w}` (2.14). -/
noncomputable def SigmaG (y z W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  LamA (radLt A z) W1' w - Lam2 y z W1' w (radLt A z)

/-- `Σ₁(A, z) = Σ_{d ∣ (A, P(z))} μ(d) χ_y(d) φ(d)` (2.24). -/
noncomputable def Sig1 (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  ∑ d ∈ (radLt A z).divisors, (μ d : ℝ) * chi y m d * phiW W1' w d

/-- `Σ₂(A, z)` (2.25). -/
noncomputable def Sig2 (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  open Classical in
  ∑ p ∈ (radLt A z).primeFactors, -(chibar y m p) *
    (phiW W1' w p * Ssv (A / p) (Real.sqrt (y / p)) +
      ∑ q ∈ (A / p).primeFactors.filter (fun q : ℕ => q < p ∧ (q : ℝ) ^ 2 * p < y), w q * Ssv (A / (p * q)) p)

/-- Inner sum of (2.26), (2.27): `Σ_{t ∣ (A, P(p(δ)))} μ(t) φ(tδ)`. -/
noncomputable def innerS (W1' : ℝ) (w : ℕ → ℝ) (A δ : ℕ) : ℝ :=
  ∑ t ∈ (radLt A (δ.minFac : ℝ)).divisors, (μ t : ℝ) * phiW W1' w (t * δ)

/-- `Σ₃(A, z)` (2.26): odd `3 ≤ ν(δ) ≤ 1/m`. -/
noncomputable def Sig3 (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  open Classical in
  ∑ δ ∈ (radLt A z).divisors.filter (fun δ : ℕ => Odd (ω δ) ∧ 3 ≤ ω δ ∧ (ω δ : ℝ) ≤ 1 / m),
    (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ

/-- `Σ₄(A, z)` (2.27): even `ν(δ) ≥ 2`. -/
noncomputable def Sig4 (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ) : ℝ :=
  open Classical in
  ∑ δ ∈ (radLt A z).divisors.filter (fun δ : ℕ => Even (ω δ) ∧ 2 ≤ ω δ),
    (μ δ : ℝ) * chibar y m δ * innerS W1' w A δ

/-- The set `𝒟` of the λ²-terms: `δ ∣ P(z)`, `δ ≠ 1`, `χ̄_y(δ) = 1`, `ν(δ)` odd, `ν(δ) ≤ 1/m`
(Σ₂: `ν = 1`, `p³ ≥ y`; Σ₃: odd `ν ≥ 3`). -/
noncomputable def Dset (y z m : ℝ) : Finset ℕ :=
  open Classical in
  (primorialLt z).divisors.filter (fun δ : ℕ => δ ≠ 1 ∧ chibar y m δ = 1 ∧ Odd (ω δ) ∧ (ω δ : ℝ) ≤ 1 / m)

/-! ## The weight of the route -/

/-- `W(t)`: `0` on `[0, m]`, `min(k²t², t − m)` on `(m, 1/3]`, `t − V` on `(1/3, U]`, `W(1)` above `U` (`V = m`). -/
noncomputable def Wf (t : ℝ) : ℝ :=
  if t ≤ mm then 0 else if t ≤ 1 / 3 then min (kSq * t ^ 2) (t - mm) else if t ≤ UU then t - mm else W1

/-- `w(p) = W(log p / log y)`. -/
noncomputable def wy (y : ℝ) (p : ℕ) : ℝ := Wf (Real.log p / Real.log y)

/-! ## Selberg and Lemma A weights (density `γ(p) = 1` for `p ∤ b³ − b`) -/

/-- `{n : 1 ≤ n < z}`. -/
noncomputable def ltSet (z : ℝ) : Finset ℕ :=
  open Classical in (range ⌈z⌉₊).filter (fun n : ℕ => 1 ≤ n ∧ (n : ℝ) < z)

/-- `g(n) = γ(n)/γ*(n) = 1/φ(n)` on squarefree `n` coprime to `b³ − b`, else `0`. -/
noncomputable def gS (b n : ℕ) : ℝ :=
  open Classical in if Squarefree n ∧ Nat.Coprime n (bigB b) then 1 / (n.totient : ℝ) else 0

/-- `G(z) = Σ_{1 ≤ n < z} g(n)` (Greaves (3.8) with `z = √x`, strict inequality). -/
noncomputable def GS (b : ℕ) (z : ℝ) : ℝ := ∑ n ∈ ltSet z, gS b n

/-- A step function `η̂` on `[0, 1]`: pairs (left end, value); the value at `u` is that of the last pair with
left end `≤ u`, and `0` left of the first pair. -/
abbrev StepFn := List (ℚ × ℚ)

/-- Value of a step function. -/
noncomputable def StepFn.eval (s : StepFn) (u : ℝ) : ℝ :=
  s.foldl (fun acc pr => if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc) 0

/-- Validity: left ends strictly increasing in `(0, 1)` (so `η̂ = 0` on `[0, u_min)`, `u_min > 0`). -/
def StepOK (s : StepFn) : Prop :=
  (s.map Prod.fst).Pairwise (· < ·) ∧ ∀ pr ∈ s, 0 < pr.1 ∧ pr.1 < 1

/-- `η(q) = η̂(log q / log z)/G(z)`, `z = √x`. -/
noncomputable def etaQ (b : ℕ) (e : StepFn) (x : ℝ) (q : ℕ) : ℝ :=
  e.eval (Real.log q / Real.log (Real.sqrt x)) / GS b (Real.sqrt x)

/-- `η(k) = Σ_{q ∣ k} η(q)`. -/
noncomputable def etaK (b : ℕ) (e : StepFn) (x : ℝ) (k : ℕ) : ℝ := ∑ q ∈ k.primeFactors, etaQ b e x q

/-- `ν` of Lemma A: `ν G(z) = 1 + Σ_{k<z} g(k)η(k)`. -/
noncomputable def nuA (b : ℕ) (e : StepFn) (x : ℝ) : ℝ :=
  (1 + ∑ k ∈ ltSet (Real.sqrt x), gS b k * etaK b e x k) / GS b (Real.sqrt x)

/-- `y_k = μ(k) g(k) (ν − η(k))` for `k < z`. -/
noncomputable def ykA (b : ℕ) (e : StepFn) (x : ℝ) (k : ℕ) : ℝ := (μ k : ℝ) * gS b k * (nuA b e x - etaK b e x k)

/-- Lemma A weights at level `x` (`λ_d ω(d) = Σ_{d ∣ k, k < √x} μ(k/d) y_k`, `ω(d) = 1/d`; `λ_d = 0` if
`(d, b³ − b) > 1`). With `η̂ = 0` these are Selberg's weights `λ_x` (Greaves (3.7)). -/
noncomputable def lamA (b : ℕ) (e : StepFn) (x : ℝ) (d : ℕ) : ℝ :=
  open Classical in
  if Nat.Coprime d (bigB b) then (d : ℝ) * ∑ k ∈ (ltSet (Real.sqrt x)).filter (d ∣ ·), (μ (k / d) : ℝ) * ykA b e x k
  else 0

/-- Selberg's quadratic form `Q(Λ) = Σ_{d₁,d₂ < √x} Λ(d₁)Λ(d₂) γ([d₁,d₂])/[d₁,d₂]`. -/
noncomputable def Qform (b : ℕ) (x : ℝ) (Λ : ℕ → ℝ) : ℝ :=
  ∑ d1 ∈ ltSet (Real.sqrt x), ∑ d2 ∈ ltSet (Real.sqrt x),
    Λ d1 * Λ d2 * rhoB b (Nat.lcm d1 d2) / (Nat.lcm d1 d2 : ℝ)

/-- `Â(s) = ∫₀^s η̂(v)(s − v) dv/v`. -/
noncomputable def Ahat (e : StepFn) (s : ℝ) : ℝ := ∫ v in (0 : ℝ)..s, e.eval v * (s - v) / v

/-- Lemma A allowance `g_η(u) = 1 − ν′(1 − u) + Â(1 − u) + η̂(u)(1 − u)`, `ν′ = 1 + Â(1)`. -/
noncomputable def gEta (e : StepFn) (u : ℝ) : ℝ :=
  1 - (1 + Ahat e 1) * (1 - u) + Ahat e (1 - u) + e.eval u * (1 - u)

/-- Lemma A main-term constant
`c_η = 1 + ∫₀¹ η̂²(1 − u) du/u − ∫∫ η̂(u₁)η̂(u₂) min(1, r(u₁)r(u₂))`, `r(u) = (1 − u)/u`. -/
noncomputable def cEta (e : StepFn) : ℝ :=
  1 + (∫ u in (0 : ℝ)..1, e.eval u ^ 2 * (1 - u) / u) -
    ∫ u₁ in (0 : ℝ)..1, ∫ u₂ in (0 : ℝ)..1,
      e.eval u₁ * e.eval u₂ * min 1 ((1 - u₁) / u₁ * ((1 - u₂) / u₂))

/-! ## Σ₂ bands (Lemma A on bands of `p₁ = y^x`, `x ∈ [1/3, x_n)`) -/

/-- Band data: edges `x₀ = 1/3 < x₁ < … < x_n`, one step function and one cost bound `c_i ≥ 1` per band. -/
structure BandData where
  xs : List ℚ
  etas : List StepFn
  cs : List ℚ

/-- `x_n`, the last edge (Greaves' plain weights above it). -/
def BandData.xn (B : BandData) : ℚ := B.xs.getLastD (1 / 3)

/-- Structural conditions on band data. -/
def BandOK (B : BandData) : Prop :=
  B.xs.length = B.etas.length + 1 ∧ B.cs.length = B.etas.length ∧ B.xs.head? = some (1 / 3) ∧
    B.xs.Pairwise (· < ·) ∧ (∀ e ∈ B.etas, StepOK e) ∧ (∀ c ∈ B.cs, 1 ≤ c) ∧
    (B.xn : ℝ) ≤ 2 * UU - 1 ∧ kSq * (1 - (B.xn : ℝ)) ^ 2 ≤ 4 * (UU - B.xn)

/-- `p` is a prime in band `i`: `y^{x_i} ≤ p < y^{x_{i+1}}`. -/
def inBand (B : BandData) (y : ℝ) (i p : ℕ) : Prop :=
  p.Prime ∧ i < B.etas.length ∧ y ^ ((B.xs.getD i 0 : ℚ) : ℝ) ≤ (p : ℝ) ∧
    (p : ℝ) < y ^ ((B.xs.getD (i + 1) 0 : ℚ) : ℝ)

/-- The step function used at `δ` (band function for band primes, `0` = Selberg otherwise). -/
noncomputable def etaOf (B : BandData) (y : ℝ) (δ : ℕ) : StepFn :=
  open Classical in if h : ∃ i, inBand B y i δ then B.etas.getD (Nat.find h) [] else []

/-- The cost bound used at `δ` (`c_i` in band `i`, `1` otherwise). -/
noncomputable def cOf (B : BandData) (y : ℝ) (δ : ℕ) : ℝ :=
  open Classical in if h : ∃ i, inBand B y i δ then (B.cs.getD (Nat.find h) 1 : ℝ) else 1

/-- `I_i = U log(x_{i+1}/x_i) + (1 − U) log((1 − x_{i+1})/(1 − x_i))` (Lemma 5′). -/
noncomputable def bandI (x0 x1 : ℝ) : ℝ := UU * Real.log (x1 / x0) + (1 - UU) * Real.log ((1 - x1) / (1 - x0))

/-- Total band cost `Σ_i (c_i − 1) I_i`. -/
noncomputable def bandCost (B : BandData) : ℝ :=
  ∑ i ∈ range B.etas.length,
    ((B.cs.getD i 1 : ℝ) - 1) * bandI (B.xs.getD i 0 : ℝ) (B.xs.getD (i + 1) 0 : ℝ)

/-- The band allowance condition (Lemma 3″ hypotheses on band `i`, with margin `ε₀`): for
`x ∈ [x_i, x_{i+1}]` and `m < t < (1 − x)/2`, `g_η(u) ≥ ε₀` and `W(t) ≤ (1 − ε₀)(U − x)(g_η(u) − ε₀)²`,
`u = 2t/(1 − x)`. -/
def BandAllow (B : BandData) (ε₀ : ℝ) : Prop :=
  ∀ i < B.etas.length, ∀ x t : ℝ, (B.xs.getD i 0 : ℝ) ≤ x → x ≤ (B.xs.getD (i + 1) 0 : ℝ) →
    mm < t → 2 * t < 1 - x →
      ε₀ ≤ gEta (B.etas.getD i []) (2 * t / (1 - x)) ∧
        Wf t ≤ (1 - ε₀) * (UU - x) * (gEta (B.etas.getD i []) (2 * t / (1 - x)) - ε₀) ^ 2

/-! ## The sieve coefficient vector -/

/-- `Λ_δ`: Lemma A weights at level `y/δ` with the band function of `δ`. -/
noncomputable def LamD (b : ℕ) (B : BandData) (y : ℝ) (δ : ℕ) : ℕ → ℝ := lamA b (etaOf B y δ) (y / δ)

/-- Greaves' sieve as a linear form: `c(n) = [n ∣ P(z)] μ(n)χ_y(n)φ(n) − (1 + ε) Σ_{δ ∈ 𝒟} φ(δ) Σ_{[d₁,d₂]δ = n} Λ_δ(d₁)Λ_δ(d₂)`,
`z = y^U`, `w = wy y`. -/
noncomputable def cSieve (b : ℕ) (B : BandData) (ε y : ℝ) (n : ℕ) : ℝ :=
  open Classical in
  (if n ∣ primorialLt (y ^ UU) then (μ n : ℝ) * chi y mm n * phiW W1 (wy y) n else 0) -
    (1 + ε) * ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ *
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0

/-- The main term `Σ_{n ∣ P(z)} c(n) γ(n)/n`. -/
noncomputable def MTs (b : ℕ) (B : BandData) (ε y : ℝ) : ℝ :=
  ∑ n ∈ (primorialLt (y ^ UU)).divisors, cSieve b B ε y n * rhoB b n / n

/-! ## Greaves' main terms M₁, M₂ + M₃ (Lemma 5) and §4 -/

/-- `M₁(z) = Σ_{d ∣ P(z)} μ(d)χ_y(d)φ(d)γ(d)/d` (3.21), `z = y^U`. -/
noncomputable def M1 (b : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ (primorialLt (y ^ UU)).divisors, (μ d : ℝ) * chi y mm d * phiW W1 (wy y) d * rhoB b d / d

/-- `M₂ + M₃` without the `O`-terms ((3.22), (3.23)): `Σ_{δ ∈ 𝒟} φ(δ)γ(δ)/δ e^γ V(√(y/δ))`. -/
noncomputable def M23 (b : ℕ) (y : ℝ) : ℝ :=
  ∑ δ ∈ Dset y (y ^ UU) mm,
    phiW W1 (wy y) δ * rhoB b δ / δ * Real.exp Real.eulerMascheroniConstant * MT.VB b (Real.sqrt (y / δ))

/-- Rosser–Iwaniec `χ⁺_y` (4.2): `h p(h)² < y` for every `h ∣ d`, `h ≠ 1`, `ν(h)` odd. -/
def chiPlusProp (y : ℝ) (d : ℕ) : Prop :=
  ∀ h ∈ d.divisors, h ≠ 1 → Odd (ω h) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < y

/-- Rosser–Iwaniec `χ⁻_y` (4.3): the same for `ν(h)` even. -/
def chiMinusProp (y : ℝ) (d : ℕ) : Prop :=
  ∀ h ∈ d.divisors, h ≠ 1 → Even (ω h) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < y

/-- `χ*_y` (4.4): the same for `ν(h)` odd and `ν(h) ≤ 1/m`. -/
def chiStarProp (y m : ℝ) (d : ℕ) : Prop :=
  ∀ h ∈ d.divisors, h ≠ 1 → Odd (ω h) → (ω h : ℝ) ≤ 1 / m → (h : ℝ) * (h.minFac : ℝ) ^ 2 < y

/-- `T^±(y, w) = Σ_{d ∣ P(w)} μ(d)γ(d)χ^±_y(d)/d` ((4.16), `plus = true` for `+`). -/
noncomputable def Tpm (b : ℕ) (plus : Bool) (y w : ℝ) : ℝ :=
  open Classical in
  ∑ d ∈ (primorialLt w).divisors,
    (μ d : ℝ) * rhoB b d / d * (if (if plus then chiPlusProp y d else chiMinusProp y d) then 1 else 0)

/-- `σ⁺(η) = T⁺(η, η^{1/3})`. -/
noncomputable def sigmaP (b : ℕ) (η : ℝ) : ℝ := Tpm b true η (η ^ ((1 : ℝ) / 3))

/-- `d₁` of the decomposition (4.7) `d = d₁ p d₂`: the product of the primes of `d` above `p`. -/
noncomputable def d1of (d p : ℕ) : ℕ := ∏ q ∈ d.primeFactors.filter (fun q : ℕ => p < q), q

/-- `M*(z)` (4.9): `Σ_{d ∣ P(z)} μ(d)γ(d)χ⁻_y(d)/d {W(1) − Σ_{p ∣ d} w(p) χ*_y(d₁)}`. -/
noncomputable def Mstar (b : ℕ) (y z : ℝ) : ℝ :=
  open Classical in
  ∑ d ∈ (primorialLt z).divisors, (μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0) *
    (W1 - ∑ p ∈ d.primeFactors, wy y p * (if chiStarProp y mm (d1of d p) then 1 else 0))

/-- The `t`-set of Lemma 9: squarefree `t ∣ P(y)` with every prime `> y^{1/s}`, largest prime `< y/t`, and
`ν(t)` even (`plus`) or odd (`minus`). -/
noncomputable def T9set (y s : ℝ) (plus : Bool) : Finset ℕ :=
  open Classical in
  (primorialLt y).divisors.filter (fun t : ℕ => (∀ p ∈ t.primeFactors, y ^ (1 / s) < (p : ℝ)) ∧
    (∀ p ∈ t.primeFactors, (p : ℝ) < y / t) ∧ (if plus then Even (ω t) else Odd (ω t)))

/-- Right side of Lemma 9: `Σ_{t} μ²(t)γ(t)/t σ⁺(y/t)`. -/
noncomputable def T9sum (b : ℕ) (y s : ℝ) (plus : Bool) : ℝ :=
  ∑ t ∈ T9set y s plus, rhoB b t / t * sigmaP b (y / t)

/-- Largest prime factor `q(n)` (`q(1) = 1`). -/
noncomputable def qmax (n : ℕ) : ℕ := n.primeFactors.sup id ⊔ 1

/-- `b(n) = Σ_{d ∣ n, q(n/d) < y/(pn)} μ(d)χ_y(d)` (Lemma 10). -/
noncomputable def bfun (y m : ℝ) (p n : ℕ) : ℝ :=
  open Classical in
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (qmax (n / d) : ℝ) < y / (p * n)), (μ d : ℝ) * chi y m d

/-- The expression of Lemma 11 (without its `O`-term):
`W(1)T⁻(y, y^{1/2}) − Σ_{y^{1/2} ≤ p ≤ y^U} {W(1) − w(p)}γ(p)/p σ⁺(y/p)
 + Σ_{p < y^{1/2}} w(p)γ(p)/p {σ⁺(y/p) − Σ_{n ∣ P(y), 2 ∣ ν(n), p < p(n), n p(n) < y/p} χ̄_y(n)γ(n)/n σ⁺(y/(pn))}`. -/
noncomputable def E11 (b : ℕ) (y : ℝ) : ℝ :=
  open Classical in
  W1 * Tpm b false y (y ^ ((1 : ℝ) / 2)) -
    ∑ p ∈ (primesBelow (y ^ UU + 1)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ^ UU),
      (W1 - wy y p) * rhoB b p / p * sigmaP b (y / p) +
    ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 2))),
      wy y p * rhoB b p / p * (sigmaP b (y / p) -
        ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧
            (n : ℝ) * n.minFac < y / p),
          chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)))

/-! ## Greaves' functions h and 𝓜(W) -/

/-- The chain `x₁ > x₂ > ⋯ > x_i` read from `v = (x₁, …, x_i)` (index `0` is `x₁`). -/
noncomputable def chainV {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then v ⟨j, h⟩ else 0

/-- Region `𝓡_i` of Greaves p. 74 at `s = 1`: `x < x_i < ⋯ < x₁ < 1`, `3x_j + x_{j−1} + ⋯ + x₁ ≤ 1` for
`1 ≤ j < i`, `3x_i + x_{i−1} + ⋯ + x₁ > 1`, `x_i < u`, `u = 1 − x − Σ x_j`. -/
def HRegion86 (i : ℕ) (x : ℝ) (v : Fin i → ℝ) : Prop :=
  StrictAnti v ∧ (∀ j, x < v j) ∧ (∀ j, v j < 1) ∧
    (∀ j : ℕ, 1 ≤ j → j < i → 3 * chainV v (j - 1) + ∑ l ∈ range (j - 1), chainV v l ≤ 1) ∧
    1 < 3 * chainV v (i - 1) + ∑ l ∈ range (i - 1), chainV v l ∧
    chainV v (i - 1) < 1 - x - ∑ j, v j

/-- Greaves' `h_i(x, 1) = ∫_{𝓡_i} dx₁⋯dx_i/(x₁⋯x_i u)`. -/
noncomputable def h86 (i : ℕ) (x : ℝ) : ℝ :=
  open Classical in
  ∫ v : Fin i → ℝ, if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0

/-- `h(x, 1) = Σ_{k ≥ 1} h_{2k}(x, 1)` (finite for `x > 0`: `𝓡_i = ∅` once `i x ≥ 1`). -/
noncomputable def hS (x : ℝ) : ℝ := ∑ k ∈ Icc 1 (⌊1 / x⌋₊ + 1), h86 (2 * k) x

/-- Greaves' main-term functional for the weight of the route,
`𝓜(W) = −∫_{1/2}^1 (W(1) − W(t))/(1 − t) dt/t + ∫_0^{1/2} W(t){1/(1 − t) − h(t, 1)} dt/t`. -/
noncomputable def mvalW : ℝ :=
  -(∫ t in (1 / 2 : ℝ)..1, (W1 - Wf t) / ((1 - t) * t)) +
    ∫ t in (0 : ℝ)..(1 / 2), Wf t * (1 / (1 - t) - hS t) / t

/-- An `h`-table: cells `[ξ_j, ξ_{j+1})` with an upper bound `H_j` for `h(t, 1)` (statement of the certificate
item; the table itself is the prover's choice). -/
def HTableStmt (ξ : List ℚ) (Hb : List ℚ) : Prop :=
  ξ.length = Hb.length + 1 ∧ ξ.head? = some (2 / 103) ∧ ξ.getLastD 0 = 1 / 4 ∧ ξ.Pairwise (· < ·) ∧
    ∀ j < Hb.length, ∀ t : ℝ, (ξ.getD j 0 : ℝ) ≤ t → t ≤ (ξ.getD (j + 1) 0 : ℝ) → hS t ≤ (Hb.getD j 0 : ℝ)

/-- Lower bound for `𝓜(W)` from an `h`-table: `𝓜(W)` with `∫ W h dt/t` replaced by `Σ_j H_j ∫_{ξ_j}^{ξ_{j+1}} W dt/t`. -/
noncomputable def MvalLower (ξ Hb : List ℚ) : ℝ :=
  -(∫ t in (1 / 2 : ℝ)..1, (W1 - Wf t) / ((1 - t) * t)) + (∫ t in (0 : ℝ)..(1 / 2), Wf t / ((1 - t) * t)) -
    ∑ j ∈ range Hb.length, (Hb.getD j 0 : ℝ) * ∫ t in (ξ.getD j 0 : ℝ)..(ξ.getD (j + 1) 0 : ℝ), Wf t / t

/-! ## Named statements used as explicit hypotheses of items (sieve and main term) -/

/-- Lemma A part 1 with the support of the weights: for `x ≥ x₀`, `λ₁ = 1`, `|λ_d| ≤ C`, and `λ_d ≠ 0` only for
squarefree `1 ≤ d < √x`, uniformly over the finitely many step functions `etas`. -/
def LemmaA1Stmt (b : ℕ) (etas : List StepFn) : Prop :=
  ∃ C x₀ : ℝ, ∀ x ≥ x₀, ∀ e ∈ etas, lamA b e x 1 = 1 ∧ (∀ d, |lamA b e x d| ≤ C) ∧
    ∀ d, lamA b e x d ≠ 0 → Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) < Real.sqrt x

/-- Greaves' Lemma 7: `T⁺(y, y^{1/s}) = e^γ V(√y)(1 + o(1))` uniformly in `0 < s ≤ 3`. -/
def Lemma7Stmt (b : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ s : ℝ, 0 < s → s ≤ 3 →
    |Tpm b true y (y ^ (1 / s)) - Real.exp Real.eulerMascheroniConstant * MT.VB b (Real.sqrt y)| ≤
      ε * MT.VB b (Real.sqrt y)

/-- Greaves' Lemma 9 (Halberstam–Richert Reduction Lemma), p. 93:
`T^{(−)^ν}(y, y^{1/s}) = Σ_t μ²(t)γ(t)/t σ⁺(y/t) + o(V(y^{1/s}))` for every fixed `s ≥ 1` (sign `+`) and `s ≥ 2`
(sign `−`). Greaves prints `s ≥ 1` for both signs; for `−` and `1 ≤ s < 2` the left side has a negative main term
(`T⁻(y, w) = 1 − Σ_{p<w} ρ(p)/p T⁺(y/p, p)`) while the `t`-sum is empty, so that case is false and is not stated;
Lemma 11 uses `−` only at `y/(pd₁) > p²`, i.e. `s > 2` (NOTES §3). -/
def Lemma9Stmt (b : ℕ) : Prop :=
  ∀ s : ℝ, 1 ≤ s → ∀ plus : Bool, (plus = false → 2 ≤ s) → ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀,
    |Tpm b plus y (y ^ (1 / s)) - T9sum b y s plus| ≤ ε * MT.VB b (y ^ (1 / s))

/-- Greaves' Lemma 10 (exact identity), with `ν(n)` even (the only case used in Lemma 11; it is false for odd
`ν(n)`, see NOTES). -/
def Lemma10Stmt : Prop :=
  ∀ (y m : ℝ) (p n : ℕ), 0 < m → 0 < y → p.Prime → (p : ℝ) < y → Squarefree n → (∀ q ∈ n.primeFactors, p < q) →
    (∀ q ∈ n.primeFactors, (q : ℝ) < y) → Even (ω n) →
      bfun y m p n = if n = 1 then 1 else if (n : ℝ) * n.minFac < y / p then -chibar y m n else 0

end KappaOmega2
