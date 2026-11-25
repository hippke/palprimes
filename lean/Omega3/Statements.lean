import Omega3.DefsSieve

/-!
# Ω ≤ 3 in every base `b ≥ 5`: the frozen item statements

One `def ItemXnn : Prop` per item of `BLUEPRINT.md` §3. Each item is proved in its own file
`Omega3/Items/Xnn.lean` as `theorem itemXnn : ItemXnn`. An item never refers to another item; where the
mathematics uses another lemma, its statement appears as an explicit hypothesis (a named `…Stmt` of `Defs`),
and the skeleton supplies it. Nothing here is assumed.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega ArithmeticFunction.Moebius

namespace Omega3

open Palprimes Palprimes.Greaves

/-! ## Targets -/

/-- **Main theorem.** In every base `b ≥ 5` there are infinitely many palindromes with at most three prime factors
counted with multiplicity. -/
def MainTheorem : Prop :=
  ∀ b : ℕ, 5 ≤ b → {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite

/-- **Counting form.** For `N` large, at least `c 3^N / log x` palindromes with `2N + 1` digits, coprime to `b³ − b`,
have `Ω ≤ 3` and every prime factor `> x^{1/250}`, `x = b^{2N+1}`. -/
def MainCount : Prop :=
  ∀ b : ℕ, 5 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (3 : ℝ) ^ N / Real.log (xx b N) ≤
      (#((piStar b N).filter (fun n => Ω n ≤ 3 ∧ ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ)

/-! ## Part L: level of distribution for the weighted sequence -/

/-- L01 (= pilot ItemM). `|G_g| = F_m` for the Fejér weight. -/
def ItemL01 : Prop := FejerAbsStmt

/-- L02 (= pilot ItemE). Bernoulli. -/
def ItemL02 : Prop := BernoulliStmt

/-- L03 (= pilot ItemN). Fejér fourth moment in closed form. -/
def ItemL03 : Prop := FejerM4Stmt

/-- L04. Exact LP majorant for `b = 6` (28 Bernstein cells). -/
def ItemL04 : Prop := Cert6Stmt

/-- L05. Exact LP majorant for `b = 8` (34 Bernstein cells). -/
def ItemL05 : Prop := Cert8Stmt

/-- L06. The record majorants `T = (1 − p) + pP ≥ |G_g|^p` for every `b ≥ 5`. -/
def ItemL06 : Prop :=
  BernoulliStmt → FejerAbsStmt → Cert6Stmt → Cert8Stmt → ∀ b : ℕ, 5 ≤ b → RecMajStmt b

/-- L07. Record numerics: for every `b ≥ 5` the scalar conditions of Proposition C_w at `θ = 17/50`, `θ₀ = 3/10`
((ii*) at `δ′ = 2θ`, (iii*) at `δ′ = 2θ₀`, cut `A₁` only) and of Proposition CQ_E′ ((Q1), (Q2′)) hold with explicit
exponents `ψ_T, lA, θ_w, κ`. -/
def ItemL07 : Prop :=
  FejerM4Stmt → ∀ b : ℕ, 5 ≤ b → ∃ ψ lA θw κ : ℝ,
    0 < recTau b 0 ∧ recTau b 0 ≤ (b : ℝ) ^ (-ψ) ∧ trigMass (recH b) (recTau b) ≤ (b : ℝ) ^ lA ∧
    mw4 b (recGR b) ≤ (b : ℝ) ^ (-(1 + θw)) ∧ 0 < θw ∧ 0 < κ ∧
    2 * thS + 2 * κ < ψ + (1 - recP b) * (2 * thS * θw - 2 * κ) / 3 ∧
    lA + 2 * κ < (1 - recP b) * (2 * th0 * θw - 2 * κ) / 3 ∧
    2 * c1 < ψ ∧ 3 * lA < (1 - recP b) * ψ * θw

/-- L08. Lemma 2.8 (weight free averaged majorant products). -/
def ItemL08 : Prop := Lemma28Stmt

/-- L09. Lemma 2.9_w (inner large sieve, exact fourth moment). -/
def ItemL09 : Prop := Lemma29wStmt

/-- L10. Proposition C_w with the cut `A₁` only (no Lemma 2.10_w): the scalar conditions (ii*), (iii*) give
`TL¹_w(θ, κ, θ₀)`. -/
def ItemL10 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ lA θw θ κ θ₀ : ℝ),
    3 ≤ b → IsDigitWeight b g → 0 < p → p < 1 → H ≤ 2 * b - 2 →
    (∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) →
    0 < τ 0 → τ 0 ≤ (b : ℝ) ^ (-ψ) → trigMass H τ ≤ (b : ℝ) ^ lA →
    mw4 b g ≤ (b : ℝ) ^ (-(1 + θw)) → 0 < θw → 0 < κ → 0 < θ₀ → θ₀ < θ → θ < 1 / 2 →
    2 * θ + 2 * κ < ψ + (1 - p) * (2 * θ * θw - 2 * κ) / 3 →
    lA + 2 * κ < (1 - p) * (2 * θ₀ * θw - 2 * κ) / 3 →
    Lemma28Stmt → Lemma29wStmt → TL1w b g θ κ θ₀

/-- L11. Lemma SS (self-similarity of TL¹). -/
def ItemL11 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (θ κ θ₀ : ℝ), 2 ≤ b → IsDigitWeight b g → 0 < θ₀ → θ₀ < θ → 0 < κ →
    TL1w b g θ κ θ₀ → SSStmt b g θ κ

/-- L12. Lemma K (weighted Col bound). -/
def ItemL12 : Prop := ∀ (b : ℕ) (g : ℕ → ℝ), 2 ≤ b → IsDigitWeight b g → LemmaKStmt b g

/-- L13. Lemma 2.1_w: `X_w ≫ 1`. -/
def ItemL13 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ), 3 ≤ b → IsDigitWeight b g → 0 < g 0 → 0 < g 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, c ≤ XW b g N

/-- L14. Regrouping (Lemmas 2.2_w, 2.3, r169 Lemma R): the level sum is bounded by the Farey totals at the
shifts `k/(b³ − b)`. -/
def ItemL14 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (Kt : ℝ), 2 ≤ b →
    (∀ k < bigB b, FareyW b g N D ((k : ℝ) / (bigB b : ℝ)) ≤ Kt) →
    levelSum b g N D ≤ ((bigB b).divisors.card : ℝ) *
      (∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e) * Kt

/-- L15. Lemma W_w, the three ranges (small moduli by Lemma K, middle by Lemma SS, window by TL¹): the Farey
total up to `y = x^θ` is smaller than any power of `log x`. -/
def ItemL15 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (θ κ θ₀ : ℝ), 3 ≤ b → IsDigitWeight b g → 0 < g 0 → 0 < g 1 →
    0 < θ₀ → θ₀ < θ → θ < 1 / 2 → 0 < κ →
    LemmaKStmt b g → SSStmt b g θ κ → TL1w b g θ κ θ₀ →
    ∀ A : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k < bigB b,
      FareyW b g N ⌊xx b N ^ θ⌋₊ ((k : ℝ) / (bigB b : ℝ)) ≤ 1 / Real.log (xx b N) ^ A

/-- L16. Facts about the record data: a digit weight with `g(0), g(1) > 0`, every `g(a) ≤ 1/3`,
`0 < p_T < 1`, degree `≤ 2b − 2`. -/
def ItemL16 : Prop :=
  ∀ b : ℕ, 5 ≤ b → IsDigitWeight b (recGR b) ∧ 0 < recGR b 0 ∧ 0 < recGR b 1 ∧
    (∀ a, recGR b a ≤ 1 / 3) ∧ 0 < recP b ∧ recP b < 1 ∧ recH b ≤ 2 * b - 2

/-- L17. Facts about the weighted sequence: `0 ≤ a_n ≤ M^{N+1}` when `0 ≤ g ≤ M`, `a_n ≠ 0` only on `Π*_b(2N)`,
`A^w_q = Σ_{n < x, q ∣ n} a_n`, and `X_w ≤ 1` for a digit weight. -/
def ItemL17 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (M : ℝ) (N : ℕ), 2 ≤ b → (∀ a, 0 ≤ g a) → (∀ a, g a ≤ M) →
    (∀ n, 0 ≤ aW b g N n ∧ aW b g N n ≤ M ^ (N + 1) ∧ (aW b g N n ≠ 0 → n ∈ piStar b N)) ∧
    (∀ q, AW b g N q = ∑ n ∈ range (b ^ (2 * N + 1)), if q ∣ n then aW b g N n else 0) ∧
    (IsDigitWeight b g → XW b g N ≤ 1)

/-! ## Part Q: squares (Proposition CQ with route E′) -/

/-- Q01. Reduction (step 1 of CQ). -/
def ItemQ01 : Prop := SqRedStmt

/-- Q02. `T_K` over square and prime moduli ((3.1), (3.2)). -/
def ItemQ02 : Prop := SqDiagStmt

/-- Q03. Route E′: Parseval modulo `p²`. -/
def ItemQ03 : Prop := SqParsevalStmt

/-- Q04. Proposition CQ_E′: with (Q1) `ψ_T > 2c₁` and (Q2′) `3lA < (1 − p)ψ_Tθ_w`, the prime squares in
`(x^{c₀}, x^{c₁}]` carry weight `≤ 2X_w x^{−c₀} + x^{−η}`. -/
def ItemQ04 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ lA θw c₀ c₁ : ℝ),
    3 ≤ b → IsDigitWeight b g → 0 < p → p < 1 → H ≤ 2 * b - 2 →
    (∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) →
    0 < τ 0 → τ 0 ≤ (b : ℝ) ^ (-ψ) → trigMass H τ ≤ (b : ℝ) ^ lA →
    mw4 b g ≤ (b : ℝ) ^ (-(1 + θw)) → 0 < θw → 0 < c₀ → c₀ < c₁ → c₁ < 1 / 2 →
    2 * c₁ < ψ → 3 * lA < (1 - p) * ψ * θw →
    SqRedStmt → SqDiagStmt → SqParsevalStmt →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      SqW b g N c₀ c₁ ≤ 2 * XW b g N * xx b N ^ (-c₀) + xx b N ^ (-η)

/-! ## Part S: the sieve (Greaves 1986 §2–3 with Lemma A bands and Lemma 4 (ii′)) -/

/-- S01. Greaves' Lemma 1 (radical form): `Σ((a, P(z)), z) ≤ [ν_{y,U}(a) ≤ 3] w(p(a))` for `2 ≤ a < y^g`,
`g ≤ V + 3U`, `z ≥ y^U`, under the linear lines of (1.8): `0 ≤ w ≤ W(1)`, `w = W(1)` above `y^U`, `w = 0` up to `y^V`,
`w(p) ≤ log_y p − V` in between. -/
def ItemS01 : Prop :=
  ∀ (y U V z g' : ℝ) (w : ℕ → ℝ) (a : ℕ), 1 < y → 1 / 2 < U → U < 1 → 0 ≤ V → y ^ U ≤ z →
    g' ≤ V + 3 * U → 2 ≤ a → (a : ℝ) < y ^ g' →
    (∀ p : ℕ, p.Prime → 0 ≤ w p) → (∀ p : ℕ, p.Prime → w p ≤ U - V) →
    (∀ p : ℕ, p.Prime → y ^ U ≤ (p : ℝ) → w p = U - V) →
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ y ^ V → w p = 0) →
    (∀ p : ℕ, p.Prime → y ^ V < (p : ℝ) → (p : ℝ) < y ^ U → w p ≤ Real.log p / Real.log y - V) →
    SigmaG y z (U - V) w (radLt a z) ≤ ptarget y U w a

/-- S02. Greaves' Lemma 2 (2.23) for squarefree `A ∣ P(z)`. -/
def ItemS02 : Prop :=
  ∀ (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ), 0 < m → m ≤ 1 → 1 < y → z ≤ y → Squarefree A →
    (∀ p ∈ A.primeFactors, (p : ℝ) < z) →
    SigmaG y z W1' w A = Sig1 y z m W1' w A + Sig2 y z m W1' w A + Sig3 y z m W1' w A + Sig4 y z m W1' w A

/-- S03. `Σ₄ ≥ 0` (Lemma 4 (iii) and (2.12)). -/
def ItemS03 : Prop :=
  ∀ (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ), 0 < m → 1 < y → Squarefree A →
    (∀ p ∈ A.primeFactors, (p : ℝ) < z) → (∀ p, 0 ≤ w p) →
    (∀ δ ∈ (primorialLt z).divisors, Even (ω δ) → 2 ≤ ω δ → chibar y m δ = 1 →
      ∑ p ∈ δ.primeFactors, w p ≤ W1') →
    0 ≤ Sig4 y z m W1' w A

/-- S04. `Σ₂ + Σ₃ ≥ −Σ_{δ ∈ 𝒟, δ ∣ A} Λ{(A/δ, P(√(y/δ))), φ(δ), w}` ((3.28), (3.29)–(3.31)), under (3.10). -/
def ItemS04 : Prop :=
  ∀ (y z m W1' : ℝ) (w : ℕ → ℝ) (A : ℕ), 0 < m → 1 < y → Squarefree A →
    (∀ p ∈ A.primeFactors, (p : ℝ) < z) → (∀ p, 0 ≤ w p) →
    (∀ δ ∈ Dset y z m, δ ∣ A → 0 ≤ phiW W1' w δ ∧
      (3 ≤ ω δ → ∀ q : ℕ, q.Prime → q < δ.minFac → w q ≤ phiW W1' w δ)) →
    -(∑ δ ∈ (Dset y z m).filter (· ∣ A),
        LamA (radLt (A / δ) (Real.sqrt (y / δ))) (phiW W1' w δ) w) ≤
      Sig2 y z m W1' w A + Sig3 y z m W1' w A

/-- S05. The weight of the route satisfies the hypotheses of S01, S03, S04 (Greaves (1.8) linear lines, (3.10),
Lemma 4 (iii), `φ ≥ 0` on `𝒟`). -/
def ItemS05 : Prop :=
  ∀ y : ℝ, 1 < y →
    (∀ p : ℕ, 0 ≤ wy y p) ∧ (∀ p : ℕ, p.Prime → wy y p ≤ W1) ∧
    (∀ p : ℕ, p.Prime → y ^ UU ≤ (p : ℝ) → wy y p = W1) ∧
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ y ^ mm → wy y p = 0) ∧
    (∀ p : ℕ, p.Prime → y ^ mm < (p : ℝ) → (p : ℝ) < y ^ UU → wy y p ≤ Real.log p / Real.log y - mm) ∧
    (∀ δ ∈ Dset y (y ^ UU) mm, 0 ≤ phiW W1 (wy y) δ ∧
      (3 ≤ ω δ → ∀ q : ℕ, q.Prime → q < δ.minFac → wy y q ≤ phiW W1 (wy y) δ)) ∧
    (∀ δ ∈ (primorialLt (y ^ UU)).divisors, Even (ω δ) → 2 ≤ ω δ → chibar y mm δ = 1 →
      ∑ p ∈ δ.primeFactors, wy y p ≤ W1)

/-- S06. Greaves' Lemma 3, pointwise part (generic). -/
def ItemS06 : Prop :=
  ∀ (z₁ c K : ℝ) (f Λ : ℕ → ℝ) (M : ℕ), 0 ≤ c → 1 ≤ K → Λ 1 = 1 →
    (∀ d, Λ d ≠ 0 → Squarefree d ∧ (d : ℝ) < z₁) →
    (∀ q : ℕ, q.Prime → (q : ℝ) < z₁ → f q ≤ K * c * (Λ 1 + Λ q) ^ 2) → 1 ≤ M →
    LamA (radLt M z₁) c f ≤ K * c * (∑ d ∈ M.divisors, Λ d) ^ 2

/-- S07. Admissibility outside the bands: Lemma 4 (i) with Greaves' weights for `p₁ ≥ y^{x_n}` and Lemma 4 (ii′)
(cap `10t²`) for odd `ν(δ) ≥ 3`: `W(t) ≤ φ(δ)(2 log q/log(y/δ))²` for primes `q` with `q²δ < y`. -/
def ItemS07 : Prop :=
  ∀ (B : BandData), BandOK B → ∀ (y : ℝ) (δ q : ℕ), 1 < y → δ ∈ Dset y (y ^ UU) mm →
    ¬ (∃ i, inBand B y i δ) → q.Prime → (q : ℝ) ^ 2 * δ < y →
    wy y q ≤ phiW W1 (wy y) δ * (2 * Real.log q / Real.log (y / δ)) ^ 2

/-- S08. Lemma A part 3 (with `η̂ = 0` it is Greaves' (F4) for Selberg's weights): `λ₁ + λ_q = g_η(u) + o(1)`,
`u = log q/log √x`, uniformly for primes `x^{u_lo} ≤ q < √x` and the finitely many `η̂ ∈ etas`. -/
def ItemS08 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ etas : List StepFn, (∀ e ∈ etas, StepOK e) → ∀ ulo ε : ℝ, 0 < ulo → 0 < ε →
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ e ∈ etas, ∀ q : ℕ, q.Prime → x ^ ulo ≤ (q : ℝ) → (q : ℝ) < Real.sqrt x →
      |lamA b e x 1 + lamA b e x q - gEta e (Real.log q / Real.log (Real.sqrt x))| ≤ ε

/-- S09. Lemma A part 1 (`λ₁ = 1`, `|λ_d| ≤ C`, support). -/
def ItemS09 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ etas : List StepFn, (∀ e ∈ etas, StepOK e) → LemmaA1Stmt b etas

/-- S10. Band certificate at `θ = 0.340`: band data with the Lemma 3″ allowance on every band, `c_η ≤ c_i`, and
total cost `Σ (c_i − 1)I_i ≤ 0.007` (r188 design A with 5 bands, mainterm NOTES §1: cost 0.006066; 4 bands cost 0.0074). -/
def ItemS10 : Prop :=
  ∃ (B : BandData) (ε₀ : ℝ), 0 < ε₀ ∧ BandOK B ∧ BandAllow B ε₀ ∧
    (∀ i < B.etas.length, cEta (B.etas.getD i []) ≤ (B.cs.getD i 1 : ℝ)) ∧ bandCost B ≤ 7 / 1000

/-- S11. The sieve coefficients: support in squarefree `n ≤ y` and `|c(n)| ≤ K 3^{ω(n)}` (Greaves p. 89, each `n`
has at most one `δ`). -/
def ItemS11 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ B : BandData, BandOK B → LemmaA1Stmt b ([] :: B.etas) →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∃ K y₀ : ℝ, ∀ y ≥ y₀, ∀ n : ℕ, cSieve b B ε y n ≠ 0 →
      (Squarefree n ∧ 1 ≤ n ∧ (n : ℝ) ≤ y ∧ n ∣ primorialLt (y ^ UU)) ∧ |cSieve b B ε y n| ≤ K * 3 ^ ω n

/-- S12. Expansion of the linear form: `Σ_{n ∣ a} c(n) = Σ₁(A) − (1 + ε) Σ_{δ ∈ 𝒟, δ ∣ A} φ(δ)(Σ_{d ∣ A/δ} Λ_δ(d))²`,
`A = (a, P(z))`, `z = y^U`. -/
def ItemS12 : Prop :=
  ∀ (b : ℕ) (B : BandData) (ε y : ℝ) (a : ℕ), 2 ≤ b → 1 < y → 1 ≤ a →
    ∑ n ∈ a.divisors, cSieve b B ε y n =
      Sig1 y (y ^ UU) mm W1 (wy y) (radLt a (y ^ UU)) -
        (1 + ε) * ∑ δ ∈ (Dset y (y ^ UU) mm).filter (· ∣ radLt a (y ^ UU)),
          phiW W1 (wy y) δ * (∑ d ∈ (radLt a (y ^ UU) / δ).divisors, LamD b B y δ d) ^ 2

/-- S13. Facts on `𝒟`: squarefree, primes `< z`, `y ≤ δ p(δ)²`, and `y/δ ≥ y^{c_D}` with `c_D = (1/2)(2/3)^{84}`. -/
def ItemS13 : Prop :=
  ∀ y : ℝ, 1 < y → ∀ δ ∈ Dset y (y ^ UU) mm,
    Squarefree δ ∧ (∀ p ∈ δ.primeFactors, (p : ℝ) < y ^ UU) ∧ y ≤ (δ : ℝ) * (δ.minFac : ℝ) ^ 2 ∧
      y ^ ((1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84) ≤ y / δ

/-- S14. Facts on band primes: the band index is unique, `c_δ ≥ 1`, `x = log δ/log y ∈ [x_i, x_{i+1}]` and `φ(δ) = U − x`. -/
def ItemS14 : Prop :=
  ∀ B : BandData, BandOK B → ∀ y : ℝ, 1 < y → ∀ (i δ : ℕ), inBand B y i δ →
    etaOf B y δ = B.etas.getD i [] ∧ cOf B y δ = (B.cs.getD i 1 : ℝ) ∧ B.etas.getD i [] ∈ B.etas ∧ 1 ≤ cOf B y δ ∧
    (B.xs.getD i 0 : ℝ) ≤ Real.log δ / Real.log y ∧ Real.log δ / Real.log y ≤ (B.xs.getD (i + 1) 0 : ℝ) ∧
    phiW W1 (wy y) δ = UU - Real.log δ / Real.log y

/-- S15. Facts on `(a, P(z))`: squarefree, its primes are the primes `< z` of `a`, it divides `P(z)` and `a`, and a
squarefree `d` with primes `< z` divides `a` iff it divides `(a, P(z))`. -/
def ItemS15 : Prop :=
  ∀ (a : ℕ) (z : ℝ), 1 ≤ a →
    Squarefree (radLt a z) ∧ (∀ p ∈ (radLt a z).primeFactors, (p : ℝ) < z ∧ p ∣ a) ∧
    radLt a z ∣ primorialLt z ∧ radLt a z ∣ a ∧ radLt (radLt a z) z = radLt a z ∧
    ∀ d : ℕ, Squarefree d → (∀ p ∈ d.primeFactors, (p : ℝ) < z) → (d ∣ a ↔ d ∣ radLt a z)

/-! ## Part M: the main term -/

/-- M01. Main-term identity (Greaves Lemma 5 algebra): `Σ_{n ∣ P(z)} c(n)γ(n)/n = M₁ − (1 + ε) Σ_{δ ∈ 𝒟} φ(δ)γ(δ)/δ Q(Λ_δ)`. -/
def ItemM01 : Prop :=
  ∀ (b : ℕ) (B : BandData) (ε y : ℝ), 2 ≤ b → 1 < y →
    MTs b B ε y = M1 b y - (1 + ε) * ∑ δ ∈ Dset y (y ^ UU) mm,
      phiW W1 (wy y) δ * rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ)

/-- M02. Lemma A part 2: `Q(Λ^η) ≤ (c_η + ε)/G(√x)` for `x ≥ x₀`. -/
def ItemM02 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ etas : List StepFn, (∀ e ∈ etas, StepOK e) → ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ e ∈ etas, Qform b x (lamA b e x) ≤ (cEta e + ε) / GS b (Real.sqrt x)

/-- M03. (F5): `1/G(√x) ≤ (1 + ε) e^γ V(√x)` for `x ≥ x₀`. -/
def ItemM03 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x ≥ x₀,
    1 / GS b (Real.sqrt x) ≤ (1 + ε) * Real.exp Real.eulerMascheroniConstant * MT.VB b (Real.sqrt x)

/-- M04. Band cost (Lemma 5′): `Σ_{δ ∈ 𝒟} φ(δ)γ(δ)/δ e^γ V(√(y/δ))(c_δ − 1) ≤ 2e^γ V(y)(Σ_i (c_i − 1)I_i + ε)`. -/
def ItemM04 : Prop :=
  ∀ b : ℕ, 2 ≤ b → ∀ B : BandData, BandOK B → ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀,
    ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ * rhoB b δ / δ * Real.exp Real.eulerMascheroniConstant *
        MT.VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1) ≤
      2 * Real.exp Real.eulerMascheroniConstant * MT.VB b y * (bandCost B + ε)

/-- M05. `M₂ + M₃ = O(V(y))`. -/
def ItemM05 : Prop := ∀ b : ℕ, 2 ≤ b → ∃ C y₀ : ℝ, ∀ y ≥ y₀, M23 b y ≤ C * MT.VB b y

/-- M06. Greaves' Lemma 7 (from the Rosser–Iwaniec asymptotic `Palprimes.E1.rosserAsymp_of_two_le`). -/
def ItemM06 : Prop := ∀ b : ℕ, 2 ≤ b → Lemma7Stmt b

/-- M07. Greaves' Lemma 8: `M(y^U) = M*(y^U) + o(V(y))`. -/
def ItemM07 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Lemma7Stmt b → ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀,
    |M1 b y - M23 b y - Mstar b y (y ^ UU)| ≤ ε * MT.VB b y

/-- M08. Greaves' Lemma 9 (Halberstam–Richert Reduction Lemma). -/
def ItemM08 : Prop := ∀ b : ℕ, 2 ≤ b → Lemma7Stmt b → Lemma9Stmt b

/-- M09. Greaves' Lemma 10 (exact identity, even `ν(n)`). -/
def ItemM09 : Prop := Lemma10Stmt

/-- M10. Greaves' Lemma 11: `M*(y^U) = E11(y) + o(V(y))`. -/
def ItemM10 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Lemma9Stmt b → Lemma10Stmt → ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀,
    |Mstar b y (y ^ UU) - E11 b y| ≤ ε * MT.VB b y

/-- M11. Greaves' Lemma 12: `E11(y) = 2e^γ V(y)(𝓜(W) + o(1))`. -/
def ItemM11 : Prop :=
  ∀ b : ℕ, 2 ≤ b → Lemma7Stmt b → ∀ ε : ℝ, 0 < ε → ∃ y₀ : ℝ, ∀ y ≥ y₀,
    |E11 b y - 2 * Real.exp Real.eulerMascheroniConstant * MT.VB b y * mvalW| ≤ ε * MT.VB b y

/-- M12. `h`-table certificate: a table with `h(t, 1) ≤ H_j` on `[ξ_j, ξ_{j+1}]` (from `m` to `1/4`) whose lower
bound for `𝓜(W)` is `≥ 0.009` (r188 `M_low = 0.010484`; with the Q = 2000 cells `𝓜(W) ∈ [0.01042, 0.01061]`). -/
def ItemM12 : Prop := ∃ ξ Hb : List ℚ, HTableStmt ξ Hb ∧ 9 / 1000 ≤ MvalLower ξ Hb

/-- M13. An `h`-table gives a lower bound for `𝓜(W)` (`h ≥ 0`, `h = 0` on `[1/4, 1/2]`, `W ≥ 0`). -/
def ItemM13 : Prop := ∀ ξ Hb : List ℚ, HTableStmt ξ Hb → MvalLower ξ Hb ≤ mvalW

/-! ## All items -/

/-- The conjunction of all items. -/
def AllItems : Prop :=
  ItemL01 ∧ ItemL02 ∧ ItemL03 ∧ ItemL04 ∧ ItemL05 ∧ ItemL06 ∧ ItemL07 ∧ ItemL08 ∧ ItemL09 ∧ ItemL10 ∧
  ItemL11 ∧ ItemL12 ∧ ItemL13 ∧ ItemL14 ∧ ItemL15 ∧ ItemL16 ∧ ItemL17 ∧
  ItemQ01 ∧ ItemQ02 ∧ ItemQ03 ∧ ItemQ04 ∧
  ItemS01 ∧ ItemS02 ∧ ItemS03 ∧ ItemS04 ∧ ItemS05 ∧ ItemS06 ∧ ItemS07 ∧ ItemS08 ∧ ItemS09 ∧ ItemS10 ∧
  ItemS11 ∧ ItemS12 ∧ ItemS13 ∧ ItemS14 ∧ ItemS15 ∧
  ItemM01 ∧ ItemM02 ∧ ItemM03 ∧ ItemM04 ∧ ItemM05 ∧ ItemM06 ∧ ItemM07 ∧ ItemM08 ∧ ItemM09 ∧ ItemM10 ∧
  ItemM11 ∧ ItemM12 ∧ ItemM13

end Omega3
