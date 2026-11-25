import KappaOmega2.DefsK
import KappaOmega2.Statements

/-!
# Ω ≤ 2 for κ-palindromes (κ = 7/10, every base `b ≥ 3`): the frozen κ item statements

The sieve items `S01 … S15`, `M01 … M13` and the Fejér items `L01 … L03` are those of `Statements.lean` (Greaves 1986
at `R = 2`, `θ = 103/200`). The level and square items for the κ-sequence are below. As in `Statements.lean`, an item
never refers to another item; dependencies appear as named `…Stmt` hypotheses. Nothing here is assumed.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace KappaOmega2

open Palprimes

/-! ## Targets -/

/-- **Main theorem.** In every base `b ≥ 3` there are infinitely many κ-palindromes (`κ = 7/10`: the first
`⌊7L/20⌋` digits mirror the last ones) with at most two prime factors counted with multiplicity. -/
def MainTheoremK : Prop :=
  ∀ b : ℕ, 3 ≤ b → {n : ℕ | IsKappaPal b n ∧ Nat.IsAtMostAlmostPrime 2 n}.Infinite

/-- **Counting form.** For `N` large, at least `c 2^m W / log x` κ-palindromes with `2N + 1` digits, coprime to
`b³ − b`, have `Ω ≤ 2` and every prime factor `> x^{1/100}`. -/
def MainCountK : Prop :=
  ∀ b : ℕ, 3 ≤ b → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (2 : ℝ) ^ mK N * (WK b N : ℝ) / Real.log (xx b N) ≤
      (#((kpiStar b N).filter (fun n => Ω n ≤ 2 ∧ ∀ p ∈ n.primeFactors, xx b N ^ c0 < (p : ℝ))) : ℝ)

/-! ## Part LK: level of distribution for the κ-sequence -/

/-- LK01. `|G_g| ≤ (F_M + F_{M+1})/2` for the product weight. -/
def ItemLK01 : Prop := ProdAbsStmt

/-- LK06. The κ majorants `T = (1 − p) + pP ≥ |G_g|^p`, `p = 1 − b^{−6}`, for every `b ≥ 3`. -/
def ItemLK06 : Prop :=
  BernoulliStmt → FejerAbsStmt → ProdAbsStmt → ∀ b : ℕ, 3 ≤ b → RecMajKStmt b

/-- LK07. Record numerics for every `b ≥ 3`: weight, exponent, degree, mass, fourth moment `ψ₄ ≥ 1`, and the
rate `ψ` with `(7/20)ψ + (3/10)p ≥ θ + 1/1000`. -/
def ItemLK07 : Prop :=
  FejerM4Stmt → ∀ b : ℕ, 3 ≤ b →
    IsDigitWeight b (recGKR b) ∧ 0 < recGKR b 1 ∧ (∀ a, recGKR b a ≤ 1 / 2) ∧
    1 / 2 ≤ recPK b ∧ recPK b < 1 ∧ recHK b ≤ b * (b - 1) ∧
    0 < recTauK b 0 ∧ trigMass (recHK b) (recTauK b) ≤ 1 ∧ mw4 b (recGKR b) ≤ 1 / (b : ℝ) ∧
    ∃ ψ : ℝ, recTauK b 0 ≤ (b : ℝ) ^ (-ψ) ∧ thS + 1 / 1000 ≤ 7 / 20 * ψ + 3 / 10 * recPK b

/-- LK08. Lemma 2.8_κ (expansion with Lemma R and the middle factor). -/
def ItemLK08 : Prop := Lemma28KStmt

/-- LK09. Lemma 2.9_κ (inner large sieve with the exact fourth moment). -/
def ItemLK09 : Prop := Lemma29KStmt

/-- LKM. The middle majorant `K̃ ≥ |M_W|^p`. -/
def ItemLKM : Prop := KmidStmt

/-- LK10. Proposition C_κ: the scalar conditions give `TL¹_κ(θ, η, θ₀)`.
Large values with the cut `x^{−a}`: `4a + η < θ₀` (moduli with `D² < W`), `4a + η < 3/20` (`W ≤ D² ≤ x`),
`θ + 4a + η < 13/20` (`D² > x`); small values: diagonal `θ + η < (7/20)ψ + (3/10)p + a(1 − p)`,
off-diagonal `η < a(1 − p)`. -/
def ItemLK10 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ a η θ θ₀ : ℝ),
    3 ≤ b → IsDigitWeight b g → 1 / 2 ≤ p → p < 1 → H ≤ b * (b - 1) →
    (∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) →
    0 < τ 0 → τ 0 ≤ (b : ℝ) ^ (-ψ) → trigMass H τ ≤ 1 → mw4 b g ≤ 1 / (b : ℝ) →
    0 < a → 0 < η → 0 < θ₀ → θ₀ < θ → θ < 1 →
    4 * a + η < θ₀ → 4 * a + η < 3 / 20 → θ + 4 * a + η < 13 / 20 →
    θ + η < 7 / 20 * ψ + 3 / 10 * p + a * (1 - p) → η < a * (1 - p) →
    Lemma28KStmt → Lemma29KStmt → KmidStmt → TL1K b g θ η θ₀

/-- LK13. `X ≥ c > 0` for a digit weight with `g(1) > 0`. -/
def ItemLK13 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ), 3 ≤ b → IsDigitWeight b g → 0 < g 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, c ≤ XK b g N

/-- LK14. Regrouping: the level sum is bounded by the Farey totals at the shifts `k/(b³ − b)`. -/
def ItemLK14 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (Kt : ℝ), 3 ≤ b →
    (∀ k < bigB b, FareyK b g N D ((k : ℝ) / (bigB b : ℝ)) ≤ Kt) →
    levelSumK b g N D ≤ ((bigB b).divisors.card : ℝ) *
      (∑ e ∈ Icc 1 D, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e / e) * Kt

/-- LK15. The two ranges: moduli `q ≤ x^{θ₀}` by the free middle block (`|f(h/q + k/r)| ≤ qr/(2W)`, `W ≥ x^{3/10}`,
`θ₀ < 3/20`), larger moduli by `TL¹_κ`: the Farey total up to `y = x^θ` is smaller than any power of `log x`. -/
def ItemLK15 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (θ η θ₀ : ℝ), 3 ≤ b → IsDigitWeight b g →
    0 < θ₀ → θ₀ < θ → θ₀ < 3 / 20 → θ < 1 → 0 < η → TL1K b g θ η θ₀ →
    ∀ A : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k < bigB b,
      FareyK b g N ⌊xx b N ^ θ⌋₊ ((k : ℝ) / (bigB b : ℝ)) ≤ 1 / Real.log (xx b N) ^ A

/-- LK17. Facts about the weighted κ-sequence: `0 ≤ a_n ≤ M^m/W` when `0 ≤ g ≤ M`, `a_n ≠ 0` only on κ-palindromes of
`2N + 1` digits coprime to `b³ − b`, `A_q = Σ_{n < x, q ∣ n} a_n`, and `X ≤ 1` for a digit weight. -/
def ItemLK17 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (M : ℝ) (N : ℕ), 3 ≤ b → 1 ≤ N → (∀ a, 0 ≤ g a) → (∀ a, g a ≤ M) →
    (∀ n, 0 ≤ aK b g N n ∧ aK b g N n ≤ M ^ mK N / (WK b N : ℝ) ∧ (aK b g N n ≠ 0 → n ∈ kpiStar b N)) ∧
    (∀ q, AK b g N q = ∑ n ∈ range (b ^ (2 * N + 1)), if q ∣ n then aK b g N n else 0) ∧
    (IsDigitWeight b g → XK b g N ≤ 1)

/-! ## Part QK: squares (Proposition CQ_κ, route E′, no Baier–Zhao) -/

/-- QK01. Reduction (step 1 of CQ_κ). -/
def ItemQK01 : Prop := SqRedKStmt

/-- QK03. Route E′ for κ-palindromes (Parseval modulo `p²`). -/
def ItemQK03 : Prop := SqParsevalKStmt

/-- QK04. Proposition CQ_κ: the prime squares in `(x^{c₀}, x^{c₁}]` carry weight `≤ 2X x^{−c₀} + x^{−η′}`.
Small `p` by the middle block, `p² ∈ (x^{θ₀}, x^θ]` and prime moduli `p > x^{θ₀}` by `TL¹_κ`, large `p²` by the cut
with route E′ (large values) and Lemma 2.8_κ (small values). -/
def ItemQK04 : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (p : ℝ) (H : ℕ) (τ : ℕ → ℝ) (ψ a η θ θ₀ c₀ c₁ : ℝ),
    3 ≤ b → IsDigitWeight b g → 1 / 2 ≤ p → p < 1 → H ≤ b * (b - 1) →
    (∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) →
    0 < τ 0 → τ 0 ≤ (b : ℝ) ^ (-ψ) → trigMass H τ ≤ 1 → mw4 b g ≤ 1 / (b : ℝ) →
    0 < a → 0 < η → 4 * a + η < 3 / 20 →
    c₁ + η < 7 / 20 * ψ + 3 / 10 * p + a * (1 - p) → η < a * (1 - p) →
    0 < c₀ → c₀ < c₁ → c₁ < 1 / 2 → 0 < θ₀ → θ₀ < 3 / 20 → 3 / 10 < θ → c₁ ≤ θ → θ < 1 →
    TL1K b g θ η θ₀ → SqRedKStmt → SqParsevalKStmt → Lemma28KStmt → KmidStmt →
    ∃ η' : ℝ, 0 < η' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      SqK b g N c₀ c₁ ≤ 2 * XK b g N * xx b N ^ (-c₀) + xx b N ^ (-η')

/-! ## All items -/

/-- The sieve items (unchanged statements of `Statements.lean`, now at `R = 2`). -/
def SieveItems : Prop :=
  ItemS01 ∧ ItemS02 ∧ ItemS03 ∧ ItemS04 ∧ ItemS05 ∧ ItemS06 ∧ ItemS07 ∧ ItemS08 ∧ ItemS09 ∧ ItemS10 ∧
  ItemS11 ∧ ItemS12 ∧ ItemS13 ∧ ItemS14 ∧ ItemS15 ∧
  ItemM01 ∧ ItemM02 ∧ ItemM03 ∧ ItemM04 ∧ ItemM05 ∧ ItemM06 ∧ ItemM07 ∧ ItemM08 ∧ ItemM09 ∧ ItemM10 ∧
  ItemM11 ∧ ItemM12 ∧ ItemM13

/-- The κ level and square items. -/
def KItems : Prop :=
  ItemL01 ∧ ItemL02 ∧ ItemL03 ∧ ItemLK01 ∧ ItemLK06 ∧ ItemLK07 ∧ ItemLK08 ∧ ItemLK09 ∧ ItemLKM ∧ ItemLK10 ∧
  ItemLK13 ∧ ItemLK14 ∧ ItemLK15 ∧ ItemLK17 ∧ ItemQK01 ∧ ItemQK03 ∧ ItemQK04

/-- All items of the κ theorem. -/
def AllItemsK : Prop := SieveItems ∧ KItems

end KappaOmega2
