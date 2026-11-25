import KappaOmega2.Defs

/-!
# Ω ≤ 2 for κ-palindromes: definitions for the κ-sequence, its level and its squares

Definitions only. Source: `omega-2/PROOF_K2.md` (Theorem K2), `omega-2/LEAN_PLAN_K2.md`.
The sieve part (Greaves 1986 at R = 2, θ = 103/200) is in `Defs.lean`, `DefsSieve.lean`.

Setting. `x = b^{2N+1}` (`xx b N`), `m = mK N = ⌊7(2N+1)/20⌋` mirrored outer digit pairs (κ = 7/10),
a free middle block of `ℓ = ellK N = 2N + 1 − 2m` digits, `W = b^ℓ`. A κ-palindrome is
`n = Σ_{k<m} u_k c_k + w b^m` with `c_k = b^k + b^{2N−k}` (`cK b N k`), digits `u_k < b`, `0 ≤ w < W`.
The weighted sequence carries `a = Π_k g(u_k) / W` on `n` coprime to `b³ − b`.
-/

set_option linter.style.longLine false

open Finset Real

namespace KappaOmega2

open Palprimes

/-! ## The κ = 7/10 shape -/

/-- Number of mirrored outer digit pairs, `m = ⌊7(2N+1)/20⌋`. -/
def mK (N : ℕ) : ℕ := 7 * (2 * N + 1) / 20

/-- Length of the free middle block, `ℓ = 2N + 1 − 2m`. -/
def ellK (N : ℕ) : ℕ := 2 * N + 1 - 2 * mK N

/-- `W = b^ℓ`, the number of middle blocks. -/
def WK (b N : ℕ) : ℕ := b ^ ellK N

/-- Outer digit vectors. -/
abbrev KVec (b N : ℕ) := Fin (mK N) → Fin b

/-- `n(u, w) = Σ_{k<m} u_k c_k + w b^m`. -/
def kpalVal (b N : ℕ) (u : KVec b N) (w : ℕ) : ℕ :=
  ∑ k : Fin (mK N), (u k : ℕ) * cK b N k + w * b ^ mK N

/-- The target notion: the first `⌊7L/20⌋` digits mirror the last ones (`L` = number of digits). -/
def IsKappaPal (b n : ℕ) : Prop :=
  ∀ i < 7 * (Nat.digits b n).length / 20,
    (Nat.digits b n).getD i 0 = (Nat.digits b n).getD ((Nat.digits b n).length - 1 - i) 0

instance (b n : ℕ) : Decidable (IsKappaPal b n) := by unfold IsKappaPal; infer_instance

/-- κ-palindromes with exactly `2N + 1` digits, coprime to `b³ − b`. -/
def kpiStar (b N : ℕ) : Finset ℕ :=
  (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (fun n => IsKappaPal b n ∧ Nat.Coprime n (bigB b))

/-! ## Digit weights of record (κ version) -/

/-- Product weight for even `b = 2M`: the convolution of the uniform weights on `[0, M)` and `[0, M]`,
`min(a + 1, M, 2M − a)/(M(M + 1))` for `a < 2M`. -/
def prodW (M a : ℕ) : ℚ :=
  if a < 2 * M then (min (min (a + 1) M) (2 * M - a) : ℕ) / ((M : ℚ) * (M + 1)) else 0

/-- The κ digit weight of record: Fejér of order `(b + 1)/2` for odd `b`, the product weight of order `b/2` for even `b`. -/
def recGK (b a : ℕ) : ℚ := if b % 2 = 1 then fejerW ((b + 1) / 2) a else prodW (b / 2) a

/-- `recGK` as a real function. -/
noncomputable def recGKR (b : ℕ) (a : ℕ) : ℝ := (recGK b a : ℝ)

/-- The exponent `p = 1 − b^{−6}`. -/
noncomputable def recPK (b : ℕ) : ℝ := 1 - 1 / (b : ℝ) ^ 6

/-- Degree of the κ majorant: `M − 1` for odd `b = 2M − 1`, `M` for even `b = 2M`. -/
def recHK (b : ℕ) : ℕ := if b % 2 = 1 then (b + 1) / 2 - 1 else b / 2

/-- Coefficients of `P = F_M` (odd `b`) or `P = (F_M + F_{M+1})/2` (even `b`). -/
noncomputable def recPolyK (b u : ℕ) : ℝ :=
  if b % 2 = 1 then fejTau ((b + 1) / 2) u else (fejTau (b / 2) u + fejTau (b / 2 + 1) u) / 2

/-- The κ majorant `T = (1 − p) + p P`. -/
noncomputable def recTauK (b u : ℕ) : ℝ := (if u = 0 then 1 - recPK b else 0) + recPK b * recPolyK b u

/-! ## Exponential sums -/

/-- The normalised middle kernel `M_W(β) = W⁻¹ Σ_{w<W} e(wβ)`. -/
noncomputable def Mmid (W : ℕ) (β : ℝ) : ℂ := (1 / (W : ℂ)) * ∑ w ∈ range W, ee (w * β)

/-- `∫₀¹ |M_W|⁴ = (2W² + 1)/(3W³)`. -/
noncomputable def mM4 (W : ℕ) : ℝ := (2 * (W : ℝ) ^ 2 + 1) / (3 * (W : ℝ) ^ 3)

/-- `f(α) = Π_{k<m} G_g(c_k α) · M_W(b^m α)`. -/
noncomputable def fK (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  (∏ k ∈ range (mK N), Gg b g ((cK b N k : ℝ) * α)) * Mmid (WK b N) ((b : ℝ) ^ mK N * α)

/-- `g_J(α) = Π_{m−j ≤ k < m} G_g(c_k α) · M_W(b^m α)`, the `j` innermost mirrored positions with the middle. -/
noncomputable def gJK (b : ℕ) (g : ℕ → ℝ) (N j : ℕ) (α : ℝ) : ℂ :=
  (∏ k ∈ Ico (mK N - j) (mK N), Gg b g ((cK b N k : ℝ) * α)) * Mmid (WK b N) ((b : ℝ) ^ mK N * α)

/-! ## The weighted κ-sequence -/

/-- Weight of an outer digit vector, `Π_k g(u_k)`. -/
noncomputable def wK (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (u : KVec b N) : ℝ := ∏ k : Fin (mK N), g (u k)

/-- `a_n = Σ_{(u, w) : n(u,w) = n} Π g(u_k) / W · [(n, b³ − b) = 1]`. -/
noncomputable def aK (b : ℕ) (g : ℕ → ℝ) (N n : ℕ) : ℝ :=
  open Classical in
  ∑ u : KVec b N, ∑ w ∈ range (WK b N),
    if kpalVal b N u w = n ∧ Nat.Coprime n (bigB b) then wK b g N u / (WK b N : ℝ) else 0

/-- `A_q = Σ_{q ∣ n} a_n`, written over `(u, w)`. -/
noncomputable def AK (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) : ℝ :=
  open Classical in
  ∑ u : KVec b N, ∑ w ∈ range (WK b N),
    if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ q ∣ kpalVal b N u w then wK b g N u / (WK b N : ℝ) else 0

/-- `X = Σ_n a_n`. -/
noncomputable def XK (b : ℕ) (g : ℕ → ℝ) (N : ℕ) : ℝ := AK b g N 1

/-- `R(d) = A_d − X γ(d)/d`. -/
noncomputable def RK (b : ℕ) (g : ℕ → ℝ) (N d : ℕ) : ℝ := AK b g N d - XK b g N * rhoB b d / d

/-- The level sum `Σ_{d ≤ D, d squarefree} 3^{ω(d)} |R(d)|`. -/
noncomputable def levelSumK (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) : ℝ :=
  open Classical in
  ∑ d ∈ (Icc 1 D).filter Squarefree, (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RK b g N d|

/-- The square sum `Σ_{x^{lo} < p ≤ x^{hi}, p prime} A_{p²}`. -/
noncomputable def SqK (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (lo hi : ℝ) : ℝ :=
  open Classical in
  ∑ p ∈ (Icc 1 ⌊xx b N ^ hi⌋₊).filter (fun p : ℕ => p.Prime ∧ xx b N ^ lo < (p : ℝ)), AK b g N (p ^ 2)

/-! ## Farey sums and TL¹ -/

/-- `Σ*_{h mod d} |f(h/d + β)|`. -/
noncomputable def L1fareyK (b : ℕ) (g : ℕ → ℝ) (N d : ℕ) (β : ℝ) : ℝ :=
  ∑ h ∈ redRes d, ‖fK b g N ((h : ℝ) / d + β)‖

/-- The dyadic block `Σ_{d ∈ [D, 2D), (d, b) = 1} L1*(d, β)`. -/
noncomputable def blockL1K (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (β : ℝ) : ℝ :=
  ∑ d ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), L1fareyK b g N d β

/-- `TL¹_κ(θ, η, θ₀)`: for every `ε > 0` and large `N`, every dyadic `x^{θ₀} < D ≤ x^θ` and every `β`,
the block is `≤ D x^{−η+ε}`. -/
def TL1K (b : ℕ) (g : ℕ → ℝ) (θ η θ₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : ℕ, (∃ j : ℕ, D = 2 ^ j) →
    xx b N ^ θ₀ < (D : ℝ) → (D : ℝ) ≤ xx b N ^ θ → ∀ β : ℝ,
      blockL1K b g N D β ≤ (D : ℝ) * xx b N ^ (-η + ε)

/-- The `3^ω`-weighted Farey total `Σ_{2 ≤ q ≤ D, (q, b³−b) = 1} 3^{ω(q)} q⁻¹ L1*(q, β)`. -/
noncomputable def FareyK (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (β : ℝ) : ℝ :=
  ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
    (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1fareyK b g N q β

/-! ## Named statements (hypotheses of items; definitions of `Prop`s, nothing assumed) -/

/-- `|G_g| ≤ (F_M + F_{M+1})/2` for the product weight of even `b = 2M`. -/
def ProdAbsStmt : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ y : ℝ,
    ‖∑ a ∈ Finset.range (2 * M), ((prodW M a : ℚ) : ℂ) * ee (a * y)‖ ≤ (fejerK M y + fejerK (M + 1) y) / 2

/-- The κ majorant of record: `T ≥ |G_g|^p` on `ℝ`. -/
def RecMajKStmt (b : ℕ) : Prop :=
  ∀ t : ℝ, ‖Gg b (recGKR b) t‖ ^ recPK b ≤ trigEval (recHK b) (recTauK b) t

/-- The middle majorant: for `W ≥ 16` and `1/2 ≤ p < 1` there is a cosine polynomial `K̃ = κ₀ + 2Σ_{1≤s≤S} κ_s cos 2πsβ`
with `κ_s ≥ 0`, `2S < W`, `K̃ ≥ |M_W|^p`, `κ₀ ≤ 100(1 + log W) W^{−p}` and `Σ|κ| ≤ 100`. -/
def KmidStmt : Prop :=
  ∀ (W : ℕ) (p : ℝ), 16 ≤ W → 1 / 2 ≤ p → p < 1 →
    ∃ (S : ℕ) (κ : ℕ → ℝ), 2 * S < W ∧ (∀ s, 0 ≤ κ s) ∧
      (∀ β : ℝ, ‖Mmid W β‖ ^ p ≤ trigEval S κ β) ∧
      κ 0 ≤ 100 * (1 + Real.log W) * (W : ℝ) ^ (-p) ∧ trigMass S κ ≤ 100

/-- Lemma 2.8_κ (expansion with Lemma R): for `3 ≤ b`, `H ≤ b(b − 1)`, `K ⊆ [1, m)`, a cosine polynomial `κ` of degree
`S ≤ W` in the middle coordinate, and `Td` bounding the number of moduli of `Qs` dividing any nonzero integer
`|v| ≤ (2H + 1) b^{2N+1}`:
`Σ_q Σ_{h<q} Π_{k∈K} T(c_k α) · K̃(b^m α) ≤ (Σ q) τ₀^{|K|} κ₀ + (max q) Td A(T)^{|K|} A(K̃)`, `α = h/q + β`. -/
def Lemma28KStmt : Prop :=
  ∀ (b H N S : ℕ) (τ κ : ℕ → ℝ) (K : Finset ℕ) (Qs : Finset ℕ) (β Td : ℝ), 3 ≤ b → H ≤ b * (b - 1) →
    1 ≤ mK N → K ⊆ Ico 1 (mK N) → S ≤ WK b N → (∀ q ∈ Qs, 1 ≤ q) → 0 ≤ Td →
    (∀ v : ℤ, v ≠ 0 → |v| ≤ (2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) →
      ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ v)).card : ℝ) ≤ Td) →
    ∑ q ∈ Qs, ∑ h ∈ range q,
        (∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
          trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q + β)) ≤
      (∑ q ∈ Qs, (q : ℝ)) * τ 0 ^ K.card * κ 0 +
        ((Qs.sup id : ℕ) : ℝ) * Td * trigMass H τ ^ K.card * trigMass S κ

/-- Lemma 2.9_κ (inner large sieve with the exact fourth moment of the inner block and the middle): for `j < m`,
`Σ_{d ∈ [D, 2D), (d, b) = 1} Σ*_h |g_J(h/d + β)|⁴ ≤ 16(D² + b W b^{2j}) m_w(4)^j m_M(4)`. -/
def Lemma29KStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N j D : ℕ) (β : ℝ), 3 ≤ b → (∀ a, 0 ≤ g a) → j < mK N → 1 ≤ D →
    ∑ d ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), ∑ h ∈ redRes d,
        ‖gJK b g N j ((h : ℝ) / d + β)‖ ^ 4 ≤
      16 * ((D : ℝ) ^ 2 + b * (WK b N : ℝ) * (b : ℝ) ^ (2 * j)) * mw4 b g ^ j * mM4 (WK b N)

/-- Step 1 of Proposition CQ_κ (reduction): for a prime `p ∤ b³ − b`,
`|A_{p²} − X/p²| ≤ τ(r) Σ_{k<r} p^{−2}(Σ_{h<p², p∤h} |f(h/p² + k/r)| + Σ_{0<h<p} |f(h/p + k/r)|)`. -/
def SqRedKStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N p : ℕ), 3 ≤ b → p.Prime → ¬ p ∣ bigB b →
    |AK b g N (p ^ 2) - XK b g N / (p : ℝ) ^ 2| ≤
      ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ((p : ℝ) ^ 2)⁻¹ *
        ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖)

/-- Route E′ for κ-palindromes (Parseval modulo `p²`): for `j < m`, a prime `p ∤ b` with `6 W b^{2j} ≤ p²`,
`Σ_{h<p²} |g_J(h/p² + β)|⁴ = p² m_w(4)^j m_M(4)`. -/
def SqParsevalKStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N j p : ℕ) (β : ℝ), 3 ≤ b → j < mK N → p.Prime → ¬ p ∣ b →
    6 * WK b N * b ^ (2 * j) ≤ p ^ 2 →
    ∑ h ∈ range (p ^ 2), ‖gJK b g N j ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 =
      (p : ℝ) ^ 2 * mw4 b g ^ j * mM4 (WK b N)

end KappaOmega2
