import Palprimes.MainTerm.E1
import Palprimes.Greaves.Lemma31

/-!
# Ω ≤ 2 for κ-palindromes: definitions, part 1 (sieve parameters; Omega3's palindrome sequence, unused)

KappaOmega2 NOTE (omega-2, 2026-11-25). This file is the Omega3 file with the sieve constants changed to Greaves 1986 at `R = 2`
(`θ = 103/200`, `U = 99/103`, `V = m = 2/103`, `k² = 582/103`, no Σ₂ bands). Docstrings that still mention `θ = 0.340`,
`R = 3`, bands or `b ≥ 5` describe the Omega3 original; the definitions are those stated. The κ theorem uses only the
sieve part of this file and the Fejér items; its own sequence, level and squares are in `DefsK.lean`, `StatementsK.lean`.


Definitions only, no theorems. Sources: `r243_dossier_v5/DOSSIER_v5.md` §2, §3, `r238_weighted_chain/proof.md`,
`lean/omega3_p0/certs/NOTES.md`, `lean/omega3_p0/squares/NOTES.md`. Notation of the blueprint (`BLUEPRINT.md` §1).

Conventions.
* A digit weight is a function `g : ℕ → ℝ` read on the digits `0 … b − 1`.
* `x = b^{2N+1}` is `xx b N`; positions `k = 0 … N` carry `c_k = cK b N k` (Palprimes).
* `Gg b g t = Σ_{a<b} g(a) e(at)`, `fg b g N α = Π_{k ≤ N} Gg b g (c_k α)`.
* `AW b g N q = Σ_e w(e) [(n(e), b³ − b) = 1, q ∣ n(e)]` with `w(e) = Π_k g(e_k)`, `XW = AW 1`.
* The trigonometric majorants are even cosine polynomials `τ₀ + 2 Σ_{1≤u≤H} τ_u cos 2πut`.
-/

set_option linter.style.longLine false

open Finset Real

namespace KappaOmega2

open Palprimes

/-! ## Parameters of the route (Greaves 1986, `R = 2`, `θ = 103/200`, no bands) -/

/-- Sieve level `θ = 103/200`, `y = x^θ`. -/
noncomputable def thS : ℝ := 103 / 200
/-- Greaves' `U = 99/103 = (2/θ − 1)/3` (kink `V + 2U = 1/θ`, `2V + U = 1`). -/
noncomputable def UU : ℝ := 99 / 103
/-- `V = m = (1 − U)/2 = 2/103`. -/
noncomputable def mm : ℝ := 2 / 103
/-- `W(1) = U − V = 97/103`. -/
noncomputable def W1 : ℝ := 97 / 103
/-- The λ² line `k² = 9(U − 1/3) = 582/103` (Greaves' envelope, no bands). -/
noncomputable def kSq : ℝ := 582 / 103
/-- `c₀ = θ m = 1/100` (smallest prime factor exponent, lower end of the square range). -/
noncomputable def c0 : ℝ := 1 / 100
/-- `c₁ = θ U = 99/200` (upper end of the square range). -/
noncomputable def c1 : ℝ := 99 / 200
/-- TL¹ window start `θ₀ = 3/10` (Lemma SS allows any `θ₀ < θ`). -/
noncomputable def th0 : ℝ := 3 / 10

/-- `x = b^{2N+1}`. -/
noncomputable def xx (b N : ℕ) : ℝ := (b : ℝ) ^ (2 * N + 1)

/-! ## Digit weights -/

/-- A digit weight on `0 … b − 1`: nonnegative with total mass `1`. -/
def IsDigitWeight (b : ℕ) (g : ℕ → ℝ) : Prop := (∀ a, 0 ≤ g a) ∧ ∑ a ∈ range b, g a = 1

/-- Fejér digit weight of order `m` (verbatim `Pilot.fejerW`): `min(a+1, 2m−1−a)/m²` for `a ≤ 2m − 2`. -/
def fejerW (m a : ℕ) : ℚ :=
  if a + 1 < 2 * m then (min (a + 1) (2 * m - 1 - a) : ℕ) / ((m : ℚ) ^ 2) else 0

/-- Fejér kernel (verbatim `Pilot.fejerK`): `F_m(y) = (1/m) Σ_{|k|<m} (1 − |k|/m) cos 2πky`. -/
noncomputable def fejerK (m : ℕ) (y : ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ k ∈ Finset.Ioo (-(m : ℤ)) m,
    (1 - (|k| : ℝ) / m) * Real.cos (2 * Real.pi * k * y)

/-- `m_b = ⌊(b + 1)/2⌋`, the order of the Fejér weight of base `b`. -/
def mB (b : ℕ) : ℕ := (b + 1) / 2

/-- r238's weight of record for `b = 6`: `(9, 17, 24, 24, 17, 9)/100`. -/
def g6list : List ℚ := [9 / 100, 17 / 100, 24 / 100, 24 / 100, 17 / 100, 9 / 100]

/-- r238's weight of record for `b = 8` (0.4 Fejér + 0.6 opt, `b8_mix0.4_H14.json`). -/
def g8list : List ℚ :=
  [336527 / 5242880, 627976 / 5242880, 867075 / 5242880, 1052006 / 5242880,
    920934 / 5242880, 736003 / 5242880, 496904 / 5242880, 205455 / 5242880]

/-- The digit weight of record: Fejér of order `m_b` for `b ∉ {6, 8}`, r238's weights for `b = 6, 8`. -/
def recG (b a : ℕ) : ℚ :=
  if b = 6 then g6list.getD a 0 else if b = 8 then g8list.getD a 0 else fejerW (mB b) a

/-- `recG` as a real function. -/
noncomputable def recGR (b : ℕ) (a : ℕ) : ℝ := (recG b a : ℝ)

/-! ## Exponential sums of the weighted sequence -/

/-- `G_g(t) = Σ_{a<b} g(a) e(at)`. -/
noncomputable def Gg (b : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℂ := ∑ a ∈ range b, (g a : ℂ) * ee (a * t)

/-- `f_g(α) = Π_{k ≤ N} G_g(c_k α)`. -/
noncomputable def fg (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∏ k ∈ range (N + 1), Gg b g ((cK b N k : ℝ) * α)

/-- `g_J(α) = Π_{k ∈ J} G_g(c_k α)` for a set of positions `J`. -/
noncomputable def gJ (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (J : Finset ℕ) (α : ℝ) : ℂ :=
  ∏ k ∈ J, Gg b g ((cK b N k : ℝ) * α)

/-- `m_w(4) = Σ_s ((g ∗ g)(s))² = ∫₀¹ |G_g|⁴`. -/
noncomputable def mw4 (b : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ s ∈ range (2 * b - 1),
    (∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0) ^ 2

/-! ## The weighted sieve sequence -/

/-- Weight of a digit string, `w(e) = Π_{k ≤ N} g(e_k)`. -/
noncomputable def wDig (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (d : DigVec b N) : ℝ := ∏ k : Fin (N + 1), g (d k)

/-- `a_n = Σ_{e : n(e) = n} w(e) [(n, b³ − b) = 1]` (at most one `e` by injectivity). -/
noncomputable def aW (b : ℕ) (g : ℕ → ℝ) (N n : ℕ) : ℝ :=
  open Classical in
  ∑ d : DigVec b N, if palVal b N d = n ∧ Nat.Coprime n (bigB b) then wDig b g N d else 0

/-- `A^w_q = Σ_{q ∣ n} a_n`, written over digit strings. -/
noncomputable def AW (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) : ℝ :=
  open Classical in
  ∑ d : DigVec b N, if Nat.Coprime (palVal b N d) (bigB b) ∧ q ∣ palVal b N d then wDig b g N d else 0

/-- `X_w = Σ_n a_n`. -/
noncomputable def XW (b : ℕ) (g : ℕ → ℝ) (N : ℕ) : ℝ := AW b g N 1

/-- Sieve density `γ(d) = 1` if `(d, b³ − b) = 1`, else `0` (multiplicative on squarefree `d`). -/
noncomputable def rhoB (b d : ℕ) : ℝ := open Classical in if Nat.Coprime d (bigB b) then 1 else 0

/-- `R_w(d) = A^w_d − X_w γ(d)/d`. -/
noncomputable def RW (b : ℕ) (g : ℕ → ℝ) (N d : ℕ) : ℝ := AW b g N d - XW b g N * rhoB b d / d

/-- The level sum `Σ_{d ≤ D, d squarefree} 3^{ω(d)} |R_w(d)|`. -/
noncomputable def levelSum (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) : ℝ :=
  open Classical in
  ∑ d ∈ (Icc 1 D).filter Squarefree,
    (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d * |RW b g N d|

/-- The square sum `Σ_{x^{lo} < p ≤ x^{hi}, p prime} A^w_{p²}`. -/
noncomputable def SqW (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (lo hi : ℝ) : ℝ :=
  open Classical in
  ∑ p ∈ (Icc 1 ⌊xx b N ^ hi⌋₊).filter (fun p : ℕ => p.Prime ∧ xx b N ^ lo < (p : ℝ)), AW b g N (p ^ 2)

/-! ## Trigonometric majorants -/

/-- `T(t) = τ₀ + 2 Σ_{1 ≤ u ≤ H} τ_u cos 2πut`. -/
noncomputable def trigEval (H : ℕ) (τ : ℕ → ℝ) (t : ℝ) : ℝ :=
  τ 0 + 2 * ∑ u ∈ Icc 1 H, τ u * Real.cos (2 * Real.pi * u * t)

/-- `A(T) = |τ₀| + 2 Σ_{1 ≤ u ≤ H} |τ_u|` (sum of the absolute Fourier coefficients). -/
noncomputable def trigMass (H : ℕ) (τ : ℕ → ℝ) : ℝ := |τ 0| + 2 * ∑ u ∈ Icc 1 H, |τ u|

/-- The exponent of record: `p_T = 1023/1024` for `b ≤ 15`, `1 − 1/b²` for `b ≥ 16`. -/
noncomputable def recP (b : ℕ) : ℝ := if b ≤ 15 then 1023 / 1024 else 1 - 1 / (b : ℝ) ^ 2

/-- Coefficients of `F_m` in the form `τ₀ + 2 Σ τ_u cos`: `τ₀ = 1/m`, `τ_u = (m − u)/m²`. -/
noncomputable def fejTau (m u : ℕ) : ℝ :=
  if u = 0 then 1 / (m : ℝ) else if u < m then ((m : ℝ) - u) / (m : ℝ) ^ 2 else 0

/-- The exact LP majorant `P₆ ≥ |G_{g₆}|` (dyadic rationals of `amgm_b6_symA_H10_P.json`). -/
def P6list : List ℚ :=
  [1321873323313001 / 4503599627370496, 7222560589874485 / 36028797018963968,
    8214455710924505 / 72057594037927936, 2794269570583501 / 72057594037927936]

/-- The exact LP majorant `P₈ ≥ |G_{g₈}|` (dyadic rationals of `amgm_b8_mix0.4_H14_P.json`). -/
def P8list : List ℚ :=
  [8383891917856039 / 36028797018963968, 1576219461424283 / 9007199254740992,
    4168387876891915 / 36028797018963968, 4833877587123735 / 72057594037927936,
    3409766388037827 / 144115188075855872, 5108764914694413 / 2305843009213693952]

/-- Degree of the majorant of record. -/
def recH (b : ℕ) : ℕ := if b = 6 then 3 else if b = 8 then 5 else mB b - 1

/-- `P = F_m` (Fejér) or the LP polynomial (`b = 6, 8`), coefficients in the `τ₀ + 2Σ τ_u cos` form. -/
noncomputable def recPoly (b u : ℕ) : ℝ :=
  if b = 6 then (P6list.getD u 0 : ℝ) else if b = 8 then (P8list.getD u 0 : ℝ) else fejTau (mB b) u

/-- The majorant of record `T = (1 − p) + p P` (Bernoulli/AM-GM, no cells for Fejér). -/
noncomputable def recTau (b u : ℕ) : ℝ := (if u = 0 then 1 - recP b else 0) + recP b * recPoly b u

/-! ## TL¹ for weighted sequences and Farey sums -/

/-- `L1*_w(d, β) = Σ*_{h mod d} |f_g(h/d + β)|`. -/
noncomputable def L1farey (b : ℕ) (g : ℕ → ℝ) (N d : ℕ) (β : ℝ) : ℝ :=
  ∑ h ∈ redRes d, ‖fg b g N ((h : ℝ) / d + β)‖

/-- The dyadic block `Σ_{d ∈ [D, 2D), (d, b) = 1} L1*_w(d, β)`. -/
noncomputable def blockL1 (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (β : ℝ) : ℝ :=
  ∑ d ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), L1farey b g N d β

/-- `TL¹_w(θ, κ, θ₀)` (dossier v5 §2.5): for every `ε > 0` and `N ≥ N₀(ε)`, every dyadic `D` with
`x^{θ₀} < D ≤ x^θ` and every real `β`, the block is `≤ D x^{−κ+ε}`. -/
def TL1w (b : ℕ) (g : ℕ → ℝ) (θ κ θ₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D : ℕ, (∃ j : ℕ, D = 2 ^ j) →
    xx b N ^ θ₀ < (D : ℝ) → (D : ℝ) ≤ xx b N ^ θ → ∀ β : ℝ,
      blockL1 b g N D β ≤ (D : ℝ) * xx b N ^ (-κ + ε)

/-- The `3^ω`-weighted Farey total `Σ_{2 ≤ q ≤ D, (q, b³−b) = 1} 3^{ω(q)} q⁻¹ L1*_w(q, β)`. -/
noncomputable def FareyW (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (β : ℝ) : ℝ :=
  ∑ q ∈ (Icc 2 D).filter (fun q => Nat.Coprime q (bigB b)),
    (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q / q * L1farey b g N q β

/-! ## Named statements used as explicit hypotheses of items (definitions of `Prop`s, nothing assumed) -/

/-- Bernoulli's inequality (verbatim `Pilot.ItemE`). -/
def BernoulliStmt : Prop :=
  ∀ t p : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ p → p ≤ 1 → t ^ p ≤ 1 - p + p * t

/-- `|G_g| = F_m` for the Fejér weight (`Pilot.ItemM` with `Pilot.e = ee`). -/
def FejerAbsStmt : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ y : ℝ,
    ‖∑ a ∈ Finset.range (2 * m - 1), ((fejerW m a : ℚ) : ℂ) * ee (a * y)‖ = fejerK m y

/-- Fejér fourth moment in closed form (verbatim `Pilot.ItemN`). -/
def FejerM4Stmt : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∑ s ∈ Finset.range (4 * m),
        (∑ i ∈ Finset.range (s + 1), fejerW m i * fejerW m (s - i)) ^ 2 =
      ((151 * (m : ℚ) ^ 6 + 70 * (m : ℚ) ^ 4 + 49 * (m : ℚ) ^ 2 + 45) / (315 * (m : ℚ) ^ 7))

/-- Exact LP majorant for `b = 6`: `|G_{g₆}(t)| ≤ P₆(t)` on `ℝ`. -/
def Cert6Stmt : Prop :=
  ∀ t : ℝ, ‖Gg 6 (recGR 6) t‖ ≤ trigEval 3 (fun u => (P6list.getD u 0 : ℝ)) t

/-- Exact LP majorant for `b = 8`: `|G_{g₈}(t)| ≤ P₈(t)` on `ℝ`. -/
def Cert8Stmt : Prop :=
  ∀ t : ℝ, ‖Gg 8 (recGR 8) t‖ ≤ trigEval 5 (fun u => (P8list.getD u 0 : ℝ)) t

/-- The record majorant of base `b`: `T ≥ |G_g|^{p_T}` on `ℝ`. -/
def RecMajStmt (b : ℕ) : Prop :=
  ∀ t : ℝ, ‖Gg b (recGR b) t‖ ^ recP b ≤ trigEval (recH b) (recTau b) t

/-- Lemma 2.8 (weight free): averaged `T`-products over all residues of a set of moduli. With
`T_K(α) = Π_{k∈K} T(c_k α)`, `K ⊆ [0, N)`, `H ≤ 2b − 2` (Proposition S (a)) and `Td` bounding the number of
moduli dividing any nonzero integer `|w| ≤ 2H b^{2N+1}`. -/
def Lemma28Stmt : Prop :=
  ∀ (b H N : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) (Qs : Finset ℕ) (β Td : ℝ), 2 ≤ b → H ≤ 2 * b - 2 →
    K ⊆ range N → (∀ q ∈ Qs, 1 ≤ q) → 0 ≤ Td →
    (∀ w : ℤ, w ≠ 0 → |w| ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) →
      ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)).card : ℝ) ≤ Td) →
    ∑ q ∈ Qs, ∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) ≤
      (∑ q ∈ Qs, (q : ℝ)) * τ 0 ^ K.card + ((Qs.sup id : ℕ) : ℝ) * Td * trigMass H τ ^ K.card

/-- Lemma 2.9_w (inner large sieve with the exact fourth moment): for `J = [N − j, N)`, `1 ≤ j ≤ N`,
`Σ_{d ∈ [D, 2D), (d, b) = 1} Σ*_h |g_J(h/d + β)|⁴ ≤ 6(4D² + 2b·b^{2j}) m_w(4)^j` (factor 6: fix of 2026-11-24, fits Palprimes `large_sieve`). -/
def Lemma29wStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N j D : ℕ) (β : ℝ), 2 ≤ b → (∀ a, 0 ≤ g a) → 1 ≤ j → j ≤ N → 1 ≤ D →
    ∑ d ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b), ∑ h ∈ redRes d,
        ‖gJ b g N (Ico (N - j) N) ((h : ℝ) / d + β)‖ ^ 4 ≤
      6 * (4 * (D : ℝ) ^ 2 + 2 * b * (b : ℝ) ^ (2 * j)) * mw4 b g ^ j

/-- Lemma K (weighted Col bound), dossier v5 §2.4: for `α = h/q + k/(b³ − b)` with `q ≥ 2`, `(q, h(b³ − b)) = 1`
and `2 ≤ M ≤ N − 1`, `Π_{1≤n≤M} |G_g(c_n α)| ≤ exp(−g(0)g(1)⌊(M − 1)/L_q⌋/(b⁴(b+1)²))`, `L_q = max(1, ⌊log_b q⌋)`. -/
def LemmaKStmt (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ (N q M : ℕ) (h k : ℤ), 2 ≤ q → Nat.Coprime q (h.natAbs * bigB b) → 2 ≤ M → M + 1 ≤ N →
    ∏ n ∈ Icc 1 M, ‖Gg b g ((cK b N n : ℝ) * ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ)))‖ ≤
      Real.exp (-(g 0 * g 1) * (((M - 1) / max 1 (Nat.log b q) : ℕ) : ℝ) /
        ((b : ℝ) ^ 4 * ((b : ℝ) + 1) ^ 2))

/-- Conclusion of Lemma SS: for every `ε > 0` there is `D₀` such that for every `N`, every dyadic
`D₀ ≤ D ≤ x^θ` and every `β`, the block is `≤ D · D^{−κ/θ + ε}`. -/
def SSStmt (b : ℕ) (g : ℕ → ℝ) (θ κ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℝ, ∀ N D : ℕ, (∃ j : ℕ, D = 2 ^ j) → D₀ ≤ (D : ℝ) →
    (D : ℝ) ≤ xx b N ^ θ → ∀ β : ℝ, blockL1 b g N D β ≤ (D : ℝ) * (D : ℝ) ^ (-κ / θ + ε)

/-- Step 1 of Proposition CQ (reduction): for a prime `p ∤ b³ − b`,
`|A^w_{p²} − X_w/p²| ≤ τ(r) Σ_{k<r} p^{−2}(Σ_{h<p², p∤h} |f(h/p² + k/r)| + Σ_{0<h<p} |f(h/p + k/r)|)`. -/
def SqRedStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N p : ℕ), 2 ≤ b → p.Prime → ¬ p ∣ bigB b →
    |AW b g N (p ^ 2) - XW b g N / (p : ℝ) ^ 2| ≤
      ((bigB b).divisors.card : ℝ) * ∑ k ∈ range (bigB b), ((p : ℝ) ^ 2)⁻¹ *
        ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fg b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fg b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖)

/-- Steps 3 of Proposition CQ ((3.1), (3.2)): `T_K` summed over square and prime moduli. For
`K ⊆ [1, N)`, `H ≤ 2b − 2`, `τ₀ ≥ 0`, `Q ≥ 2` and primes `p ∈ [Q, 2Q)`:
`Σ_p Σ_{h<p²} T_K(h/p² + β) ≤ 4Q³τ₀^{|K|} + 4Q² ℓ A^{|K|}` and `Σ_p Σ_{h<p} T_K(h/p + β) ≤ 4Q²τ₀^{|K|} + 2Q ℓ A^{|K|}`,
`ℓ = log(2H b^{2N+1})/log Q`. -/
def SqDiagStmt : Prop :=
  ∀ (b H N Q : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) (β : ℝ), 2 ≤ b → H ≤ 2 * b - 2 → 0 ≤ τ 0 →
    K ⊆ Ico 1 N → 2 ≤ Q →
    (∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, ∑ h ∈ range (p ^ 2),
        ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / (p ^ 2 : ℕ) + β)) ≤
      4 * (Q : ℝ) ^ 3 * τ 0 ^ K.card +
        4 * (Q : ℝ) ^ 2 * (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) * trigMass H τ ^ K.card) ∧
    (∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, ∑ h ∈ range p,
        ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / p + β)) ≤
      4 * (Q : ℝ) ^ 2 * τ 0 ^ K.card +
        2 * (Q : ℝ) * (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) * trigMass H τ ^ K.card)

/-- Route E′ (Parseval modulo `p²`): for `J = [N − j, N)`, `1 ≤ j < N`, a prime `p ∤ b` with `2b^{2j+1} ≤ p²`
and any real digit weight, `Σ_{h<p²} |g_J(h/p² + β)|⁴ = p² m_w(4)^j`. -/
def SqParsevalStmt : Prop :=
  ∀ (b : ℕ) (g : ℕ → ℝ) (N j p : ℕ) (β : ℝ), 2 ≤ b → 1 ≤ j → j < N → p.Prime → ¬ p ∣ b →
    2 * b ^ (2 * j + 1) ≤ p ^ 2 →
    ∑ h ∈ range (p ^ 2), ‖gJ b g N (Ico (N - j) N) ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 =
      (p : ℝ) ^ 2 * mw4 b g ^ j

end KappaOmega2
