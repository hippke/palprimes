# M07 sub-blueprint: Greaves 1986 Lemma 8, `|M₁ − M₂₃ − M*(y^U)| ≤ εV(y)`

Written 2026-11-24 20:40 CET (`date`). Frozen statement (Statements.lean):
```
ItemM07 : ∀ b, 2 ≤ b → Lemma7Stmt b → ∀ ε > 0, ∃ y₀, ∀ y ≥ y₀, |M1 b y − M23 b y − Mstar b y (y^UU)| ≤ ε·VB b y
```
Verdict: **true as stated** (proof below). No hypothesis of the statement is false (Lemma7Stmt is Greaves' Lemma 7,
item M06). Notation: `g(d) = rhoB b d / d`, `z = y^U`, `P(z) = primorialLt z`, `p(d) = d.minFac`, `ν = ω`,
classes: "−" = even ν, "*" = odd ν ≤ 85 (= 1/mm), "+" = odd ν. `χ = chi y mm`, `χ⁻, χ*` the props of DefsSieve.

## 0. Prefixes (all divisors are squarefree divisors of `P(z)`)
For squarefree `d` and a prime `q ∣ d` put `pre(d, q) = Π_{q' ∣ d, q' ≥ q} q'` (the top prefix ending at `q`).
Lemma P (prefix = divisor form). For a class `C ⊆ ℕ` of values of ν and squarefree `d`:
`(∀ h ∣ d, h ≠ 1, ν(h) ∈ C → h p(h)² < Y)` ⟺ `(∀ prime q ∣ d, ν(pre(d,q)) ∈ C → pre(d,q) q² < Y)`.
Proof. ⇒: `pre(d,q) ∣ d`, `p(pre(d,q)) = q`. ⇐: given `h`, `j = ν(h)`, take the prime `q ∣ d` with `ν(pre(d,q)) = j`.
(i) `p(h) ≤ q`: otherwise every prime of `h` is `> q`, so `h ∣ pre(d,q)/q`, `j ≤ j − 1`. (ii) `h ≤ pre(d,q)`: split
`h = h_hi h_lo` (primes `≥ q` / `< q`), `pre(d,q) = h_hi r`, `ν(r) = ν(h_lo)`, every prime of `r` is `≥ q`, of `h_lo` `< q`,
so `h_lo ≤ r`. Hence `h p(h)² ≤ pre(d,q) q² < Y`. ∎
Consequences: `χ(d) = χ⁻(d) ∧ χ*(d)` (definitional: Even ∨ ≤85 = Even ∨ (Odd ∧ ≤85)); all three are divisor-closed.

## 1. Exact identity (Greaves (4.9) = (4.10))
Claim E. For every `y > 0`: `M1 − Mstar(z) = Σ_{δ ∈ Dset y z mm} φ(δ) g(δ) T⁺(y/δ, p(δ))`, `T⁺(Y,w) = Tpm b true Y w`.
Proof. Write `φ(d) = W1 − Σ_{p∣d} w(p)`. Then
`M1 − M* = W1 Σ_d μg(χ − χ⁻) − Σ_d μg Σ_{p∣d} w(p)(χ(d) − χ⁻(d)χ*(d₁(d,p)))`.
(a) Since `χ*(d) ⇒ χ*(d₁)` (`d₁ ∣ d`), `χ(d) − χ⁻(d)χ*(d₁) = −χ⁻(d)[¬χ*(d) ∧ χ*(d₁(d,p))]` and `χ − χ⁻ = −χ⁻[¬χ*]`.
(b) Decomposition. For `d` with `χ⁻(d)`, `¬χ*(d)` let `q` be the largest prime of `d` with `pre(d,q)` violating
(odd ν ≤ 85, `pre q² ≥ y`), `δ = pre(d,q)`, `t = d/δ` (`t ∣ P(p(δ))`). Then `δ ∈ D`: `χ(δ/p(δ)) = 1` (its prefixes are
the shorter prefixes of `d`: odd ones fine by maximality of `q`, even ones by `χ⁻(d)`), `χ(δ) = 0`, ν(δ) odd ≤ 85,
`δ ≠ 1`. Conversely for `δ ∈ D`, `t ∣ P(p(δ))`: the prefixes of `δt` are the prefixes of `δ` and the `δ·pre(t, q)`;
`χ⁻(δt) ⟺ χ⁺_{y/δ}(t)` (even prefix `δ t'` ⟺ ν(t') odd, condition `δ t' p(t')² < y ⟺ t' p(t')² < y/δ`), and the
largest violating prefix of `δt` is `δ`. So `(δ, t) ↦ δt` is a bijection from `{δ ∈ D, t ∣ P(p(δ)), χ⁺_{y/δ}(t)}` onto
`{d ∣ P(z) : χ⁻(d), ¬χ*(d)}`.
(c) `χ*(d₁(d,p))` for `p ∣ d` holds iff `p ∣ δ` (`d₁(d,p)` is the prefix above `p`; it contains `δ` iff `p < p(δ)`).
(d) Multiplicativity `μ(δt) = μ(δ)μ(t) = −μ(t)`, `g(δt) = g(δ)g(t)`. Collect:
`M1 − M* = Σ_δ g(δ)T⁺(y/δ,p(δ)) (W1 − Σ_{p∣δ} w(p))`. ∎ (Numerically confirmed by the lead to 10⁻¹⁴, logs/sanity_g4_identity.log.)

## 2. Facts on `D` (S13-type, proved inside the item)
For `δ ∈ D`, `p = p(δ)`, `δ' = δ/p`, `y > 1`:
(D1) `y ≤ δ p²` (the violating divisor `h` of `δ` has `p(δ) ∣ h`, else `h ∣ δ'`; so `p(h) = p`, `h ≤ δ`).
(D2) For every `h ∣ δ'`: `y/h ≥ y^{(2/3)^{ν(h)}}` (induction on `ν(h)`, `h = h'p(h)`: `h p(h)² < y` gives `p(h)³ < y/h'`,
so `y/h > (y/h')^{2/3}`); `ν(δ') ≤ 84`.
(D3) `y/δ ≥ y^{c₂}`, `c₂ = (1/2)(2/3)^{84}`: if `δ' = 1`, `y/δ = y/p > y^{1−U}`; else `p < p(δ')`, `δ' p(δ')² < y` gives
`p² < y/δ'`, so `y/δ > (y/δ')^{1/2}`.
(D4) every prime of `δ` is `≥ p ≥ (y/δ)^{1/2} ≥ y^{c₂/2}` (from D1).
(D5) `|φ(δ)| ≤ 86 W1` (`0 ≤ w ≤ W1`, ν(δ) ≤ 85).

## 3. Analytic part
(A1) Lemma 7 at `Y = y/δ`, `s = log Y / log p`: `0 < s ≤ 3` by (D1)–(D3) (`p³ ≥ p² ≥ Y`, `Y > 1`, `p ≥ 2`),
`Y^{1/s} = p`. So for `y^{c₂} ≥ y₀(ε')`: `|T⁺(y/δ,p(δ)) − e^γ V(√(y/δ))| ≤ ε' V(√(y/δ))`.
(A2) `V(√(y/δ)) ≤ C₁ V(y)` from VB_log_bounds (`V(w) log w ≍ κ_B` for `w ≥ w₀`), `√(y/δ) ≥ y^{c₂/2}`: `C₁ = 2·2/c₂·(1+η)/(1−η)`.
(A3) `Σ_{δ∈D} g(δ) ≤ Π_{y^{c₂/2} ≤ p < z}(1 + g(p)) ≤ Π (1 − g(p))^{−1} = V(y^{c₂/2})/V(z) ≤ C₂` (D4, VB_log_bounds).
(A4) By §1, `M1 − M23 − M* = Σ_δ φ(δ)g(δ)(T⁺(y/δ,p(δ)) − e^γ V(√(y/δ)))`, so
`|…| ≤ ε'·86W1·C₁C₂·V(y)`. Take `ε' = ε/(86 W1 C₁ C₂ + 1)`, `y₀ = max(w₀^{2/c₂}, y₀(ε')^{1/c₂}, 2)`. ∎

## 4. Lean layout (planned)
`M07_Prefix.lean` (Lemma P, decomposition bijection), `M07_Exact.lean` (Claim E as a Finset identity over
`(primorialLt z).divisors`, via `Finset.sum_bij`/`sum_sigma`), `M07_D.lean` (D1–D5), `M07.lean` (A1–A4).
Estimated 1500–2000 lines. Reusable: Palprimes `MT.VB_log_bounds`, `E1.VB_pos'`, rpow facts; M08's divisor-sum
helpers (copy with renamed declarations).

## 5. Status
See reports/M07.md.
