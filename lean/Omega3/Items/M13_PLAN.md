# M13 sub-blueprint: `HTableStmt ξ H → MvalLower ξ H ≤ 𝓜(W)`

Started 2026-11-24 22:20 CET. Statement `ItemM13` exactly as frozen. Verdict: true as stated.

`𝓜(W) − MvalLower = ∫₀^{1/2} W(1/(1−t) − h)/t − ∫₀^{1/2} W/((1−t)t) + Σ_j H_j ∫_{ξ_j}^{ξ_{j+1}} W/t`, so it suffices that
(a) `t ↦ W(t)h(t)/t` is integrable on `[0, 1/2]` (then the first integral splits), and
(b) `∫₀^{1/2} W h/t ≤ Σ_j H_j ∫_{ξ_j}^{ξ_{j+1}} W/t`.

Facts.
1. `W ≥ 0` everywhere on `[0, ∞)`, `W = 0` on `[0, 1/85]`, `W ≤ 1` and `W` is measurable.
2. `h₉₆(i, x) := h86 i x ≥ 0` (integral of a nonnegative function) and `h86 i x = 0` when `(i + 2)x ≥ 1`: on 𝓡_i all
   `v_j > x` and `u = 1 − x − Σ v_j > v_{i−1} > x`, so `1 > (i + 2)x`. Hence `hS ≥ 0`, `hS = 0` on `[1/4, 1/2]`
   (all terms have `i = 2k ≥ 2`), and for `t ≥ 1/85`, `hS t = Σ_{k=1}^{43} h86(2k, t)` (terms with `2k > 85` vanish).
3. Measurability of `t ↦ h86 i t`: the integrand `F(t, v) = 1_{𝓡_i(t)}(v)/(Π v_j · (1 − t − Σ v_j))` is jointly
   measurable (𝓡_i is a finite Boolean combination of strict/non-strict inequalities between continuous functions of
   `(t, v)`), so `t ↦ ∫ F(t, v) dv` is measurable (`StronglyMeasurable.integral_prod_right`).
4. On each cell `[ξ_j, ξ_{j+1}] ⊂ [1/85, 1/4]`: `0 ≤ hS ≤ H_j` (table), so `0 ≤ W h/t ≤ H_j W/t`; on `[0, 1/85]`, `W h/t = 0`;
   on `[1/4, 1/2]`, `W h/t = 0`. Integrability (a) follows (measurable, bounded by `max_j H_j · 85` on `[1/85, 1/4]`, zero
   elsewhere), and (b) from `∫₀^{1/2} = ∫₀^{1/85} + Σ_j ∫_{ξ_j}^{ξ_{j+1}} + ∫_{1/4}^{1/2}` and monotonicity.
