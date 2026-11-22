import Mathlib

/-! # Greaves §4–§5: the continuous objects (definitions only)

* `Iint t s`: Greaves' `I_t(s) = ∫_{1<u_t<⋯<u_1, Σu = s} du_1⋯du_{t-1}/(u_1⋯u_t)` (Lemma 5.1),
  written as a Lebesgue integral over `w = (u_1, …, u_{t-1}) ∈ ℝ^{t-1}` with `u_t = s − Σ w`;
* `Fjr s = 2e^γ Σ_{t odd} I_t(s)`, `fjr s = 2e^γ Σ_{t even} I_t(s)`: the Jurkat–Richert functions
  (Lemma 5.1; the sums are finite since `I_t(s) = 0` for `t ≥ s`);
* `kr r x`: Greaves (4.15) at `s = 1`, `k_r(x, 1, G_r)` with `G_r = F` (`r` odd), `f` (`r` even):
  `∫_{x<x_{r-1}<⋯<x_1, Rosser} G_r((1 − x − Σ x_i)/x) Π dx_i/x_i` over `v = (x_1, …, x_{r-1})`;
* `hk k x`: Greaves (5.2)/(5.3) at `s = 1`, `h_{2k}(x, 1)`.
No theorems here. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real

namespace Palprimes.MT

/-- Last coordinate of the `I_t` chain: `u_t = s − Σ w`. -/
noncomputable def lastU {n : ℕ} (s : ℝ) (w : Fin n → ℝ) : ℝ := s - ∑ i, w i

/-- The region of `I_t`: `1 < u_t < u_{t-1} < ⋯ < u_1`, here `w = (u_1, …, u_{t-1})`. -/
def IRegion (n : ℕ) (s : ℝ) (w : Fin n → ℝ) : Prop :=
  StrictAnti w ∧ (∀ i, 1 < w i) ∧ 1 < lastU s w ∧ (∀ i, lastU s w < w i)

/-- Greaves' `I_t(s)` (`t ≥ 1`; `I_0 = 0`). -/
noncomputable def Iint (t : ℕ) (s : ℝ) : ℝ :=
  open Classical in
  if t = 0 then 0 else
    ∫ w : Fin (t - 1) → ℝ, if IRegion (t - 1) s w then 1 / ((∏ i, w i) * lastU s w) else 0

/-- Jurkat–Richert `F(s) = 2e^γ Σ_{t odd, t ≤ ⌊s⌋} I_t(s)` (Lemma 5.1). -/
noncomputable def Fjr (s : ℝ) : ℝ :=
  2 * Real.exp Real.eulerMascheroniConstant *
    ∑ t ∈ (Finset.range (⌊s⌋₊ + 1)).filter Odd, Iint t s

/-- Jurkat–Richert `f(s) = 2e^γ Σ_{t even, t ≥ 2, t ≤ ⌊s⌋} I_t(s)` (Lemma 5.1). -/
noncomputable def fjr (s : ℝ) : ℝ :=
  2 * Real.exp Real.eulerMascheroniConstant *
    ∑ t ∈ (Finset.range (⌊s⌋₊ + 1)).filter (fun t => Even t ∧ 2 ≤ t), Iint t s

/-- `G_r = F` for `r` odd, `f` for `r` even (Greaves' `G^{(−)^r}`, parity as in Lemma 5.2). -/
noncomputable def Gr (r : ℕ) (s : ℝ) : ℝ := if Odd r then Fjr s else fjr s

/-- The chain `x_1 > ⋯ > x_{r-1} > x_r = x` read from `v = (x_1, …, x_{r-1})`. -/
noncomputable def chainX {n : ℕ} (x : ℝ) (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then v ⟨i, h⟩ else x

/-- Rosser's lower-bound conditions on the chain of length `r = n + 1`:
`x_1 + ⋯ + x_{2j-1} + 3 x_{2j} ≤ 1` for `2 ≤ 2j ≤ r` (positions counted from `1`). -/
def RosserX {n : ℕ} (x : ℝ) (v : Fin n → ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → 2 * j ≤ n + 1 →
    (∑ i ∈ Finset.range (2 * j - 1), chainX x v i) + 3 * chainX x v (2 * j - 1) ≤ 1

/-- The region of `k_r(x, 1, ·)`: `x < x_{r-1} < ⋯ < x_1` and Rosser. -/
def KRegion (n : ℕ) (x : ℝ) (v : Fin n → ℝ) : Prop :=
  StrictAnti v ∧ (∀ i, x < v i) ∧ RosserX x v

/-- Greaves' `k_r(x, 1, G_r)` (4.15), `r ≥ 1`. -/
noncomputable def kr (r : ℕ) (x : ℝ) : ℝ :=
  open Classical in
  if r = 0 then 0 else
    ∫ v : Fin (r - 1) → ℝ,
      if KRegion (r - 1) x v then Gr r ((1 - x - ∑ i, v i) / x) / (∏ i, v i) else 0

/-- The region `𝓡_{2k}` of (5.3) at `s = 1`, `v = (x_1, …, x_{2k})`, `u = 1 − x − Σ v`. -/
def HRegion (k : ℕ) (x : ℝ) (v : Fin (2 * k) → ℝ) : Prop :=
  StrictAnti v ∧ (∀ i, x < v i) ∧ (∀ i, v i < 1) ∧
  (∀ j : ℕ, 1 ≤ j → j < k →
    (∑ i ∈ Finset.range (2 * j - 1), chainX x v i) + 3 * chainX x v (2 * j - 1) ≤ 1) ∧
  1 < (∑ i ∈ Finset.range (2 * k - 1), chainX x v i) + 3 * chainX x v (2 * k - 1) ∧
  chainX x v (2 * k - 1) < 1 - x - ∑ i, v i

/-- Greaves' `h_{2k}(x, 1)` (5.2). -/
noncomputable def hk (k : ℕ) (x : ℝ) : ℝ :=
  open Classical in
  ∫ v : Fin (2 * k) → ℝ,
    if HRegion k x v then 1 / ((∏ i, v i) * (1 - x - ∑ i, v i)) else 0

end Palprimes.MT
