import Palprimes.MainTerm.Comb
import Palprimes.MainTerm.Defs
import Palprimes.Greaves.Sieve
import Palprimes.Defs

/-! # Greaves' Lemma 4.2 as an explicit hypothesis

Density `gB b p = 1/p` for primes `p ∤ b³ − b` (0 otherwise), `V(w) = Π_{p<w} (1 − gB p)`.
`Splus z s`, `Sminus z s`: the Rosser upper/lower sums of level `z` over the primes `< z^{1/s}`
(Greaves (4.1): `S^±(z, s)`; the recursion `Sg` is the same as in the sieve).

`RosserAsymp b` is Greaves' Lemma 4.2 (Iwaniec 1971) for this density, with an `o(1)` error:
`S^+(z,s) = V(z^{1/s})(F(s) + o(1))` uniformly in `1 ≤ s ≤ 9` and `S^-(z,s) = V(z^{1/s})(f(s) + o(1))`
uniformly in `2 ≤ s ≤ 9` (only this range is used; Greaves states it for all `s ≥ 1`, resp. `s ≥ 2`), `F, f` the Jurkat–Richert functions (`Fjr`, `fjr`, defined via Lemma 5.1).
It is a hypothesis of the conditional Ω ≤ 4 theorem, not an axiom.

`Fjr` is defined from `I_t` with the strict condition `1 < u_t`, so `Fjr 1 = 0`, while Greaves'
`F(1) = 2e^γ` (`I_1(1) = 1`). The hypothesis uses `FjrC`, equal to `Fjr` except at `s = 1`, where it is
`2e^γ`; with `Fjr` itself the hypothesis would be false at `s = 1`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

/-- The sieve density of `Π*_b`. -/
noncomputable def gB (b : ℕ) (p : ℕ) : ℝ :=
  open Classical in if p.Prime ∧ Nat.Coprime p (Palprimes.bigB b) then 1 / (p : ℝ) else 0

/-- `V(w) = Π_{p < w} (1 − gB p)`. -/
noncomputable def VB (b : ℕ) (w : ℝ) : ℝ := ∏ p ∈ primesBelow w, (1 - gB b p)

/-- Greaves' `S^+(z, s)`. -/
noncomputable def Splus (b : ℕ) (z s : ℝ) : ℝ := Sg (gB b) true z (toDec (primesBelow (z ^ (1 / s))))

/-- Greaves' `S^-(z, s)`. -/
noncomputable def Sminus (b : ℕ) (z s : ℝ) : ℝ := Sg (gB b) false z (toDec (primesBelow (z ^ (1 / s))))

/-- `F` with the correct value `F(1) = 2e^γ` (Greaves' `F(s) = 2e^γ/s` on `0 < s ≤ 3`). -/
noncomputable def FjrC (s : ℝ) : ℝ := if s = 1 then 2 * Real.exp Real.eulerMascheroniConstant else Fjr s

/-- **Greaves' Lemma 4.2** (Rosser–Iwaniec linear sieve, main terms) for the density `gB b`. -/
def RosserAsymp (b : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z →
    (∀ s : ℝ, 1 ≤ s → s ≤ 9 → |Splus b z s - VB b (z ^ (1 / s)) * FjrC s| ≤ ε * VB b (z ^ (1 / s))) ∧
    (∀ s : ℝ, 2 ≤ s → s ≤ 9 → |Sminus b z s - VB b (z ^ (1 / s)) * fjr s| ≤ ε * VB b (z ^ (1 / s)))

end Palprimes.MT
