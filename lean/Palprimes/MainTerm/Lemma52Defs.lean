import Palprimes.MainTerm.Defs

/-! # Lemma 5.2: shared definitions for the symmetrisation argument

Vectors `y : Fin N → ℝ` are the `N` free variables of Greaves' `{𝒟}` (p. 317–318): an
x-chain `y_0 > ⋯ > y_{a-1}` (`= x_1 > ⋯ > x_{r-1}`, `a = r − 1`) followed by a u-chain
`y_a > ⋯ > y_{N-1}` (`= u_1 > ⋯ > u_t`). Block conditions are stated on `ℕ` indices through
`ext`, so that no casts between `Fin (a + b)` and `Fin N` are needed. -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.MT

/-- Extension of a finite vector by `0` to `ℕ`. -/
noncomputable def ext {N : ℕ} (y : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then y ⟨k, h⟩ else 0

/-- The first `a` coordinates as a vector (padded by `0` if `a > N`). -/
noncomputable def blk {N : ℕ} (a : ℕ) (y : Fin N → ℝ) : Fin a → ℝ := fun k => ext y k

/-- Strictly decreasing on the block `[0, a)` and on the block `[a, N)`. -/
def BlockMono {N : ℕ} (a : ℕ) (y : Fin N → ℝ) : Prop :=
  ∀ i j : ℕ, i < j → j < N → (j < a ∨ a ≤ i) → ext y j < ext y i

/-- The `(r, t)` region of (5.9) before the inclusion–exclusion, `a = r − 1`: all `> x`,
both chains strictly decreasing, Rosser conditions on the x-chain (followed by `x`). -/
def PReg {N : ℕ} (a : ℕ) (x : ℝ) (y : Fin N → ℝ) : Prop :=
  (∀ i, x < y i) ∧ BlockMono a y ∧ RosserX x (blk a y)

/-- The region of `h_{2m}(x, 1)` on the full vector `(x_1, …, x_{2m}, u)`. -/
def HReg (m : ℕ) (x : ℝ) (y : Fin (2 * m + 1) → ℝ) : Prop :=
  (∀ i, x < y i) ∧ HRegion m x (fun i => y (Fin.castSucc i))

end Palprimes.MT
