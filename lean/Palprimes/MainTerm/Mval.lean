import Palprimes.Greaves.Lemma32
import Palprimes.MainTerm.Lemma52H

/-! # The main-term constant `𝓜` and the parameters of the Ω ≤ 4 theorem

`Mval P = ∫_{1/2}^{U} (W(t) − W(1)) / ((1 − t) t) dt + ∫_{T₀}^{1/2} W(t) (1/(1 − t) − h₂(t) − h₄(t)) / t dt`
(Greaves' main term divided by `2e^γ`). `Pstar`: `θ = 0.2608`, `ε₀ = 10⁻⁴`, `U = (1/4 − ε₀)/θ = 2499/2608`,
`V = 4ε₀/θ = 1/652`, `T₀ = 1/8`. -/

set_option linter.style.longLine false

open Real

namespace Palprimes.MT

open Palprimes.Greaves

noncomputable def Mval (P : WPar) : ℝ :=
  (∫ t in (1 / 2 : ℝ)..P.U, (P.W t - (P.U - P.V)) / ((1 - t) * t)) +
    ∫ t in P.T0..(1 / 2 : ℝ), P.W t * (1 / (1 - t) - hk 1 t - hk 2 t) / t

/-- The parameters `θ = 0.2608`, `ε₀ = 10⁻⁴`, `T₀ = 1/8`. -/
noncomputable def Pstar : WPar where
  U := 2499 / 2608
  V := 1 / 652
  T0 := 1 / 8
  hU := by norm_num
  hU1 := by norm_num
  hV := by norm_num
  hUV := by norm_num
  hT0 := by norm_num
  hT1 := by norm_num

theorem Pstar_U : Pstar.U = (1 / 4 - 1 / 10000) / (2608 / 10000) := by simp [Pstar]; norm_num
theorem Pstar_V : Pstar.V = 4 * (1 / 10000) / (2608 / 10000) := by simp [Pstar]; norm_num

end Palprimes.MT
