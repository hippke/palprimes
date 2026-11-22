import Palprimes.Major2D.Comp
import Palprimes.Major2D.B3Cfg

/-! # Base 3: kernel-checked data facts (core instances only, so that `^` is `Nat.pow`) -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem U2_3_ok : 2 * 2 ^ (64 * 50) ≤ U2_3 ^ 50 := by decide +kernel
theorem V3_ok : ∀ j < 256, 256 * 2 ^ (64 * 50) ≤ getV V3 j ^ 50 * (256 + j) := by decide +kernel
theorem cover3 : coverOK 64 8 G3 L3 = true := by decide +kernel
theorem shiftT3 : ∀ ac ∈ shifts3, shiftOK T3terms ac.1 ac.2 8 0 = true := by decide +kernel
theorem shiftF3 : ∀ ac ∈ shifts3, ∀ f ∈ facs3, shiftOK f.1 ac.1 ac.2 8 0 = true ∨ shiftOK f.1 ac.1 ac.2 8 1 = true := by
  decide +kernel
theorem swapT3 : (T3terms.map (fun t => nrmT (swpT t))).Perm T3terms := by decide +kernel
theorem swapF3 : facs3.map (fun f => (f.1.map (fun t => nrmT (swpT t)), f.2)) = facs3.reverse := by decide +kernel
theorem nodup3 : (T3full.map Prod.fst).Nodup := by decide +kernel
theorem perm3 : (T3terms.flatMap expandH).Perm T3full := by decide +kernel
theorem even3 : evenOK T3terms = true := by decide +kernel
theorem L3lt : ∀ jk ∈ L3, jk.2 < 64 := by decide +kernel
theorem G3ok : ∀ g ∈ G3, ((g.2.2.1 : ℤ), (g.2.2.2 : ℤ)) ∈ shifts3 ∧ g.2.2.1 < 8 ∧ g.2.2.2 < 8 := by decide +kernel
theorem bounds3 : ∀ e ∈ T3full, e.1.1.natAbs < 27 ∧ e.1.2.natAbs < 27 := by decide +kernel
theorem neg3 : ∀ e ∈ T3full, ((-e.1.1, -e.1.2), e.2) ∈ T3full := by decide +kernel
theorem zero3 : ((0 : ℤ), (0 : ℤ)) ∈ T3full.map Prod.fst := by decide +kernel
theorem t00_3 : lk T3full (0, 0) = 809729125563748 := by decide +kernel
theorem A3 : (T3full.map Prod.snd).sum = 4518200408842788 := by decide +kernel
/-- condition (ii): `t₀₀^62500 · 3^97801 ≤ (27/19)^652`. -/
theorem cond2_3 : Nat.ble (condL 809729125563748 62500 3 97801 652) (condR 62500 3 652) = true := by decide +kernel
/-- condition (iii): `A^125000 · 3^3 ≤ (27/19)^1175`. -/
theorem cond3_3 : Nat.ble (condL 4518200408842788 125000 3 3 1175) (condR 125000 3 1175) = true := by decide +kernel


end Palprimes.M2
