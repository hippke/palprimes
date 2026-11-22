import Palprimes.Major2D.Comp2
import Palprimes.Major2D.B2Cfg

/-! # Base 2: kernel-checked data facts (core instances only, so that `^` is `Nat.pow`) -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem U2_2_ok : u2Chk U2_2 1000 = true := by decide +kernel
theorem V2_ok : vChk V2 1000 = true := by decide +kernel
theorem cover2 : coverOK 192 64 G2 L2 = true := by decide +kernel
theorem shiftT2 : ∀ ac ∈ shifts2, shiftOK T2terms ac.1 ac.2 3 0 = true := by decide +kernel
theorem shiftF2 : ∀ ac ∈ shifts2, ∀ f ∈ facs2, shiftOK f.1 ac.1 ac.2 3 0 = true ∨ shiftOK f.1 ac.1 ac.2 3 1 = true := by
  decide +kernel
theorem swapT2 : (T2terms.map (fun t => nrmT (swpT t))).Perm T2terms := by decide +kernel
theorem swapF2 : facs2.map (fun f => (f.1.map (fun t => nrmT (swpT t)), f.2)) = facs2.reverse := by decide +kernel
theorem nodup2 : (T2full.map Prod.fst).Nodup := by decide +kernel
theorem perm2 : (T2terms.flatMap expandH).Perm T2full := by decide +kernel
theorem even2 : evenOK T2terms = true := by decide +kernel
theorem L2lt : ∀ jk ∈ L2, jk.2 < 192 := by decide +kernel
theorem G2ok : ∀ g ∈ G2, ((g.2.2.1 : ℤ), (g.2.2.2 : ℤ)) ∈ shifts2 ∧ g.2.2.1 < 3 ∧ g.2.2.2 < 3 := by decide +kernel
theorem bounds2 : ∀ e ∈ T2full, e.1.1.natAbs < 128 ∧ e.1.2.natAbs < 128 := by decide +kernel
theorem neg2 : ∀ e ∈ T2full, ((-e.1.1, -e.1.2), e.2) ∈ T2full := by decide +kernel
theorem zero2 : ((0 : ℤ), (0 : ℤ)) ∈ T2full.map Prod.fst := by decide +kernel
theorem t00_2 : lk T2full (0, 0) = 358572778288936 := by decide +kernel
theorem A2 : (T2full.map Prod.snd).sum = 4504889504128116 := by decide +kernel
/-- condition (ii): `t₀₀^937500 · 2^3423025 ≤ (12/9)^1141`. -/
theorem cond2_2 : Nat.ble (condL 358572778288936 937500 2 3423025 1141) (condR 937500 2 1141) = true := by decide +kernel
/-- condition (iii): `A^300000 · 2^12 ≤ (12/9)^329`. -/
theorem cond3_2 : Nat.ble (condL 4504889504128116 300000 2 12 329) (condR 300000 2 329) = true := by decide +kernel


end Palprimes.M2
