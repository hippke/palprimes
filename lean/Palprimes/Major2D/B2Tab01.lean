import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 1 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_2_6 : tabOKr 3072 (tab2 2) (384 * 6) 384 = true := by decide +kernel
theorem tab2_2_7 : tabOKr 3072 (tab2 2) (384 * 7) 384 = true := by decide +kernel
theorem tab2_3_0 : tabOKr 6144 (tab2 3) (384 * 0) 384 = true := by decide +kernel
theorem tab2_3_1 : tabOKr 6144 (tab2 3) (384 * 1) 384 = true := by decide +kernel
theorem tab2_3_2 : tabOKr 6144 (tab2 3) (384 * 2) 384 = true := by decide +kernel
theorem tab2_3_3 : tabOKr 6144 (tab2 3) (384 * 3) 384 = true := by decide +kernel
theorem tab2_3_4 : tabOKr 6144 (tab2 3) (384 * 4) 384 = true := by decide +kernel
theorem tab2_3_5 : tabOKr 6144 (tab2 3) (384 * 5) 384 = true := by decide +kernel
theorem tab2_3_6 : tabOKr 6144 (tab2 3) (384 * 6) 384 = true := by decide +kernel
theorem tab2_3_7 : tabOKr 6144 (tab2 3) (384 * 7) 384 = true := by decide +kernel
theorem tab2_3_8 : tabOKr 6144 (tab2 3) (384 * 8) 384 = true := by decide +kernel
theorem tab2_3_9 : tabOKr 6144 (tab2 3) (384 * 9) 384 = true := by decide +kernel

end Palprimes.M2
