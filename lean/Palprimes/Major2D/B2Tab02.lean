import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 2 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_3_10 : tabOKr 6144 (tab2 3) (384 * 10) 384 = true := by decide +kernel
theorem tab2_3_11 : tabOKr 6144 (tab2 3) (384 * 11) 384 = true := by decide +kernel
theorem tab2_3_12 : tabOKr 6144 (tab2 3) (384 * 12) 384 = true := by decide +kernel
theorem tab2_3_13 : tabOKr 6144 (tab2 3) (384 * 13) 384 = true := by decide +kernel
theorem tab2_3_14 : tabOKr 6144 (tab2 3) (384 * 14) 384 = true := by decide +kernel
theorem tab2_3_15 : tabOKr 6144 (tab2 3) (384 * 15) 384 = true := by decide +kernel
theorem tab2_4_0 : tabOKr 12288 (tab2 4) (384 * 0) 384 = true := by decide +kernel
theorem tab2_4_1 : tabOKr 12288 (tab2 4) (384 * 1) 384 = true := by decide +kernel
theorem tab2_4_2 : tabOKr 12288 (tab2 4) (384 * 2) 384 = true := by decide +kernel
theorem tab2_4_3 : tabOKr 12288 (tab2 4) (384 * 3) 384 = true := by decide +kernel
theorem tab2_4_4 : tabOKr 12288 (tab2 4) (384 * 4) 384 = true := by decide +kernel
theorem tab2_4_5 : tabOKr 12288 (tab2 4) (384 * 5) 384 = true := by decide +kernel

end Palprimes.M2
