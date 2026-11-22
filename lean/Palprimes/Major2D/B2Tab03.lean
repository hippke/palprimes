import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 3 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_4_6 : tabOKr 12288 (tab2 4) (384 * 6) 384 = true := by decide +kernel
theorem tab2_4_7 : tabOKr 12288 (tab2 4) (384 * 7) 384 = true := by decide +kernel
theorem tab2_4_8 : tabOKr 12288 (tab2 4) (384 * 8) 384 = true := by decide +kernel
theorem tab2_4_9 : tabOKr 12288 (tab2 4) (384 * 9) 384 = true := by decide +kernel
theorem tab2_4_10 : tabOKr 12288 (tab2 4) (384 * 10) 384 = true := by decide +kernel
theorem tab2_4_11 : tabOKr 12288 (tab2 4) (384 * 11) 384 = true := by decide +kernel
theorem tab2_4_12 : tabOKr 12288 (tab2 4) (384 * 12) 384 = true := by decide +kernel
theorem tab2_4_13 : tabOKr 12288 (tab2 4) (384 * 13) 384 = true := by decide +kernel
theorem tab2_4_14 : tabOKr 12288 (tab2 4) (384 * 14) 384 = true := by decide +kernel
theorem tab2_4_15 : tabOKr 12288 (tab2 4) (384 * 15) 384 = true := by decide +kernel
theorem tab2_4_16 : tabOKr 12288 (tab2 4) (384 * 16) 384 = true := by decide +kernel
theorem tab2_4_17 : tabOKr 12288 (tab2 4) (384 * 17) 384 = true := by decide +kernel

end Palprimes.M2
