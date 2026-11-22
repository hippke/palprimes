import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 5 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_4_30 : tabOKr 12288 (tab2 4) (384 * 30) 384 = true := by decide +kernel
theorem tab2_4_31 : tabOKr 12288 (tab2 4) (384 * 31) 384 = true := by decide +kernel
theorem tab2_5_0 : tabOKr 24576 (tab2 5) (384 * 0) 384 = true := by decide +kernel
theorem tab2_5_1 : tabOKr 24576 (tab2 5) (384 * 1) 384 = true := by decide +kernel
theorem tab2_5_2 : tabOKr 24576 (tab2 5) (384 * 2) 384 = true := by decide +kernel
theorem tab2_5_3 : tabOKr 24576 (tab2 5) (384 * 3) 384 = true := by decide +kernel
theorem tab2_5_4 : tabOKr 24576 (tab2 5) (384 * 4) 384 = true := by decide +kernel
theorem tab2_5_5 : tabOKr 24576 (tab2 5) (384 * 5) 384 = true := by decide +kernel
theorem tab2_5_6 : tabOKr 24576 (tab2 5) (384 * 6) 384 = true := by decide +kernel
theorem tab2_5_7 : tabOKr 24576 (tab2 5) (384 * 7) 384 = true := by decide +kernel
theorem tab2_5_8 : tabOKr 24576 (tab2 5) (384 * 8) 384 = true := by decide +kernel
theorem tab2_5_9 : tabOKr 24576 (tab2 5) (384 * 9) 384 = true := by decide +kernel

end Palprimes.M2
