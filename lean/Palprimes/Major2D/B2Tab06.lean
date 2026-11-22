import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 6 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_5_10 : tabOKr 24576 (tab2 5) (384 * 10) 384 = true := by decide +kernel
theorem tab2_5_11 : tabOKr 24576 (tab2 5) (384 * 11) 384 = true := by decide +kernel
theorem tab2_5_12 : tabOKr 24576 (tab2 5) (384 * 12) 384 = true := by decide +kernel
theorem tab2_5_13 : tabOKr 24576 (tab2 5) (384 * 13) 384 = true := by decide +kernel
theorem tab2_5_14 : tabOKr 24576 (tab2 5) (384 * 14) 384 = true := by decide +kernel
theorem tab2_5_15 : tabOKr 24576 (tab2 5) (384 * 15) 384 = true := by decide +kernel
theorem tab2_5_16 : tabOKr 24576 (tab2 5) (384 * 16) 384 = true := by decide +kernel
theorem tab2_5_17 : tabOKr 24576 (tab2 5) (384 * 17) 384 = true := by decide +kernel
theorem tab2_5_18 : tabOKr 24576 (tab2 5) (384 * 18) 384 = true := by decide +kernel
theorem tab2_5_19 : tabOKr 24576 (tab2 5) (384 * 19) 384 = true := by decide +kernel
theorem tab2_5_20 : tabOKr 24576 (tab2 5) (384 * 20) 384 = true := by decide +kernel
theorem tab2_5_21 : tabOKr 24576 (tab2 5) (384 * 21) 384 = true := by decide +kernel

end Palprimes.M2
