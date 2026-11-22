import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 7 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_5_22 : tabOKr 24576 (tab2 5) (384 * 22) 384 = true := by decide +kernel
theorem tab2_5_23 : tabOKr 24576 (tab2 5) (384 * 23) 384 = true := by decide +kernel
theorem tab2_5_24 : tabOKr 24576 (tab2 5) (384 * 24) 384 = true := by decide +kernel
theorem tab2_5_25 : tabOKr 24576 (tab2 5) (384 * 25) 384 = true := by decide +kernel
theorem tab2_5_26 : tabOKr 24576 (tab2 5) (384 * 26) 384 = true := by decide +kernel
theorem tab2_5_27 : tabOKr 24576 (tab2 5) (384 * 27) 384 = true := by decide +kernel
theorem tab2_5_28 : tabOKr 24576 (tab2 5) (384 * 28) 384 = true := by decide +kernel
theorem tab2_5_29 : tabOKr 24576 (tab2 5) (384 * 29) 384 = true := by decide +kernel
theorem tab2_5_30 : tabOKr 24576 (tab2 5) (384 * 30) 384 = true := by decide +kernel
theorem tab2_5_31 : tabOKr 24576 (tab2 5) (384 * 31) 384 = true := by decide +kernel
theorem tab2_5_32 : tabOKr 24576 (tab2 5) (384 * 32) 384 = true := by decide +kernel
theorem tab2_5_33 : tabOKr 24576 (tab2 5) (384 * 33) 384 = true := by decide +kernel

end Palprimes.M2
