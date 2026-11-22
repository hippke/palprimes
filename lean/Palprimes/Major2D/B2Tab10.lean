import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 10 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_5_58 : tabOKr 24576 (tab2 5) (384 * 58) 384 = true := by decide +kernel
theorem tab2_5_59 : tabOKr 24576 (tab2 5) (384 * 59) 384 = true := by decide +kernel
theorem tab2_5_60 : tabOKr 24576 (tab2 5) (384 * 60) 384 = true := by decide +kernel
theorem tab2_5_61 : tabOKr 24576 (tab2 5) (384 * 61) 384 = true := by decide +kernel
theorem tab2_5_62 : tabOKr 24576 (tab2 5) (384 * 62) 384 = true := by decide +kernel
theorem tab2_5_63 : tabOKr 24576 (tab2 5) (384 * 63) 384 = true := by decide +kernel

end Palprimes.M2
