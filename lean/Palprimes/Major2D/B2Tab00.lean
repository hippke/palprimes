import Palprimes.Major2D.TabR
import Palprimes.Major2D.B2Cfg

/-! # Base 2: range checks of the phase tables, part 0 -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_0_0 : tabOKr 768 (tab2 0) (384 * 0) 384 = true := by decide +kernel
theorem tab2_0_1 : tabOKr 768 (tab2 0) (384 * 1) 384 = true := by decide +kernel
theorem tab2_1_0 : tabOKr 1536 (tab2 1) (384 * 0) 384 = true := by decide +kernel
theorem tab2_1_1 : tabOKr 1536 (tab2 1) (384 * 1) 384 = true := by decide +kernel
theorem tab2_1_2 : tabOKr 1536 (tab2 1) (384 * 2) 384 = true := by decide +kernel
theorem tab2_1_3 : tabOKr 1536 (tab2 1) (384 * 3) 384 = true := by decide +kernel
theorem tab2_2_0 : tabOKr 3072 (tab2 2) (384 * 0) 384 = true := by decide +kernel
theorem tab2_2_1 : tabOKr 3072 (tab2 2) (384 * 1) 384 = true := by decide +kernel
theorem tab2_2_2 : tabOKr 3072 (tab2 2) (384 * 2) 384 = true := by decide +kernel
theorem tab2_2_3 : tabOKr 3072 (tab2 2) (384 * 3) 384 = true := by decide +kernel
theorem tab2_2_4 : tabOKr 3072 (tab2 2) (384 * 4) 384 = true := by decide +kernel
theorem tab2_2_5 : tabOKr 3072 (tab2 2) (384 * 5) 384 = true := by decide +kernel

end Palprimes.M2
