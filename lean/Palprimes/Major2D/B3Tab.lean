import Palprimes.Major2D.TabR
import Palprimes.Major2D.B3Cfg

/-! # Base 3: range checks of the phase tables (256 entries per declaration) -/

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab3_0_0 : tabOKr 256 (tab3 0) (256 * 0) 256 = true := by decide +kernel
theorem tab3_1_0 : tabOKr 512 (tab3 1) (256 * 0) 256 = true := by decide +kernel
theorem tab3_1_1 : tabOKr 512 (tab3 1) (256 * 1) 256 = true := by decide +kernel
theorem tab3_2_0 : tabOKr 1024 (tab3 2) (256 * 0) 256 = true := by decide +kernel
theorem tab3_2_1 : tabOKr 1024 (tab3 2) (256 * 1) 256 = true := by decide +kernel
theorem tab3_2_2 : tabOKr 1024 (tab3 2) (256 * 2) 256 = true := by decide +kernel
theorem tab3_2_3 : tabOKr 1024 (tab3 2) (256 * 3) 256 = true := by decide +kernel
theorem tab3_3_0 : tabOKr 2048 (tab3 3) (256 * 0) 256 = true := by decide +kernel
theorem tab3_3_1 : tabOKr 2048 (tab3 3) (256 * 1) 256 = true := by decide +kernel
theorem tab3_3_2 : tabOKr 2048 (tab3 3) (256 * 2) 256 = true := by decide +kernel
theorem tab3_3_3 : tabOKr 2048 (tab3 3) (256 * 3) 256 = true := by decide +kernel
theorem tab3_3_4 : tabOKr 2048 (tab3 3) (256 * 4) 256 = true := by decide +kernel
theorem tab3_3_5 : tabOKr 2048 (tab3 3) (256 * 5) 256 = true := by decide +kernel
theorem tab3_3_6 : tabOKr 2048 (tab3 3) (256 * 6) 256 = true := by decide +kernel
theorem tab3_3_7 : tabOKr 2048 (tab3 3) (256 * 7) 256 = true := by decide +kernel
theorem tab3_4_0 : tabOKr 4096 (tab3 4) (256 * 0) 256 = true := by decide +kernel
theorem tab3_4_1 : tabOKr 4096 (tab3 4) (256 * 1) 256 = true := by decide +kernel
theorem tab3_4_2 : tabOKr 4096 (tab3 4) (256 * 2) 256 = true := by decide +kernel
theorem tab3_4_3 : tabOKr 4096 (tab3 4) (256 * 3) 256 = true := by decide +kernel
theorem tab3_4_4 : tabOKr 4096 (tab3 4) (256 * 4) 256 = true := by decide +kernel
theorem tab3_4_5 : tabOKr 4096 (tab3 4) (256 * 5) 256 = true := by decide +kernel
theorem tab3_4_6 : tabOKr 4096 (tab3 4) (256 * 6) 256 = true := by decide +kernel
theorem tab3_4_7 : tabOKr 4096 (tab3 4) (256 * 7) 256 = true := by decide +kernel
theorem tab3_4_8 : tabOKr 4096 (tab3 4) (256 * 8) 256 = true := by decide +kernel
theorem tab3_4_9 : tabOKr 4096 (tab3 4) (256 * 9) 256 = true := by decide +kernel
theorem tab3_4_10 : tabOKr 4096 (tab3 4) (256 * 10) 256 = true := by decide +kernel
theorem tab3_4_11 : tabOKr 4096 (tab3 4) (256 * 11) 256 = true := by decide +kernel
theorem tab3_4_12 : tabOKr 4096 (tab3 4) (256 * 12) 256 = true := by decide +kernel
theorem tab3_4_13 : tabOKr 4096 (tab3 4) (256 * 13) 256 = true := by decide +kernel
theorem tab3_4_14 : tabOKr 4096 (tab3 4) (256 * 14) 256 = true := by decide +kernel
theorem tab3_4_15 : tabOKr 4096 (tab3 4) (256 * 15) 256 = true := by decide +kernel
theorem tab3_5_0 : tabOKr 8192 (tab3 5) (256 * 0) 256 = true := by decide +kernel
theorem tab3_5_1 : tabOKr 8192 (tab3 5) (256 * 1) 256 = true := by decide +kernel
theorem tab3_5_2 : tabOKr 8192 (tab3 5) (256 * 2) 256 = true := by decide +kernel
theorem tab3_5_3 : tabOKr 8192 (tab3 5) (256 * 3) 256 = true := by decide +kernel
theorem tab3_5_4 : tabOKr 8192 (tab3 5) (256 * 4) 256 = true := by decide +kernel
theorem tab3_5_5 : tabOKr 8192 (tab3 5) (256 * 5) 256 = true := by decide +kernel
theorem tab3_5_6 : tabOKr 8192 (tab3 5) (256 * 6) 256 = true := by decide +kernel
theorem tab3_5_7 : tabOKr 8192 (tab3 5) (256 * 7) 256 = true := by decide +kernel
theorem tab3_5_8 : tabOKr 8192 (tab3 5) (256 * 8) 256 = true := by decide +kernel
theorem tab3_5_9 : tabOKr 8192 (tab3 5) (256 * 9) 256 = true := by decide +kernel
theorem tab3_5_10 : tabOKr 8192 (tab3 5) (256 * 10) 256 = true := by decide +kernel
theorem tab3_5_11 : tabOKr 8192 (tab3 5) (256 * 11) 256 = true := by decide +kernel
theorem tab3_5_12 : tabOKr 8192 (tab3 5) (256 * 12) 256 = true := by decide +kernel
theorem tab3_5_13 : tabOKr 8192 (tab3 5) (256 * 13) 256 = true := by decide +kernel
theorem tab3_5_14 : tabOKr 8192 (tab3 5) (256 * 14) 256 = true := by decide +kernel
theorem tab3_5_15 : tabOKr 8192 (tab3 5) (256 * 15) 256 = true := by decide +kernel
theorem tab3_5_16 : tabOKr 8192 (tab3 5) (256 * 16) 256 = true := by decide +kernel
theorem tab3_5_17 : tabOKr 8192 (tab3 5) (256 * 17) 256 = true := by decide +kernel
theorem tab3_5_18 : tabOKr 8192 (tab3 5) (256 * 18) 256 = true := by decide +kernel
theorem tab3_5_19 : tabOKr 8192 (tab3 5) (256 * 19) 256 = true := by decide +kernel
theorem tab3_5_20 : tabOKr 8192 (tab3 5) (256 * 20) 256 = true := by decide +kernel
theorem tab3_5_21 : tabOKr 8192 (tab3 5) (256 * 21) 256 = true := by decide +kernel
theorem tab3_5_22 : tabOKr 8192 (tab3 5) (256 * 22) 256 = true := by decide +kernel
theorem tab3_5_23 : tabOKr 8192 (tab3 5) (256 * 23) 256 = true := by decide +kernel
theorem tab3_5_24 : tabOKr 8192 (tab3 5) (256 * 24) 256 = true := by decide +kernel
theorem tab3_5_25 : tabOKr 8192 (tab3 5) (256 * 25) 256 = true := by decide +kernel
theorem tab3_5_26 : tabOKr 8192 (tab3 5) (256 * 26) 256 = true := by decide +kernel
theorem tab3_5_27 : tabOKr 8192 (tab3 5) (256 * 27) 256 = true := by decide +kernel
theorem tab3_5_28 : tabOKr 8192 (tab3 5) (256 * 28) 256 = true := by decide +kernel
theorem tab3_5_29 : tabOKr 8192 (tab3 5) (256 * 29) 256 = true := by decide +kernel
theorem tab3_5_30 : tabOKr 8192 (tab3 5) (256 * 30) 256 = true := by decide +kernel
theorem tab3_5_31 : tabOKr 8192 (tab3 5) (256 * 31) 256 = true := by decide +kernel

end Palprimes.M2
