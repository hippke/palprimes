import Palprimes.Major2D.B3Tab
import Palprimes.Major2D.B3Light
import Palprimes.Major2D.Maj
import Palprimes.Major2D.Table

/-! # Base 3: kernel-checked facts -/

set_option linter.style.longLine false

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab3_lv0 : TabGood 256 (tab3 0) :=
  tabGood_of_ranges 256 (tab3 0) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have : i = 0 := by omega
    subst this; exact tab3_0_0)

theorem tab3_lv1 : TabGood 512 (tab3 1) :=
  tabGood_of_ranges 512 (tab3 1) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 2 := by omega
    interval_cases i
    exacts [tab3_1_0, tab3_1_1])

theorem tab3_lv2 : TabGood 1024 (tab3 2) :=
  tabGood_of_ranges 1024 (tab3 2) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 4 := by omega
    interval_cases i
    exacts [tab3_2_0, tab3_2_1, tab3_2_2, tab3_2_3])

theorem tab3_lv3 : TabGood 2048 (tab3 3) :=
  tabGood_of_ranges 2048 (tab3 3) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 8 := by omega
    interval_cases i
    exacts [tab3_3_0, tab3_3_1, tab3_3_2, tab3_3_3, tab3_3_4, tab3_3_5, tab3_3_6, tab3_3_7])

theorem tab3_lv4 : TabGood 4096 (tab3 4) :=
  tabGood_of_ranges 4096 (tab3 4) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 16 := by omega
    interval_cases i
    exacts [tab3_4_0, tab3_4_1, tab3_4_2, tab3_4_3, tab3_4_4, tab3_4_5, tab3_4_6, tab3_4_7, tab3_4_8, tab3_4_9, tab3_4_10, tab3_4_11, tab3_4_12, tab3_4_13, tab3_4_14, tab3_4_15])

theorem tab3_lv5 : TabGood 8192 (tab3 5) :=
  tabGood_of_ranges 8192 (tab3 5) 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 32 := by omega
    interval_cases i
    exacts [tab3_5_0, tab3_5_1, tab3_5_2, tab3_5_3, tab3_5_4, tab3_5_5, tab3_5_6, tab3_5_7, tab3_5_8, tab3_5_9, tab3_5_10, tab3_5_11, tab3_5_12, tab3_5_13, tab3_5_14, tab3_5_15, tab3_5_16, tab3_5_17, tab3_5_18, tab3_5_19, tab3_5_20, tab3_5_21, tab3_5_22, tab3_5_23, tab3_5_24, tab3_5_25, tab3_5_26, tab3_5_27, tab3_5_28, tab3_5_29, tab3_5_30, tab3_5_31])

end Palprimes.M2
