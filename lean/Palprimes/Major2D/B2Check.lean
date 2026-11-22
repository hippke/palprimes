import Palprimes.Major2D.B2Tab
import Palprimes.Major2D.B2Light
import Palprimes.Major2D.Maj
import Palprimes.Major2D.Table

/-! # Base 2: kernel-checked facts (except the cell certificate, see `B2C*.lean`) -/

set_option linter.style.longLine false

namespace Palprimes.M2

set_option maxRecDepth 100000

theorem tab2_lv0 : TabGood 768 (tab2 0) :=
  tabGood_of_ranges 768 (tab2 0) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 2 := by omega
    interval_cases i
    exacts [tab2_0_0, tab2_0_1])

theorem tab2_lv1 : TabGood 1536 (tab2 1) :=
  tabGood_of_ranges 1536 (tab2 1) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 4 := by omega
    interval_cases i
    exacts [tab2_1_0, tab2_1_1, tab2_1_2, tab2_1_3])

theorem tab2_lv2 : TabGood 3072 (tab2 2) :=
  tabGood_of_ranges 3072 (tab2 2) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 8 := by omega
    interval_cases i
    exacts [tab2_2_0, tab2_2_1, tab2_2_2, tab2_2_3, tab2_2_4, tab2_2_5, tab2_2_6, tab2_2_7])

theorem tab2_lv3 : TabGood 6144 (tab2 3) :=
  tabGood_of_ranges 6144 (tab2 3) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 16 := by omega
    interval_cases i
    exacts [tab2_3_0, tab2_3_1, tab2_3_2, tab2_3_3, tab2_3_4, tab2_3_5, tab2_3_6, tab2_3_7, tab2_3_8, tab2_3_9, tab2_3_10, tab2_3_11, tab2_3_12, tab2_3_13, tab2_3_14, tab2_3_15])

theorem tab2_lv4 : TabGood 12288 (tab2 4) :=
  tabGood_of_ranges 12288 (tab2 4) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 32 := by omega
    interval_cases i
    exacts [tab2_4_0, tab2_4_1, tab2_4_2, tab2_4_3, tab2_4_4, tab2_4_5, tab2_4_6, tab2_4_7, tab2_4_8, tab2_4_9, tab2_4_10, tab2_4_11, tab2_4_12, tab2_4_13, tab2_4_14, tab2_4_15, tab2_4_16, tab2_4_17, tab2_4_18, tab2_4_19, tab2_4_20, tab2_4_21, tab2_4_22, tab2_4_23, tab2_4_24, tab2_4_25, tab2_4_26, tab2_4_27, tab2_4_28, tab2_4_29, tab2_4_30, tab2_4_31])

theorem tab2_lv5 : TabGood 24576 (tab2 5) :=
  tabGood_of_ranges 24576 (tab2 5) 384 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by
    intro i hi
    have hi' : i < 64 := by omega
    interval_cases i
    exacts [tab2_5_0, tab2_5_1, tab2_5_2, tab2_5_3, tab2_5_4, tab2_5_5, tab2_5_6, tab2_5_7, tab2_5_8, tab2_5_9, tab2_5_10, tab2_5_11, tab2_5_12, tab2_5_13, tab2_5_14, tab2_5_15, tab2_5_16, tab2_5_17, tab2_5_18, tab2_5_19, tab2_5_20, tab2_5_21, tab2_5_22, tab2_5_23, tab2_5_24, tab2_5_25, tab2_5_26, tab2_5_27, tab2_5_28, tab2_5_29, tab2_5_30, tab2_5_31, tab2_5_32, tab2_5_33, tab2_5_34, tab2_5_35, tab2_5_36, tab2_5_37, tab2_5_38, tab2_5_39, tab2_5_40, tab2_5_41, tab2_5_42, tab2_5_43, tab2_5_44, tab2_5_45, tab2_5_46, tab2_5_47, tab2_5_48, tab2_5_49, tab2_5_50, tab2_5_51, tab2_5_52, tab2_5_53, tab2_5_54, tab2_5_55, tab2_5_56, tab2_5_57, tab2_5_58, tab2_5_59, tab2_5_60, tab2_5_61, tab2_5_62, tab2_5_63])

end Palprimes.M2
