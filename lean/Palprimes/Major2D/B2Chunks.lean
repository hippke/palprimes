import Palprimes.Major2D.Chunk
import Palprimes.Major2D.B2C000
import Palprimes.Major2D.B2C001
import Palprimes.Major2D.B2C002
import Palprimes.Major2D.B2C003
import Palprimes.Major2D.B2C004
import Palprimes.Major2D.B2C005
import Palprimes.Major2D.B2C006
import Palprimes.Major2D.B2C007
import Palprimes.Major2D.B2C008
import Palprimes.Major2D.B2C009
import Palprimes.Major2D.B2C010
import Palprimes.Major2D.B2C011
import Palprimes.Major2D.B2C012
import Palprimes.Major2D.B2C013
import Palprimes.Major2D.B2C014
import Palprimes.Major2D.B2C015
import Palprimes.Major2D.B2C016
import Palprimes.Major2D.B2C017
import Palprimes.Major2D.B2C018
import Palprimes.Major2D.B2C019
import Palprimes.Major2D.B2C020
import Palprimes.Major2D.B2C021
import Palprimes.Major2D.B2C022
import Palprimes.Major2D.B2C023
import Palprimes.Major2D.B2C024
import Palprimes.Major2D.B2C025
import Palprimes.Major2D.B2C026
import Palprimes.Major2D.B2C027
import Palprimes.Major2D.B2C028
import Palprimes.Major2D.B2C029
import Palprimes.Major2D.B2C030
import Palprimes.Major2D.B2C031
import Palprimes.Major2D.B2C032
import Palprimes.Major2D.B2C033
import Palprimes.Major2D.B2C034
import Palprimes.Major2D.B2C035
import Palprimes.Major2D.B2C036
import Palprimes.Major2D.B2C037
import Palprimes.Major2D.B2C038
import Palprimes.Major2D.B2C039
import Palprimes.Major2D.B2C040
import Palprimes.Major2D.B2C041
import Palprimes.Major2D.B2C042
import Palprimes.Major2D.B2C043
import Palprimes.Major2D.B2C044
import Palprimes.Major2D.B2C045
import Palprimes.Major2D.B2C046
import Palprimes.Major2D.B2C047
import Palprimes.Major2D.B2C048
import Palprimes.Major2D.B2C049
import Palprimes.Major2D.B2C050
import Palprimes.Major2D.B2C051
import Palprimes.Major2D.B2C052
import Palprimes.Major2D.B2C053
import Palprimes.Major2D.B2C054
import Palprimes.Major2D.B2C055
import Palprimes.Major2D.B2C056
import Palprimes.Major2D.B2C057
import Palprimes.Major2D.B2C058
import Palprimes.Major2D.B2C059
import Palprimes.Major2D.B2C060
import Palprimes.Major2D.B2C061
import Palprimes.Major2D.B2C062
import Palprimes.Major2D.B2C063
import Palprimes.Major2D.B2C064
import Palprimes.Major2D.B2C065
import Palprimes.Major2D.B2C066
import Palprimes.Major2D.B2C067
import Palprimes.Major2D.B2C068
import Palprimes.Major2D.B2C069
import Palprimes.Major2D.B2C070
import Palprimes.Major2D.B2C071
import Palprimes.Major2D.B2C072
import Palprimes.Major2D.B2C073
import Palprimes.Major2D.B2C074
import Palprimes.Major2D.B2C075
import Palprimes.Major2D.B2C076
import Palprimes.Major2D.B2C077
import Palprimes.Major2D.B2C078
import Palprimes.Major2D.B2C079
import Palprimes.Major2D.B2C080
import Palprimes.Major2D.B2C081
import Palprimes.Major2D.B2C082
import Palprimes.Major2D.B2C083
import Palprimes.Major2D.B2C084
import Palprimes.Major2D.B2C085
import Palprimes.Major2D.B2C086
import Palprimes.Major2D.B2C087
import Palprimes.Major2D.B2C088
import Palprimes.Major2D.B2C089
import Palprimes.Major2D.B2C090
import Palprimes.Major2D.B2C091
import Palprimes.Major2D.B2C092
import Palprimes.Major2D.B2C093
import Palprimes.Major2D.B2C094
import Palprimes.Major2D.B2C095
import Palprimes.Major2D.B2C096
import Palprimes.Major2D.B2C097
import Palprimes.Major2D.B2C098
import Palprimes.Major2D.B2C099
import Palprimes.Major2D.B2C100
import Palprimes.Major2D.B2C101
import Palprimes.Major2D.B2C102
import Palprimes.Major2D.B2C103
import Palprimes.Major2D.B2C104
import Palprimes.Major2D.B2C105
import Palprimes.Major2D.B2C106
import Palprimes.Major2D.B2C107
import Palprimes.Major2D.B2C108
import Palprimes.Major2D.B2C109
import Palprimes.Major2D.B2C110

/-! # Base 2: the cell certificate from its 111 chunks -/

namespace Palprimes.M2

/-- the chunks `(offset, size)`. -/
def chunks2 : List (ℕ × ℕ) := [(0, 29), (29, 31), (60, 29), (89, 35), (124, 36), (160, 37), (197, 23), (220, 22), (242, 41), (283, 29), (312, 30), (342, 20), (362, 28), (390, 32), (422, 30), (452, 26), (478, 32), (510, 20), (530, 32), (562, 31), (593, 25), (618, 25), (643, 23), (666, 34), (700, 32), (732, 26), (758, 33), (791, 33), (824, 27), (851, 29), (880, 26), (906, 33), (939, 26), (965, 30), (995, 28), (1023, 26), (1049, 25), (1074, 20), (1094, 23), (1117, 26), (1143, 29), (1172, 28), (1200, 30), (1230, 26), (1256, 37), (1293, 37), (1330, 26), (1356, 32), (1388, 36), (1424, 30), (1454, 25), (1479, 33), (1512, 26), (1538, 24), (1562, 25), (1587, 33), (1620, 29), (1649, 27), (1676, 32), (1708, 29), (1737, 20), (1757, 29), (1786, 28), (1814, 31), (1845, 27), (1872, 24), (1896, 28), (1924, 25), (1949, 30), (1979, 28), (2007, 29), (2036, 31), (2067, 30), (2097, 18), (2115, 25), (2140, 31), (2171, 22), (2193, 26), (2219, 21), (2240, 30), (2270, 31), (2301, 37), (2338, 35), (2373, 36), (2409, 34), (2443, 28), (2471, 25), (2496, 25), (2521, 23), (2544, 19), (2563, 28), (2591, 26), (2617, 26), (2643, 33), (2676, 31), (2707, 28), (2735, 25), (2760, 22), (2782, 28), (2810, 21), (2831, 27), (2858, 19), (2877, 32), (2909, 24), (2933, 31), (2964, 33), (2997, 29), (3026, 24), (3050, 33), (3083, 34), (3117, 19)]

theorem chainOK2 : chainOK 0 chunks2 L2.length = true := by decide +kernel

theorem chunks2_ok : ∀ c ∈ chunks2, ((L2.drop c.1).take c.2).all
    (fun jk => checkRec cfg2 cfg2.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true :=
  List.forall_mem_cons.2 ⟨chk2_000, List.forall_mem_cons.2 ⟨chk2_001, List.forall_mem_cons.2 ⟨chk2_002, List.forall_mem_cons.2 ⟨chk2_003, List.forall_mem_cons.2 ⟨chk2_004, List.forall_mem_cons.2 ⟨chk2_005, List.forall_mem_cons.2 ⟨chk2_006, List.forall_mem_cons.2 ⟨chk2_007, List.forall_mem_cons.2 ⟨chk2_008, List.forall_mem_cons.2 ⟨chk2_009, List.forall_mem_cons.2 ⟨chk2_010, List.forall_mem_cons.2 ⟨chk2_011, List.forall_mem_cons.2 ⟨chk2_012, List.forall_mem_cons.2 ⟨chk2_013, List.forall_mem_cons.2 ⟨chk2_014, List.forall_mem_cons.2 ⟨chk2_015, List.forall_mem_cons.2 ⟨chk2_016, List.forall_mem_cons.2 ⟨chk2_017, List.forall_mem_cons.2 ⟨chk2_018, List.forall_mem_cons.2 ⟨chk2_019, List.forall_mem_cons.2 ⟨chk2_020, List.forall_mem_cons.2 ⟨chk2_021, List.forall_mem_cons.2 ⟨chk2_022, List.forall_mem_cons.2 ⟨chk2_023, List.forall_mem_cons.2 ⟨chk2_024, List.forall_mem_cons.2 ⟨chk2_025, List.forall_mem_cons.2 ⟨chk2_026, List.forall_mem_cons.2 ⟨chk2_027, List.forall_mem_cons.2 ⟨chk2_028, List.forall_mem_cons.2 ⟨chk2_029, List.forall_mem_cons.2 ⟨chk2_030, List.forall_mem_cons.2 ⟨chk2_031, List.forall_mem_cons.2 ⟨chk2_032, List.forall_mem_cons.2 ⟨chk2_033, List.forall_mem_cons.2 ⟨chk2_034, List.forall_mem_cons.2 ⟨chk2_035, List.forall_mem_cons.2 ⟨chk2_036, List.forall_mem_cons.2 ⟨chk2_037, List.forall_mem_cons.2 ⟨chk2_038, List.forall_mem_cons.2 ⟨chk2_039, List.forall_mem_cons.2 ⟨chk2_040, List.forall_mem_cons.2 ⟨chk2_041, List.forall_mem_cons.2 ⟨chk2_042, List.forall_mem_cons.2 ⟨chk2_043, List.forall_mem_cons.2 ⟨chk2_044, List.forall_mem_cons.2 ⟨chk2_045, List.forall_mem_cons.2 ⟨chk2_046, List.forall_mem_cons.2 ⟨chk2_047, List.forall_mem_cons.2 ⟨chk2_048, List.forall_mem_cons.2 ⟨chk2_049, List.forall_mem_cons.2 ⟨chk2_050, List.forall_mem_cons.2 ⟨chk2_051, List.forall_mem_cons.2 ⟨chk2_052, List.forall_mem_cons.2 ⟨chk2_053, List.forall_mem_cons.2 ⟨chk2_054, List.forall_mem_cons.2 ⟨chk2_055, List.forall_mem_cons.2 ⟨chk2_056, List.forall_mem_cons.2 ⟨chk2_057, List.forall_mem_cons.2 ⟨chk2_058, List.forall_mem_cons.2 ⟨chk2_059, List.forall_mem_cons.2 ⟨chk2_060, List.forall_mem_cons.2 ⟨chk2_061, List.forall_mem_cons.2 ⟨chk2_062, List.forall_mem_cons.2 ⟨chk2_063, List.forall_mem_cons.2 ⟨chk2_064, List.forall_mem_cons.2 ⟨chk2_065, List.forall_mem_cons.2 ⟨chk2_066, List.forall_mem_cons.2 ⟨chk2_067, List.forall_mem_cons.2 ⟨chk2_068, List.forall_mem_cons.2 ⟨chk2_069, List.forall_mem_cons.2 ⟨chk2_070, List.forall_mem_cons.2 ⟨chk2_071, List.forall_mem_cons.2 ⟨chk2_072, List.forall_mem_cons.2 ⟨chk2_073, List.forall_mem_cons.2 ⟨chk2_074, List.forall_mem_cons.2 ⟨chk2_075, List.forall_mem_cons.2 ⟨chk2_076, List.forall_mem_cons.2 ⟨chk2_077, List.forall_mem_cons.2 ⟨chk2_078, List.forall_mem_cons.2 ⟨chk2_079, List.forall_mem_cons.2 ⟨chk2_080, List.forall_mem_cons.2 ⟨chk2_081, List.forall_mem_cons.2 ⟨chk2_082, List.forall_mem_cons.2 ⟨chk2_083, List.forall_mem_cons.2 ⟨chk2_084, List.forall_mem_cons.2 ⟨chk2_085, List.forall_mem_cons.2 ⟨chk2_086, List.forall_mem_cons.2 ⟨chk2_087, List.forall_mem_cons.2 ⟨chk2_088, List.forall_mem_cons.2 ⟨chk2_089, List.forall_mem_cons.2 ⟨chk2_090, List.forall_mem_cons.2 ⟨chk2_091, List.forall_mem_cons.2 ⟨chk2_092, List.forall_mem_cons.2 ⟨chk2_093, List.forall_mem_cons.2 ⟨chk2_094, List.forall_mem_cons.2 ⟨chk2_095, List.forall_mem_cons.2 ⟨chk2_096, List.forall_mem_cons.2 ⟨chk2_097, List.forall_mem_cons.2 ⟨chk2_098, List.forall_mem_cons.2 ⟨chk2_099, List.forall_mem_cons.2 ⟨chk2_100, List.forall_mem_cons.2 ⟨chk2_101, List.forall_mem_cons.2 ⟨chk2_102, List.forall_mem_cons.2 ⟨chk2_103, List.forall_mem_cons.2 ⟨chk2_104, List.forall_mem_cons.2 ⟨chk2_105, List.forall_mem_cons.2 ⟨chk2_106, List.forall_mem_cons.2 ⟨chk2_107, List.forall_mem_cons.2 ⟨chk2_108, List.forall_mem_cons.2 ⟨chk2_109, List.forall_mem_cons.2 ⟨chk2_110, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- **The base-2 cell certificate** (all 3136 level-0 cells). -/
theorem chk2 : checkList cfg2 L2 = true := by
  unfold checkList
  have := all_chunks2 _ L2 chunks2 0 chunks2_ok chainOK2
  simpa using this

end Palprimes.M2
