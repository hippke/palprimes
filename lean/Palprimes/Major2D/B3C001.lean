import Palprimes.Major2D.B3Cfg

/-! # Base 3: cell certificate, chunk 1 of 3 (level-0 cells 61 … 120, 600 checker nodes) -/

namespace Palprimes.M2

set_option maxRecDepth 100000 in
theorem chk3_001 : ((L3.drop 61).take 60).all
    (fun jk => checkRec cfg3 cfg3.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true := by decide +kernel

end Palprimes.M2
