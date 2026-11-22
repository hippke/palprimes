import Palprimes.Major2D.B3Cfg

/-! # Base 3: cell certificate, chunk 0 of 3 (level-0 cells 0 … 60, 593 checker nodes) -/

namespace Palprimes.M2

set_option maxRecDepth 100000 in
theorem chk3_000 : ((L3.drop 0).take 61).all
    (fun jk => checkRec cfg3 cfg3.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true := by decide +kernel

end Palprimes.M2
