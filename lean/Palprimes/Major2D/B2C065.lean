import Palprimes.Major2D.B2Cfg

/-! # Base 2: cell certificate, chunk 65 of 111 (level-0 cells 1872 … 1895, 624 checker nodes) -/

namespace Palprimes.M2

set_option maxRecDepth 100000 in
theorem chk2_065 : ((L2.drop 1872).take 24).all
    (fun jk => checkRec cfg2 cfg2.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true := by decide +kernel

end Palprimes.M2
