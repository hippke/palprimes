import Palprimes.Major2D.B2Cfg

/-! # Base 2: cell certificate, chunk 101 of 111 (level-0 cells 2858 … 2876, 615 checker nodes) -/

namespace Palprimes.M2

set_option maxRecDepth 100000 in
theorem chk2_101 : ((L2.drop 2858).take 19).all
    (fun jk => checkRec cfg2 cfg2.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true := by decide +kernel

end Palprimes.M2
