import Omega3.Items.M12_Data
import Omega3.Items.M12_Lit

/-! # M12 helper: kernel check of the fine level-2 top row (about 1 min, 10 GB) -/

namespace Omega3.M12

set_option maxRecDepth 100000 in
theorem h2F_eq : h2F = h2Lit := by decide +kernel

end Omega3.M12
