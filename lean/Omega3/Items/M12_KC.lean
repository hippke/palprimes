import Omega3.Items.M12_Data
import Omega3.Items.M12_Lit

/-! # M12 helper: kernel check of the coarse levels 4–16 (about 1 min) -/

namespace Omega3.M12

set_option maxRecDepth 100000 in
theorem restC_eq : restC = restLit := by decide +kernel

end Omega3.M12
