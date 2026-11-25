import KappaOmega2.Items.M12_Data
import KappaOmega2.Items.M12_Lit

/-! # M12 helper: kernel check of the coarse levels 4–16 (about 1 min) -/

namespace KappaOmega2.M12

set_option maxRecDepth 100000 in
theorem restC_eq : restC = restLit := by decide +kernel

end KappaOmega2.M12
