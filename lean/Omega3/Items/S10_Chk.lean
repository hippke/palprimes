import Omega3.Items.S10_Glue
import Omega3.Items.S10_Data

/-!
# S10 helpers, part 9: the kernel checks of the five bands (`decide +kernel`, Nat/Int arithmetic only)
-/

set_option linter.style.longLine false

namespace Omega3
namespace S10

set_option maxRecDepth 100000 in
theorem chk0 : bandChk (dEdges.headD 0) (dMs0.headD 0) dEdges.tail dMs0.tail dSg 1 3 10254 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chk1 : bandChk (dEdges.headD 0) (dMs1.headD 0) dEdges.tail dMs1.tail dSg 3917 10000 8163 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chk2 : bandChk (dEdges.headD 0) (dMs2.headD 0) dEdges.tail dMs2.tail dSg 9 20 5962 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chk3 : bandChk (dEdges.headD 0) (dMs3.headD 0) dEdges.tail dMs3.tail dSg 1271 2500 3555 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chk4 : bandChk (dEdges.headD 0) (dMs4.headD 0) dEdges.tail dMs4.tail dSg 5667 10000 1381 = true := by decide +kernel

end S10
end Omega3
