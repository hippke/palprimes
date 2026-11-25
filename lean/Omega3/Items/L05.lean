import Omega3.Statements
import Omega3.Items.L05_Gen

namespace Omega3

open Finset Palprimes Omega3.L05g

theorem l05_hF : chkP (Fpoly g8list 8 P8list 5) 60 (-1) 1 = true := by decide +kernel

theorem l05_hP : chkP (Ppoly P8list 5) 60 (-1) 1 = true := by decide +kernel

theorem itemL05 : ItemL05 := by
  intro t
  have hG : Gg 8 (recGR 8) t = ∑ a ∈ range 8, ((g8list.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t) := by
    unfold Gg
    apply Finset.sum_congr rfl
    intro a _
    simp [recGR, recG]
  rw [hG]
  exact cert_main g8list P8list 8 5 l05_hF l05_hP t

end Omega3
