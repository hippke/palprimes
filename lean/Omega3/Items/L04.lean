import Omega3.Statements
import Omega3.Items.L04_Gen

namespace Omega3

open Finset Palprimes Omega3.L04g

theorem l04_hF : chkP (Fpoly g6list 6 P6list 3) 60 (-1) 1 = true := by decide +kernel

theorem l04_hP : chkP (Ppoly P6list 3) 60 (-1) 1 = true := by decide +kernel

theorem itemL04 : ItemL04 := by
  intro t
  have hG : Gg 6 (recGR 6) t = ∑ a ∈ range 6, ((g6list.getD a 0 : ℚ) : ℂ) * ee ((a : ℝ) * t) := by
    unfold Gg
    apply Finset.sum_congr rfl
    intro a _
    simp [recGR, recG]
  rw [hG]
  exact cert_main g6list P6list 6 3 l04_hF l04_hP t

end Omega3
