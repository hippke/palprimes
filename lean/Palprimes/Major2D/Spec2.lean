import Palprimes.Major2D.Comp2
import Palprimes.Major2D.Sym

/-! # The power-table checks imply the hypotheses of `CfgOK` -/

namespace Palprimes.M2

theorem u2Chk_spec (U2 n0 : ℕ) (h : u2Chk U2 n0 = true) : 2 * 2 ^ (64 * n0) ≤ U2 ^ n0 := by
  unfold u2Chk at h; exact Nat.le_of_ble_eq_true h

theorem vChk_spec (V n0 : ℕ) (h : vChk V n0 = true) : ∀ j < 256, 256 * 2 ^ (64 * n0) ≤ getV V j ^ n0 * (256 + j) := by
  intro j hj
  unfold vChk at h
  exact Nat.le_of_ble_eq_true (allN_spec _ _ h j hj)

end Palprimes.M2
