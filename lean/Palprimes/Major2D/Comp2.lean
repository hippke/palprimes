import Palprimes.Major2D.Comp

/-! # Core-only checks of the power tables (exponents beyond the elaborator's evaluation threshold) -/

noncomputable section

namespace Palprimes.M2

def u2Chk (U2 n0 : ℕ) : Bool := Nat.ble (2 * 2 ^ (64 * n0)) (U2 ^ n0)

def vChk (V n0 : ℕ) : Bool := allN (fun j => Nat.ble (256 * 2 ^ (64 * n0)) (getV V j ^ n0 * (256 + j))) 256

end Palprimes.M2

end
