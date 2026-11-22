import Palprimes.Major2D.Code

/-! # Range checks of the phase tables (one declaration per range keeps the kernel memory small) -/

noncomputable section

namespace Palprimes.M2

/-- fields `a … a+n−1` of `tab` are the entries. -/
def tabOKr (M tab a : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => Nat.beq (getT tab (a + n)) (entryP M (a + n)) && tabOKr M tab a n

end Palprimes.M2

end
