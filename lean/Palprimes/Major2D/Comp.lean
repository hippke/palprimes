import Palprimes.Major2D.Code

/-! # Computable checks used by the symmetry and majorant files (core only, so that `^` is `Nat.pow`) -/

noncomputable section

namespace Palprimes.M2

/-- the shift condition: all phase shifts `π(Ua + Vc)/m` are `≡ eπ (mod 2π)`. -/
def shiftOK (ts : List (ℤ × ℤ × ℕ)) (a c m : ℤ) (e : ℤ) : Bool :=
  ts.all (fun t => decide ((t.1 * a + t.2.1 * c - e * m) % (2 * m) = 0))


def swpT (t : ℤ × ℤ × ℕ) : ℤ × ℤ × ℕ := (t.2.1, t.1, t.2.2)

/-- normalise the sign of a frequency (`cos` is even). -/
def nrmT (t : ℤ × ℤ × ℕ) : ℤ × ℤ × ℕ := if t.1 < 0 ∨ (t.1 = 0 ∧ t.2.1 < 0) then (-t.1, -t.2.1, t.2.2) else t


/-- `∀ i < n, p i`. -/
def allN (p : ℕ → Bool) (n : ℕ) : Bool := Nat.rec (motive := fun _ => Bool) true (fun i ih => ih && p i) n


/-- the bitmap of a cell list. -/
def bmap (Q0 : ℕ) (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun jk acc => Nat.lor acc (2 ^ (jk.1 * Q0 + jk.2))) 0


/-- a group element `(swap, negate, a, c)` acting on cell indices. -/
def imgC (Q0 st : ℕ) (g : Bool × Bool × ℕ × ℕ) (j k : ℕ) : ℕ × ℕ :=
  let p1 : ℕ × ℕ := if g.1 then (k, j) else (j, k)
  let p2 : ℕ × ℕ := if g.2.1 then (Q0 - 1 - p1.1, Q0 - 1 - p1.2) else p1
  ((p2.1 + g.2.2.1 * st) % Q0, (p2.2 + g.2.2.2 * st) % Q0)

/-- the covering check. -/
def coverOK (Q0 st : ℕ) (G : List (Bool × Bool × ℕ × ℕ)) (L : List (ℕ × ℕ)) : Bool :=
  let bm := bmap Q0 L
  allN (fun j => allN (fun k => G.any (fun g => Nat.testBit bm ((imgC Q0 st g j k).1 * Q0 + (imgC Q0 st g j k).2))) Q0) Q0


/-- lookup of a key. -/
def lk : List ((ℤ × ℤ) × ℕ) → ℤ × ℤ → ℕ
  | [], _ => 0
  | e :: L, w => if e.1 = w then e.2 else lk L w


/-- the full terms of one half term `(U, V, c)` (doubled frequency, doubled coefficient). -/
def expandH (t : ℤ × ℤ × ℕ) : List ((ℤ × ℤ) × ℕ) :=
  if t.1 = 0 ∧ t.2.1 = 0 then [((0, 0), t.2.2)] else [((t.1 / 2, t.2.1 / 2), t.2.2 / 2), ((-(t.1 / 2), -(t.2.1 / 2)), t.2.2 / 2)]

/-- evenness of the half list. -/
def evenOK (Th : List (ℤ × ℤ × ℕ)) : Bool :=
  Th.all (fun t => (t.1 = 0 ∧ t.2.1 = 0) || (t.1 % 2 = 0 && t.2.1 % 2 = 0 && t.2.2 % 2 = 0))


/-- the two sides of the exponent conditions: `x^D b^N1 (2b²+1)^N2` and `(3b²)^N2 (2^52)^D`. -/
def condL (xn D b N1 N2 : ℕ) : ℕ := Nat.mul (Nat.mul (Nat.pow xn D) (Nat.pow b N1)) (Nat.pow (Nat.add (Nat.mul 2 (Nat.mul b b)) 1) N2)
def condR (D b N2 : ℕ) : ℕ := Nat.mul (Nat.pow (Nat.mul 3 (Nat.mul b b)) N2) (Nat.pow 4503599627370496 D)

end Palprimes.M2

end
