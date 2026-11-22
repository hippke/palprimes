import Palprimes.Major2D.B2Data

/-! # Base 2: configuration of the checker -/


namespace Palprimes.M2

/-- the factors `cos(π(2^i x + 2^(6−i) y))`, doubled frequencies. -/
def facs2 : List (List (ℤ × ℤ × ℕ) × ℕ) :=
  [([(1, 64, 1)], 1), ([(2, 32, 1)], 1), ([(4, 16, 1)], 1), ([(8, 8, 1)], 1), ([(16, 4, 1)], 1), ([(32, 2, 1)], 1),
   ([(64, 1, 1)], 1)]

def O2 : ℕ := 4 * 192 * 2 ^ 24

def cfg2 : Cfg where
  l := 7
  Q0 := 192
  n0 := 1000
  dmin := 1
  dmax := 5
  O := O2
  T := prepS O2 T2terms 4503599627370496
  facs := facs2
  facP := facs2.map (fun f => prepS O2 f.1 f.2)
  thr := [0]
  U2 := U2_2
  V := V2
  tab := tab2
  Aps := apsFrom O2 facs2 0 (2 ^ 7)

def shifts2 : List (ℤ × ℤ) := Lam2.map (fun ac => ((ac.1 : ℤ), (ac.2 : ℤ))) ++ [(3, 0), (0, 3)]

def G2 : List (Bool × Bool × ℕ × ℕ) :=
  [false, true].flatMap (fun sw => [false, true].flatMap (fun ng => Lam2.map (fun ac => (sw, ng, ac.1, ac.2))))

end Palprimes.M2
