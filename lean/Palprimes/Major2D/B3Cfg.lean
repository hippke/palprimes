import Palprimes.Major2D.B3Data

/-! # Base 3: configuration of the checker -/


namespace Palprimes.M2

/-- the factors `(1 + 2 cos 2π(3^i x + 3^(2−i) y))/3`, doubled frequencies. -/
def facs3 : List (List (ℤ × ℤ × ℕ) × ℕ) :=
  [([(0, 0, 1), (2, 18, 2)], 3), ([(0, 0, 1), (6, 6, 2)], 3), ([(0, 0, 1), (18, 2, 2)], 3)]

def O3 : ℕ := 4 * 64 * 2 ^ 24

def cfg3 : Cfg where
  l := 3
  Q0 := 64
  n0 := 50
  dmin := 0
  dmax := 5
  O := O3
  T := prepS O3 T3terms 4503599627370496
  facs := facs3
  facP := facs3.map (fun f => prepS O3 f.1 f.2)
  thr := [0, 2767011611056432742, 5534023222112865484, 9223372036854775808, 13835058055282163712, 36893488147419103232]
  U2 := U2_3
  V := V3
  tab := tab3
  Aps := apsFrom O3 facs3 0 (2 ^ 3)

def shifts3 : List (ℤ × ℤ) := Lam3.map (fun ac => ((ac.1 : ℤ), (ac.2 : ℤ))) ++ [(8, 0), (0, 8)]

def G3 : List (Bool × Bool × ℕ × ℕ) :=
  [false, true].flatMap (fun sw => [false, true].flatMap (fun ng => Lam3.map (fun ac => (sw, ng, ac.1, ac.2))))

end Palprimes.M2
