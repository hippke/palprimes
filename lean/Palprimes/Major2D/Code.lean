import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-! # Kernel checker for 2D block majorants (computable part)

Cells at level `d`: centre `(J/N, K/N)`, `N = 2 Q₀ 2^d`, half-width `1/N`.  A trigonometric sum is a list of
terms `(U, V, c)` (`U V : ℤ`, `c : ℕ`) with a denominator `Dn`; its value is `Σ (c/Dn) cos(π(Ux + Vy))`
(`U, V` are doubled frequencies).  At a cell it is replaced by a degree-3 Taylor model in the box
coordinates `σ = π(x − J/N)/r`, `ρ = π(y − K/N)/r ∈ [−1, 1]` (`r = Rn/2^RB ≥ π/N`), built from a packed
table of `e(n/M)`, `M = 2N`.  All arithmetic is in `ℕ`/`ℤ`; no `Rat`. -/


noncomputable section

namespace Palprimes.M2

/-! ## Constants -/

/-- table scale `2^62` -/
def PP : ℕ := 62
/-- Taylor-model scale `2^64` -/
def QQ : ℕ := 64
/-- packed field width -/
def HW : ℕ := 160
/-- scale of `r` -/
def RB : ℕ := 80
/-- coefficient offset `2^80` -/
def OKc : ℕ := 1208925819614629174706176
/-- number of Taylor terms for table entries -/
def NT : ℕ := 28
def piLoN : ℕ := 314159265358979323846
def piHiN : ℕ := 314159265358979323847
def piD : ℕ := 100000000000000000000
def two64 : ℕ := 18446744073709551616
def two62 : ℕ := 4611686018427387904
def two160 : ℕ := 1461501637330902918203684832716283019655932542976
def two128 : ℕ := 340282366920938463463374607431768211456

/-- the factorial (core only; equals `Nat.factorial`). -/
def fct : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fct n

/-! ## Table entries: `floor((cos(2πn/M) + 1) 2^62)`, `floor((sin(2πn/M) + 1) 2^62)` -/

/-- `Σ_{k<m}` of the real (`k ≡ 0, 2 mod 4`) part of `i^k a^k b^(n−1−k) (n−1)!/k!`. -/
def tayRe (a b n : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => tayRe a b n m +
      (if m % 4 = 0 then ((a ^ m * b ^ (n - 1 - m) * (fct (n - 1) / fct m) : ℕ) : ℤ)
       else if m % 4 = 2 then -((a ^ m * b ^ (n - 1 - m) * (fct (n - 1) / fct m) : ℕ) : ℤ)
       else 0)

/-- the imaginary part (`k ≡ 1, 3 mod 4`). -/
def tayIm (a b n : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => tayIm a b n m +
      (if m % 4 = 1 then ((a ^ m * b ^ (n - 1 - m) * (fct (n - 1) / fct m) : ℕ) : ℤ)
       else if m % 4 = 3 then -((a ^ m * b ^ (n - 1 - m) * (fct (n - 1) / fct m) : ℕ) : ℤ)
       else 0)

/-- `clamp(floor((v + den) 2^62 / den))` to `[0, 2^64)`. -/
def roundE (v : ℤ) (den : ℕ) : ℕ := min ((((v + den) * two62) / (den : ℤ)).toNat) (two64 - 1)

/-- the table entry `(Cf, Sf)` for `n` (modulus `M`, `4 ∣ M`). -/
def entry (M n : ℕ) : ℕ × ℕ :=
  let q := 4 * n / M
  let rp := n - q * (M / 4)
  let a := 2 * piLoN * rp
  let b := piD * M
  let re := tayRe a b NT NT
  let im := tayIm a b NT NT
  let den := b ^ (NT - 1) * fct (NT - 1)
  let cs : ℤ × ℤ := if q = 0 then (re, im) else if q = 1 then (-im, re) else if q = 2 then (-re, -im) else (im, -re)
  (roundE cs.1 den, roundE cs.2 den)

/-- packed table entry `Cf + 2^64 Sf`. -/
def entryP (M n : ℕ) : ℕ := (entry M n).1 + two64 * (entry M n).2

/-- extraction of field `n` (width 128) of a packed table. -/
def getT (tab n : ℕ) : ℕ := Nat.mod (Nat.shiftRight tab (Nat.mul 128 n)) two128

def two63 : ℕ := 9223372036854775808

/-- `(Cf, Sf)` for `n < M` from the packed table (field `n`). -/
def lookE (tab _M n : ℕ) : ℕ × ℕ := (Nat.mod (getT tab n) two64, Nat.shiftRight (getT tab n) 64)

/-- table check: fields `0 … m−1` of `tab` are the entries. -/
def tabOK (M tab : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => Nat.beq (getT tab m) (entryP M m) && tabOK M tab m

/-! ## Packed sums -/

/-- monomial order: `1, σ, ρ, σ², σρ, ρ², σ³, σ²ρ, σρ², ρ³`. -/
def monA : List ℕ := [0, 1, 0, 2, 1, 0, 3, 2, 1, 0]
def monB : List ℕ := [0, 0, 1, 0, 1, 2, 0, 1, 2, 3]

/-- `κ_{ab} = c U^a V^b · 6/(a! b!)`. -/
def kap (U V : ℤ) (c : ℕ) (a b : ℕ) : ℤ := (c : ℤ) * U ^ a * V ^ b * ((6 / (fct a * fct b) : ℕ) : ℤ)

/-- packing of a list of field values (width `HW`). -/
def pk : List ℕ → ℕ
  | [] => 0
  | x :: l => x + two160 * pk l

/-- even monomials `(0,0), (2,0), (1,1), (0,2)` and a constant field. -/
def packE (U V : ℤ) (c : ℕ) : ℕ :=
  pk [(kap U V c 0 0 + OKc).toNat, (kap U V c 2 0 + OKc).toNat, (kap U V c 1 1 + OKc).toNat, (kap U V c 0 2 + OKc).toNat, 1]

/-- odd monomials `(1,0), (0,1), (3,0), (2,1), (1,2), (0,3)` and a constant field. -/
def packO (U V : ℤ) (c : ℕ) : ℕ :=
  pk [(kap U V c 1 0 + OKc).toNat, (kap U V c 0 1 + OKc).toNat, (kap U V c 3 0 + OKc).toNat, (kap U V c 2 1 + OKc).toNat,
    (kap U V c 1 2 + OKc).toNat, (kap U V c 0 3 + OKc).toNat, 1]

/-- A prepared term: offset frequencies and packed constants. -/
structure PTerm where
  Uo : ℕ
  Vo : ℕ
  KE : ℕ
  KO : ℕ

def prepT (O : ℕ) (t : ℤ × ℤ × ℕ) : PTerm :=
  ⟨(t.1 + O).toNat, (t.2.1 + O).toNat, packE t.1 t.2.1 t.2.2, packO t.1 t.2.1 t.2.2⟩

/-- the validity condition of one term. -/
def termOK (O : ℕ) (t : ℤ × ℤ × ℕ) : Bool :=
  decide (0 ≤ t.1 + O) && decide (0 ≤ t.2.1 + O) &&
    (List.zip monA monB).all (fun ab => decide ((kap t.1 t.2.1 t.2.2 ab.1 ab.2).natAbs < OKc))

/-- sums of the `κ`. -/
def skap (ts : List (ℤ × ℤ × ℕ)) (a b : ℕ) : ℤ := (ts.map (fun t => kap t.1 t.2.1 t.2.2 a b)).sum

/-- A prepared sum. -/
structure PSum where
  terms : List PTerm
  Dn : ℕ
  valid : Bool
  sk : List ℤ
  G0 : ℕ
  G4 : ℕ

def prepS (O : ℕ) (ts : List (ℤ × ℤ × ℕ)) (Dn : ℕ) : PSum where
  terms := ts.map (prepT O)
  Dn := Dn
  valid := decide (0 < Dn) && decide (ts.length < 16384) && ts.all (termOK O)
  sk := (List.zip monA monB).map (fun ab => skap ts ab.1 ab.2)
  G0 := (ts.map (fun t => t.2.2)).sum
  G4 := (ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum

/-! ## Signed numbers and Taylor models -/

/-- A signed number `p − n` (two naturals; never normalised in the hot path). -/
structure Z2 where
  p : ℕ
  n : ℕ

/-- its value -/
def Z2.v (z : Z2) : ℤ := (z.p : ℤ) - z.n
/-- `|z|` -/
def Z2.ab (z : Z2) : ℕ := Nat.add (Nat.sub z.p z.n) (Nat.sub z.n z.p)
def Z2.neg (z : Z2) : Z2 := ⟨z.n, z.p⟩
def Z2.nrm (z : Z2) : Z2 := ⟨Nat.sub z.p z.n, Nat.sub z.n z.p⟩
def Z2.mul (a b : Z2) : Z2 := ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
def Z2.add (a b : Z2) : Z2 := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
def Z2.sub (a b : Z2) : Z2 := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
def Z2.smul (k : ℕ) (a : Z2) : Z2 := ⟨Nat.mul k a.p, Nat.mul k a.n⟩
/-- `a < b` -/
def Z2.lt (a b : Z2) : Bool := Nat.blt (Nat.add a.p b.n) (Nat.add b.p a.n)

/-- A polynomial of degree ≤ 3 in the monomial order `1, σ, ρ, σ², σρ, ρ², σ³, σ²ρ, σρ², ρ³`. -/
structure Poly where
  c0 : Z2
  c1 : Z2
  c2 : Z2
  c3 : Z2
  c4 : Z2
  c5 : Z2
  c6 : Z2
  c7 : Z2
  c8 : Z2
  c9 : Z2

/-- A Taylor model: polynomial and remainder, both at scale `2^64`. -/
structure TM where
  p : Poly
  r : ℕ

/-- packed accumulation over the terms: `(Σ Cf·KE, Σ Sf·KO)`. -/
def accum (tab M J K : ℕ) (ts : List PTerm) : ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ × ℕ) (0, 0)
    (fun t _ ih =>
      let w := lookE tab M (Nat.mod (Nat.add (Nat.mul t.Uo J) (Nat.mul t.Vo K)) M)
      (Nat.add ih.1 (Nat.mul w.1 t.KE), Nat.add ih.2 (Nat.mul w.2 t.KO))) ts

/-- field `j` of a packed accumulator. -/
def fld (A j : ℕ) : ℕ := Nat.mod (Nat.shiftRight A (Nat.mul HW j)) two160

/-- `Rn ≥ π 2^RB / N`. -/
def Rn (N : ℕ) : ℕ := (piHiN * 2 ^ RB + (piD * N - 1)) / (piD * N)

/-- the coefficient of a monomial of degree `k` with sign `sg` from the field value `F`, the weight sum `sW` and
`Σκ = sp − sn`: `≈ sg (F − OK·sW − 2^62 (sp − sn)) Rn^k 2^64 / (6 Dn 2^62 2^(k RB))` (error `< 2`). -/
def coefOf (sg : Bool) (k : ℕ) (F sW sp sn rn Dn : ℕ) : Z2 :=
  let X := Nat.add F (Nat.mul two62 sn)
  let Y := Nat.add (Nat.mul OKc sW) (Nat.mul two62 sp)
  let m := rn ^ k * two64
  let den := 6 * Dn * two62 * 2 ^ (k * RB)
  let A := bif sg then Nat.sub X Y else Nat.sub Y X
  let B := bif sg then Nat.sub Y X else Nat.sub X Y
  ⟨Nat.div (Nat.mul A m) den, Nat.div (Nat.add (Nat.mul B m) (den - 1)) den⟩

/-- the remainder `ceil(2^64 [G4 r⁴ (1 + 8/2^62)/24 + 8 G0/2^62] / Dn) + 20`, `r = rn/2^RB`. -/
def remOf (S : PSum) (rn : ℕ) : ℕ :=
  let num := two64 * S.G4 * rn ^ 4 * (two62 + 8) + 8 * S.G0 * two64 * 24 * 2 ^ (4 * RB)
  let den := 24 * 2 ^ (4 * RB) * two62 * S.Dn
  (num + (den - 1)) / den + 20

def skP (S : PSum) (i : ℕ) : ℕ := (S.sk.getD i 0).toNat
def skN (S : PSum) (i : ℕ) : ℕ := (-(S.sk.getD i 0)).toNat

/-- The Taylor model of a prepared sum at the cell `(J, K)` with table `tab` (modulus `M`), `N = M/2`. -/
def tmS (S : PSum) (tab M J K : ℕ) : TM :=
  let rn := Rn (M / 2)
  let A := accum tab M J K S.terms
  let AE := A.1
  let AO := A.2
  let sC := Nat.shiftRight AE (Nat.mul HW 4)
  let sS := Nat.shiftRight AO (Nat.mul HW 6)
  ⟨⟨coefOf true 0 (fld AE 0) sC (skP S 0) (skN S 0) rn S.Dn,
    coefOf false 1 (fld AO 0) sS (skP S 1) (skN S 1) rn S.Dn,
    coefOf false 1 (fld AO 1) sS (skP S 2) (skN S 2) rn S.Dn,
    coefOf false 2 (fld AE 1) sC (skP S 3) (skN S 3) rn S.Dn,
    coefOf false 2 (fld AE 2) sC (skP S 4) (skN S 4) rn S.Dn,
    coefOf false 2 (fld AE 3) sC (skP S 5) (skN S 5) rn S.Dn,
    coefOf true 3 (fld AO 2) sS (skP S 6) (skN S 6) rn S.Dn,
    coefOf true 3 (fld AO 3) sS (skP S 7) (skN S 7) rn S.Dn,
    coefOf true 3 (fld AO 4) sS (skP S 8) (skN S 8) rn S.Dn,
    coefOf true 3 (fld AO 5) sS (skP S 9) (skN S 9) rn S.Dn⟩, remOf S rn⟩

/-! ## Products of sums -/

/-- `cos a cos b = (cos(a+b) + cos(a−b))/2`. -/
def comb (s t : List (ℤ × ℤ × ℕ)) : List (ℤ × ℤ × ℕ) :=
  s.flatMap (fun a => t.flatMap (fun c => [(a.1 + c.1, a.2.1 + c.2.1, a.2.2 * c.2.2), (a.1 - c.1, a.2.1 - c.2.1, a.2.2 * c.2.2)]))

def prodL : List (List (ℤ × ℤ × ℕ) × ℕ) → List (ℤ × ℤ × ℕ) × ℕ
  | [] => ([(0, 0, 1)], 1)
  | [s] => s
  | s :: t :: rest => (comb s.1 (prodL (t :: rest)).1, 2 * s.2 * (prodL (t :: rest)).2)

/-- the factors not frozen by `mask` (bit `i` set = factor `i` frozen). -/
def selF (mask : ℕ) : ℕ → List (List (ℤ × ℤ × ℕ) × ℕ) → List (List (ℤ × ℤ × ℕ) × ℕ)
  | _, [] => []
  | i, f :: fs => if Nat.testBit mask i then selF mask (i + 1) fs else f :: selF mask (i + 1) fs

/-! ## Polynomial lower bound -/

def Poly.c3sum (h : Poly) : ℕ := h.c6.ab + h.c7.ab + h.c8.ab + h.c9.ab
def Poly.c12sum (h : Poly) : ℕ := h.c1.ab + h.c2.ab + h.c3.ab + h.c4.ab + h.c5.ab

/-- the positive-definite bound: `a = h₂₀ > 0`, `D = 4ac − b² > 0`, `N = c g₁² − b g₁ g₂ + a g₂² < base·D`. -/
def pdOK (g1 g2 a b c base : Z2) : Bool :=
  let D := Z2.sub (Z2.smul 4 (Z2.mul a c)) (Z2.mul b b)
  let Nn := Z2.add (Z2.sub (Z2.mul c (Z2.mul g1 g1)) (Z2.mul b (Z2.mul g1 g2))) (Z2.mul a (Z2.mul g2 g2))
  Nat.blt a.n a.p && Z2.lt ⟨0, 0⟩ D && Z2.lt Nn (Z2.mul base D)

/-- certified `min_{[−1,1]²} h > rem`. -/
def lowOK (h : Poly) (rem : ℕ) : Bool :=
  let base : Z2 := ⟨h.c0.p, h.c0.n + (h.c3sum + rem)⟩
  Nat.blt (h.c12sum + base.n) base.p ||
    pdOK h.c1.nrm h.c2.nrm h.c3.nrm h.c4.nrm h.c5.nrm base.nrm

/-! ## Power bound `x^(−1/n0)` -/

/-- field `j` (width 128) of a packed table. -/
def getV (V j : ℕ) : ℕ := Nat.mod (Nat.shiftRight V (Nat.mul 128 j)) two128

/-- upper bound (scale `2^64`) of `(X/2^64)^(−1/n0)` for `1 ≤ X ≤ 2^64`, from `U2 ≥ 2^(1/n0) 2^64` and
`V_j ≥ (1 + j/256)^(−1/n0) 2^64`. -/
def powInv (U2 V X : ℕ) : ℕ :=
  let L := Nat.log2 X
  let e := QQ - L
  let j := Nat.shiftRight (Nat.shiftLeft X 8) L - 256
  (U2 ^ e * getV V j + (2 ^ (QQ * e) - 1)) / 2 ^ (QQ * e)

def cdivN (a b : ℕ) : ℕ := (a + (b - 1)) / b

/-! ## The cell test -/

/-- Base configuration. -/
structure Cfg where
  l : ℕ
  Q0 : ℕ
  n0 : ℕ
  dmin : ℕ
  dmax : ℕ
  O : ℕ
  T : PSum
  facs : List (List (ℤ × ℤ × ℕ) × ℕ)
  facP : List PSum
  thr : List ℕ
  U2 : ℕ
  V : ℕ
  tab : ℕ → ℕ
  Aps : List PSum

/-- the invalid sum (default of `getD`). -/
def badS : PSum := ⟨[], 1, false, [], 0, 0⟩

/-- `prepS` of the product of the non-frozen factors, for masks `m, m+1, …, m+c−1`. -/
def apsFrom (O : ℕ) (facs : List (List (ℤ × ℤ × ℕ) × ℕ)) (m : ℕ) : ℕ → List PSum
  | 0 => []
  | c + 1 => prepS O (prodL (selF m 0 facs)).1 (prodL (selF m 0 facs)).2 :: apsFrom O facs (m + 1) c

def one : ℕ := two64

/-- per-factor data from its Taylor model: `(sign ≥ 0, definite, sup, |c₀|)`. -/
def facInfo (m : TM) : Bool × Bool × ℕ × ℕ :=
  let rest : ℕ := m.p.c1.ab + m.p.c2.ab + m.p.c3.ab + m.p.c4.ab + m.p.c5.ab + m.p.c6.ab + m.p.c7.ab + m.p.c8.ab + m.p.c9.ab
  (Nat.ble m.p.c0.n m.p.c0.p, Nat.ble (rest + m.r) m.p.c0.ab, min one (m.p.c0.ab + rest + m.r), m.p.c0.ab)

/-- the freeze mask for threshold `θ`: non-definite factors and factors with `|c₀| < θ`. -/
def maskOf (θ : ℕ) : ℕ → List (Bool × Bool × ℕ × ℕ) → ℕ
  | _, [] => 0
  | i, a :: rest => maskOf θ (i + 1) rest + (if (!a.2.1) || decide (a.2.2.2 < θ) then 2 ^ i else 0)

/-- product of the sups of the frozen factors (scale `2^64`, rounded up). -/
def supProd (mask : ℕ) : ℕ → List (Bool × Bool × ℕ × ℕ) → ℕ
  | _, [] => one
  | i, a :: rest => if Nat.testBit mask i then cdivN (supProd mask (i + 1) rest * a.2.2.1) one else supProd mask (i + 1) rest

/-- sign of the product of the non-frozen factors (`true` = nonnegative). -/
def sgnProd (mask : ℕ) : ℕ → List (Bool × Bool × ℕ × ℕ) → Bool
  | _, [] => true
  | i, a :: rest => if Nat.testBit mask i then sgnProd mask (i + 1) rest else (sgnProd mask (i + 1) rest == a.1)

/-- all non-frozen factors are definite. -/
def defAll (mask : ℕ) : ℕ → List (Bool × Bool × ℕ × ℕ) → Bool
  | _, [] => true
  | i, a :: rest => (Nat.testBit mask i || a.2.1) && defAll mask (i + 1) rest

def Poly.neg (h : Poly) : Poly := ⟨h.c0.neg, h.c1.neg, h.c2.neg, h.c3.neg, h.c4.neg, h.c5.neg, h.c6.neg, h.c7.neg, h.c8.neg, h.c9.neg⟩

/-- `t·2^64 − K1·a` -/
def combZ (t a : Z2) (K1 : ℕ) : Z2 := ⟨Nat.add (Nat.mul t.p one) (Nat.mul K1 a.n), Nat.add (Nat.mul t.n one) (Nat.mul K1 a.p)⟩

/-- `t 2^64 − K1 a − K0 2^64` coefficientwise. -/
def combH (t a : Poly) (K1 K0 : ℕ) : Poly :=
  ⟨Z2.sub (combZ t.c0 a.c0 K1) ⟨Nat.mul K0 one, 0⟩, combZ t.c1 a.c1 K1, combZ t.c2 a.c2 K1, combZ t.c3 a.c3 K1,
   combZ t.c4 a.c4 K1, combZ t.c5 a.c5 K1, combZ t.c6 a.c6 K1, combZ t.c7 a.c7 K1, combZ t.c8 a.c8 K1, combZ t.c9 a.c9 K1⟩

/-- one freeze option. -/
def optOK (C : Cfg) (tab M J K : ℕ) (tT : TM) (info : List (Bool × Bool × ℕ × ℕ)) (mask : ℕ) : Bool :=
  let S := C.Aps.getD mask badS
  let mA := tmS S tab M J K
  let pa := if sgnProd mask 0 info then mA.p else mA.p.neg
  let St := supProd mask 0 info
  let Ct := min one (max (Nat.sub pa.c0.p pa.c0.n) 1)
  let X := St * Ct / one
  let pe := powInv C.U2 C.V X
  let Wt := cdivN (St * pe) one
  let K1 := cdivN (Wt * (C.n0 - 1)) C.n0
  let K0 := cdivN (Wt * Ct) (C.n0 * one)
  S.valid && defAll mask 0 info && decide (1 ≤ X) && lowOK (combH tT.p pa K1 K0) (tT.r * one + K1 * mA.r)

/-- try the thresholds in order (skipping repeated masks). -/
def tryOpts (C : Cfg) (tab M J K : ℕ) (tT : TM) (info : List (Bool × Bool × ℕ × ℕ)) : List ℕ → ℕ → Bool
  | [], _ => false
  | θ :: rest, prev =>
    let m := maskOf θ 0 info
    (decide (m ≠ prev) && optOK C tab M J K tT info m) || tryOpts C tab M J K tT info rest m

/-- the cell test at level `d`, centre `(J, K)/N`. -/
def cellOK (C : Cfg) (d J K : ℕ) : Bool :=
  let M := 4 * C.Q0 * 2 ^ d
  let tab := C.tab d
  let tT := tmS C.T tab M J K
  let info := C.facP.map (fun S => facInfo (tmS S tab M J K))
  Nat.ble C.dmin d && C.T.valid && C.facP.all (fun S => S.valid) && tryOpts C tab M J K tT info C.thr (2 ^ 30)

/-- adaptive refinement with fuel. -/
def checkRec (C : Cfg) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, d, J, K => cellOK C d J K
  | f + 1, d, J, K => cellOK C d J K ||
      (checkRec C f (d + 1) (2 * J - 1) (2 * K - 1) && checkRec C f (d + 1) (2 * J + 1) (2 * K - 1) &&
       checkRec C f (d + 1) (2 * J - 1) (2 * K + 1) && checkRec C f (d + 1) (2 * J + 1) (2 * K + 1))

/-- all level-0 cells of a list. -/
def checkList (C : Cfg) (L : List (ℕ × ℕ)) : Bool :=
  L.all (fun jk => checkRec C C.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1))

end Palprimes.M2

end
