import Mathlib

/-!
# M12 helper: the computable `h`-table checker (Nat fixed point, scale `TT = 2^64`)

A grid `g` has `x` cells `ξ_j = ρ^j/85` (`ρ = A/B`, `j < N`, `ξ_N ≥ 1/3`) and fine `y` points
`v_σ = ρ^s (1 + r(ρ − 1)/M)` (`σ = sM + r`), `y_σ = 1 − 1/v_σ`, caps `γ_σ = v_σ − 1`.
Tables `tab_i[k][j]` bound `G_i(x, c)` for `x ∈ [ξ_j, ξ_{j+1}]`, `c ≤ γ_k` (row `SY`: any cap).
-/

set_option linter.style.longLine false

namespace Omega3.M12

structure Grid where
  A : ℕ
  B : ℕ
  M : ℕ
  N : ℕ
  SY : ℕ
  SH : ℕ
  S3 : ℕ

def PP : ℕ := 64
def TT : ℕ := 2 ^ PP

/-! ## Elementary functions -/

def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

def findFirst (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, f + 1 => if p s then s else findFirst p (s + 1) f

/-- Elementwise sum with default `0`. -/
def zadd : List ℕ → List ℕ → List ℕ
  | [], l => l
  | a :: t, l => (a + l.headD 0) :: zadd t l.tail

/-- Prefix accumulation: `[acc, f acc a₀, f (f acc a₀) a₁, …]`. -/
def prefixGen {α : Type} (f : List ℕ → α → List ℕ) : List ℕ → List α → List (List ℕ)
  | acc, [] => [acc]
  | acc, a :: as => acc :: prefixGen f (f acc a) as

/-- `fuse w n acc row = acc + [⌈w max(row_j, row_{j+1})/TT⌉ for j < n]`. -/
def fuse (w : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, acc, _ => acc
  | n + 1, acc, row => match row with
    | [] => acc
    | a :: t => (acc.headD 0 + cdiv (w * max a (t.headD 0)) TT) :: fuse w n acc.tail t

/-! ## Grid numerators -/

def vnum (g : Grid) (σ : ℕ) : ℕ := g.A ^ (σ / g.M) * (g.M * g.B + σ % g.M * (g.A - g.B))
def vden (g : Grid) (σ : ℕ) : ℕ := g.B ^ (σ / g.M) * (g.M * g.B)

/-- `y_σ ≤ ξ_J`. -/
def yleX (g : Grid) (σ J : ℕ) : Bool := (vnum g σ - vden g σ) * (85 * g.B ^ J) ≤ g.A ^ J * vnum g σ
/-- `γ_k ≤ y_t`. -/
def gleY (g : Grid) (k t : ℕ) : Bool := (vnum g k - vden g k) * vnum g t ≤ (vnum g t - vden g t) * vden g k

def JL (g : Grid) (σ : ℕ) : ℕ := findFirst (fun J => yleX g (σ + 1) J) 0 g.N
def SMT (g : Grid) (k : ℕ) : ℕ := if k < g.SY then findFirst (gleY g k) 0 g.SY else g.SY
def CUT (g : Grid) (k : ℕ) : ℕ := if k < g.SY then findFirst (gleY g k) g.S3 (g.SH - g.S3) else g.SH

/-- Weight `≥ TT (v_{σ+1} − v_σ)/(v_σ − 1)`. -/
def wt (g : Grid) (σ : ℕ) : ℕ := cdiv (TT * (g.A ^ (σ / g.M) * (g.A - g.B))) (vnum g σ - vden g σ)

/-! ## Fixed-point approximations for the first level -/

def X0dn (g : Grid) (j : ℕ) : ℕ := TT * g.A ^ j / (85 * g.B ^ j)
def X1up (g : Grid) (j : ℕ) : ℕ := cdiv (TT * g.A ^ (j + 1)) (85 * g.B ^ (j + 1))
def TOP (g : Grid) (j : ℕ) : ℕ := cdiv (TT - X0dn g j) 2
def YDN (g : Grid) (σ : ℕ) : ℕ := TT * (vnum g σ - vden g σ) / vnum g σ
def YUP (g : Grid) (σ : ℕ) : ℕ := cdiv (TT * (vnum g σ - vden g σ)) (vnum g σ)
def THIRD : ℕ := TT / 3

/-- Bound for `TT ∫_{cell σ, 1/3 < z < (1 − x)/2} dz/(z(1 − x − z))`, `x ∈ [ξ_j, ξ_{j+1}]`. -/
def bterm (x1 top ydn yup1 : ℕ) : ℕ :=
  if top ≤ ydn then 0 else
    cdiv (TT * TT * (min yup1 top - max ydn THIRD)) (max ydn THIRD * (TT - x1 - min yup1 top))

/-- `acc + [bterm (xs_j) yd yu]`. -/
def addB (yd yu : ℕ) : List ℕ → List (ℕ × ℕ) → List ℕ
  | acc, [] => acc
  | acc, p :: ps => (acc.headD 0 + bterm p.1 p.2 yd yu) :: addB yd yu acc.tail ps

def xdat (g : Grid) : List (ℕ × ℕ) := (List.range g.N).map (fun j => (X1up g j, TOP g j))

def baseAcc (g : Grid) : List (List ℕ) :=
  prefixGen (fun acc σ => addB (YDN g σ) (YUP g (σ + 1)) acc (xdat g)) [] ((List.range (g.SH - g.S3)).map (g.S3 + ·))

def tab1 (g : Grid) : List (List ℕ) :=
  let acc := baseAcc g
  (List.range (g.SY + 1)).map (fun k => acc.getD (CUT g k - g.S3) [])

/-! ## The recursion step -/

def sdat (g : Grid) : List (ℕ × ℕ × ℕ) := (List.range g.SY).map (fun σ => (σ / g.M, wt g σ, JL g σ))

def stepF (acc : List ℕ) (it : (ℕ × ℕ × ℕ) × List ℕ) : List ℕ := fuse it.1.2.1 it.1.2.2 acc (it.2.drop it.1.1)

def step (g : Grid) (tab : List (List ℕ)) : List (List ℕ) :=
  let acc := prefixGen stepF [] (List.zip (sdat g) (tab.drop 1))
  (List.range (g.SY + 1)).map (fun k => acc.getD (SMT g k) [])

/-- `run g n tab acc`: adds the top rows of `step² tab, step⁴ tab, …` (`n` of them) to `acc`, where the
first added row is `step tab`'s top row. -/
def run (g : Grid) : ℕ → List (List ℕ) → List ℕ → List ℕ
  | 0, _, acc => acc
  | n + 1, tab, acc =>
    let t2 := step g tab
    run g n (step g t2) (zadd acc (t2.getD g.SY []))

/-! ## The two grids -/

/-- Fine grid: `ρ = 101/100`, `M = 16` (levels 1 and 2). -/
def gF : Grid := ⟨101, 100, 16, 337, 652, 1115, 651⟩
/-- Coarse grid: `ρ = (101/100)²`, `M = 8` (levels 1 to 17), every coarse cell is two fine cells. -/
def gC : Grid := ⟨10201, 10000, 8, 169, 163, 279, 162⟩

/-- Fine level-2 top row. -/
def h2F : List ℕ := (step gF (tab1 gF)).getD gF.SY []

/-- Coarse even levels `4, 6, …, 16`, top rows summed. -/
def restC : List ℕ := run gC 7 (step gC (step gC (tab1 gC))) []

/-! ## Side checks -/

def sideOK (g : Grid) : Bool :=
  JL g 0 == 0 && (List.range g.N).all (fun j => X1up g j + TOP g j < TT)

end Omega3.M12
