import Palprimes.Major2D.Code
import Palprimes.Major2D.Taylor

/-! # Soundness of the 2D kernel checker, part 1: Taylor models of trigonometric sums -/

set_option linter.style.longLine false

open Real

namespace Palprimes.M2

/-! ## Semantics -/

/-- `Σ (c/Dn) cos(π(Ux + Vy))`. -/
noncomputable def sumVal (ts : List (ℤ × ℤ × ℕ)) (Dn : ℕ) (x y : ℝ) : ℝ :=
  (ts.map (fun t => (t.2.2 : ℝ) * Real.cos (π * (t.1 * x + t.2.1 * y)))).sum / Dn

/-- real value of a signed pair -/
noncomputable def Z2.r (z : Z2) : ℝ := (z.p : ℝ) - z.n

/-- evaluation of a polynomial (unscaled). -/
noncomputable def Poly.ev (h : Poly) (s t : ℝ) : ℝ :=
  h.c0.r + h.c1.r * s + h.c2.r * t + h.c3.r * s ^ 2 + h.c4.r * (s * t) + h.c5.r * t ^ 2 +
    h.c6.r * s ^ 3 + h.c7.r * (s ^ 2 * t) + h.c8.r * (s * t ^ 2) + h.c9.r * t ^ 3

/-- a Taylor model of `f` on `[−1,1]²` (scale `2^64`). -/
def TMok (f : ℝ → ℝ → ℝ) (m : TM) : Prop :=
  ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 → |f s t - m.p.ev s t / 2 ^ 64| ≤ (m.r : ℝ) / 2 ^ 64

/-! ## One term -/

theorem cos_sin_sq_bound (ψ : ℝ) :
    |Real.cos ψ - (1 - ψ ^ 2 / 2)| ≤ ψ ^ 4 / 24 ∧ |Real.sin ψ - (ψ - ψ ^ 3 / 6)| ≤ ψ ^ 4 / 24 ∧
      ∀ φ : ℝ, |Real.cos φ * (Real.cos ψ - (1 - ψ ^ 2 / 2)) - Real.sin φ * (Real.sin ψ - (ψ - ψ ^ 3 / 6))| ≤ ψ ^ 4 / 24 := by
  have h := cos_sin_taylor4 ψ
  have h0 : 0 ≤ ψ ^ 4 / 24 := by positivity
  set a := Real.cos ψ - (1 - ψ ^ 2 / 2)
  set b := Real.sin ψ - (ψ - ψ ^ 3 / 6)
  refine ⟨?_, ?_, ?_⟩
  · apply abs_le_of_sq_le_sq' _ h0 |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    nlinarith [sq_nonneg b]
  · apply abs_le_of_sq_le_sq' _ h0 |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    nlinarith [sq_nonneg a]
  · intro φ
    have hcs := Real.cos_sq_add_sin_sq φ
    apply abs_le_of_sq_le_sq' _ h0 |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    have : (Real.cos φ * a - Real.sin φ * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (Real.cos φ * b + Real.sin φ * a)]
    linarith

/-- **One term**: `cos(φ₀ + ψ)` against `ĉ(1 − ψ²/2) − ŝ(ψ − ψ³/6)`. -/
theorem term_bound (φ ψ cc ss ε : ℝ) (hc : |cc - Real.cos φ| ≤ ε) (hs : |ss - Real.sin φ| ≤ ε) :
    |Real.cos (φ + ψ) - (cc * (1 - ψ ^ 2 / 2) - ss * (ψ - ψ ^ 3 / 6))| ≤ 2 * ε + (1 + 2 * ε) * (ψ ^ 4 / 24) := by
  obtain ⟨ha, hb, hab⟩ := cos_sin_sq_bound ψ
  have hab := hab φ
  set a := Real.cos ψ - (1 - ψ ^ 2 / 2)
  set b := Real.sin ψ - (ψ - ψ ^ 3 / 6)
  have e : Real.cos (φ + ψ) - (cc * (1 - ψ ^ 2 / 2) - ss * (ψ - ψ ^ 3 / 6)) =
      (Real.cos φ - cc) * Real.cos ψ - (Real.sin φ - ss) * Real.sin ψ + (Real.cos φ * a - Real.sin φ * b) +
        ((cc - Real.cos φ) * a - (ss - Real.sin φ) * b) := by
    rw [Real.cos_add]; simp only [a, b]; ring
  rw [e]
  have h1 : |(Real.cos φ - cc) * Real.cos ψ| ≤ ε := by
    rw [abs_mul, abs_sub_comm]
    exact le_trans (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ψ) (abs_nonneg _)) (by rw [mul_one]; exact hc)
  have h2 : |(Real.sin φ - ss) * Real.sin ψ| ≤ ε := by
    rw [abs_mul, abs_sub_comm]
    exact le_trans (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one ψ) (abs_nonneg _)) (by rw [mul_one]; exact hs)
  have h3 : |(cc - Real.cos φ) * a| ≤ ε * (ψ ^ 4 / 24) := by
    rw [abs_mul]; exact mul_le_mul hc ha (abs_nonneg _) (le_trans (abs_nonneg _) hc)
  have h4 : |(ss - Real.sin φ) * b| ≤ ε * (ψ ^ 4 / 24) := by
    rw [abs_mul]; exact mul_le_mul hs hb (abs_nonneg _) (le_trans (abs_nonneg _) hs)
  calc _ ≤ |(Real.cos φ - cc) * Real.cos ψ - (Real.sin φ - ss) * Real.sin ψ| + |Real.cos φ * a - Real.sin φ * b| +
          |(cc - Real.cos φ) * a - (ss - Real.sin φ) * b| := abs_add_three _ _ _
    _ ≤ (ε + ε) + ψ ^ 4 / 24 + (ε * (ψ ^ 4 / 24) + ε * (ψ ^ 4 / 24)) := by
        gcongr
        · exact le_trans (abs_sub _ _) (add_le_add h1 h2)
        · exact le_trans (abs_sub _ _) (add_le_add h3 h4)
    _ = _ := by ring


/-! ## The coefficients `κ` -/

theorem kap_vals (U V : ℤ) (c : ℕ) :
    kap U V c 0 0 = 6 * c ∧ kap U V c 1 0 = 6 * c * U ∧ kap U V c 0 1 = 6 * c * V ∧ kap U V c 2 0 = 3 * c * U ^ 2 ∧
    kap U V c 1 1 = 6 * c * U * V ∧ kap U V c 0 2 = 3 * c * V ^ 2 ∧ kap U V c 3 0 = c * U ^ 3 ∧
    kap U V c 2 1 = 3 * c * U ^ 2 * V ∧ kap U V c 1 2 = 3 * c * U * V ^ 2 ∧ kap U V c 0 3 = c * V ^ 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [kap, fct] <;> ring

/-- the Taylor polynomial of one term with table weights `Cf, Sf`. -/
noncomputable def termPoly (U V : ℤ) (c Cf Sf : ℕ) (r s t : ℝ) : ℝ :=
  let ψ := r * (U * s + V * t)
  (c : ℝ) * (((Cf : ℝ) / 2 ^ 62 - 1) * (1 - ψ ^ 2 / 2) - ((Sf : ℝ) / 2 ^ 62 - 1) * (ψ - ψ ^ 3 / 6))

/-- the same polynomial, coefficientwise (`w = Cf − 2^62` resp. `Sf − 2^62`). -/
theorem termPoly_eq (U V : ℤ) (c Cf Sf : ℕ) (r s t : ℝ) :
    termPoly U V c Cf Sf r s t = (1 / (6 * 2 ^ 62)) *
      ((kap U V c 0 0 : ℝ) * ((Cf : ℝ) - 2 ^ 62) - r * (kap U V c 1 0 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * s
        - r * (kap U V c 0 1 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * t - r ^ 2 * (kap U V c 2 0 : ℝ) * ((Cf : ℝ) - 2 ^ 62) * s ^ 2
        - r ^ 2 * (kap U V c 1 1 : ℝ) * ((Cf : ℝ) - 2 ^ 62) * (s * t) - r ^ 2 * (kap U V c 0 2 : ℝ) * ((Cf : ℝ) - 2 ^ 62) * t ^ 2
        + r ^ 3 * (kap U V c 3 0 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * s ^ 3 + r ^ 3 * (kap U V c 2 1 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * (s ^ 2 * t)
        + r ^ 3 * (kap U V c 1 2 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * (s * t ^ 2) + r ^ 3 * (kap U V c 0 3 : ℝ) * ((Sf : ℝ) - 2 ^ 62) * t ^ 3) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := kap_vals U V c
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  unfold termPoly
  push_cast
  ring

/-! ## List sums -/

theorem sum_map_sub_mul {α : Type} (l : List α) (f g : α → ℝ) (a : ℝ) :
    (l.map (fun x => f x * (g x - a))).sum = (l.map (fun x => f x * g x)).sum - a * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem lsum_sub {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun x => f x - g x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

theorem abs_sum_le_sum {α : Type} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, |f x| ≤ g x) :
    |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (abs_add_le _ _) (add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy]))))

theorem sum_le_len_mul {α : Type} (l : List α) (f : α → ℕ) (b : ℕ) (h : ∀ x ∈ l, f x ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    nlinarith

/-! ## Packing -/

def BB : ℕ := two160

theorem pk5 (a0 a1 a2 a3 a4 : ℕ) : pk [a0, a1, a2, a3, a4] = a0 + BB * (a1 + BB * (a2 + BB * (a3 + BB * a4))) := by
  simp [pk, BB]

theorem pk7 (a0 a1 a2 a3 a4 a5 a6 : ℕ) :
    pk [a0, a1, a2, a3, a4, a5, a6] = a0 + BB * (a1 + BB * (a2 + BB * (a3 + BB * (a4 + BB * (a5 + BB * a6))))) := by
  simp [pk, BB]

theorem shr_eq (A n : ℕ) : Nat.shiftRight A n = A / 2 ^ n := Nat.shiftRight_eq_div_pow A n

theorem BB_eq : BB = 2 ^ 160 := by unfold BB two160; norm_num

theorem fld_eq (A j : ℕ) : fld A j = A / BB ^ j % BB := by
  unfold fld
  rw [shr_eq, BB_eq, ← pow_mul, Nat.mul_eq]
  unfold HW two160; rfl

theorem mod_BB {x y : ℕ} (hx : x < BB) : (x + BB * y) % BB = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem div_BB {x y : ℕ} (hx : x < BB) : (x + BB * y) / BB = y := by
  have hB : 0 < BB := by unfold BB two160; norm_num
  rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx, zero_add]

theorem fld5 {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < BB) (h1 : a1 < BB) (h2 : a2 < BB) (h3 : a3 < BB) :
    let A := a0 + BB * (a1 + BB * (a2 + BB * (a3 + BB * a4)))
    fld A 0 = a0 ∧ fld A 1 = a1 ∧ fld A 2 = a2 ∧ fld A 3 = a3 ∧ Nat.shiftRight A (Nat.mul HW 4) = a4 := by
  intro A
  have e : Nat.shiftRight A (Nat.mul HW 4) = A / BB ^ 4 := by
    rw [shr_eq, BB_eq, ← pow_mul]; rfl
  simp only [fld_eq, e, pow_succ, pow_zero, one_mul, ← Nat.div_div_eq_div_mul, A, div_BB h0, div_BB h1, div_BB h2,
    div_BB h3, Nat.div_one, mod_BB h0, mod_BB h1, mod_BB h2, mod_BB h3, and_self]

theorem fld7 {a0 a1 a2 a3 a4 a5 a6 : ℕ} (h0 : a0 < BB) (h1 : a1 < BB) (h2 : a2 < BB) (h3 : a3 < BB) (h4 : a4 < BB)
    (h5 : a5 < BB) :
    let A := a0 + BB * (a1 + BB * (a2 + BB * (a3 + BB * (a4 + BB * (a5 + BB * a6)))))
    fld A 0 = a0 ∧ fld A 1 = a1 ∧ fld A 2 = a2 ∧ fld A 3 = a3 ∧ fld A 4 = a4 ∧ fld A 5 = a5 ∧
      Nat.shiftRight A (Nat.mul HW 6) = a6 := by
  intro A
  have e : Nat.shiftRight A (Nat.mul HW 6) = A / BB ^ 6 := by
    rw [shr_eq, BB_eq, ← pow_mul]; rfl
  simp only [fld_eq, e, pow_succ, pow_zero, one_mul, ← Nat.div_div_eq_div_mul, A, div_BB h0, div_BB h1, div_BB h2,
    div_BB h3, div_BB h4, div_BB h5, Nat.div_one, mod_BB h0, mod_BB h1, mod_BB h2, mod_BB h3, mod_BB h4, mod_BB h5, and_self]

theorem sum_pk5 {α : Type} (l : List α) (w e0 e1 e2 e3 e4 : α → ℕ) :
    (l.map (fun t => w t * pk [e0 t, e1 t, e2 t, e3 t, e4 t])).sum =
      (l.map (fun t => w t * e0 t)).sum + BB * ((l.map (fun t => w t * e1 t)).sum + BB * ((l.map (fun t => w t * e2 t)).sum +
        BB * ((l.map (fun t => w t * e3 t)).sum + BB * (l.map (fun t => w t * e4 t)).sum))) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, pk5]; ring

theorem sum_pk7 {α : Type} (l : List α) (w e0 e1 e2 e3 e4 e5 e6 : α → ℕ) :
    (l.map (fun t => w t * pk [e0 t, e1 t, e2 t, e3 t, e4 t, e5 t, e6 t])).sum =
      (l.map (fun t => w t * e0 t)).sum + BB * ((l.map (fun t => w t * e1 t)).sum + BB * ((l.map (fun t => w t * e2 t)).sum +
        BB * ((l.map (fun t => w t * e3 t)).sum + BB * ((l.map (fun t => w t * e4 t)).sum +
          BB * ((l.map (fun t => w t * e5 t)).sum + BB * (l.map (fun t => w t * e6 t)).sum))))) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, pk7]; ring


/-! ## Rounding of the coefficients -/

theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem Z2r_mk (p n : ℕ) : (⟨p, n⟩ : Z2).r = (p : ℝ) - n := rfl

theorem floor_div_near (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d - 1 < ((a / d : ℕ) : ℝ) ∧ ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · have h1 := Nat.lt_div_mul_add (a := a) hd
    have h2 : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast h1
    rw [div_sub_one hd'.ne', div_lt_iff₀ hd']; linarith
  · exact Nat.cast_div_le

theorem ceil_div_near (a d : ℕ) (hd : 0 < d) :
    (a : ℝ) / d ≤ (((a + (d - 1)) / d : ℕ) : ℝ) ∧ (((a + (d - 1)) / d : ℕ) : ℝ) < (a : ℝ) / d + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [div_le_iff₀ hd']
    have h1 := Nat.div_add_mod (a + (d - 1)) d
    have h2 := Nat.mod_lt (a + (d - 1)) hd
    have : a ≤ (a + (d - 1)) / d * d := by
      have : d * ((a + (d - 1)) / d) = (a + (d - 1)) / d * d := mul_comm _ _
      omega
    exact_mod_cast this
  · have h3 : (((a + (d - 1)) / d : ℕ) : ℝ) ≤ ((a + (d - 1) : ℕ) : ℝ) / d := Nat.cast_div_le
    have h4 : ((a + (d - 1) : ℕ) : ℝ) = (a : ℝ) + ((d : ℝ) - 1) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega)]; simp
    rw [h4, add_div, sub_div, div_self hd'.ne'] at h3
    have : 0 < 1 / (d : ℝ) := by positivity
    linarith

/-- `coefOf` approximates its target within `2`. -/
theorem coefOf_spec (sg : Bool) (k F sW sp sn rn Dn : ℕ) (hDn : 0 < Dn) :
    |(coefOf sg k F sW sp sn rn Dn).r -
      (bif sg then (1 : ℝ) else -1) * (((F : ℝ) + 2 ^ 62 * sn) - ((OKc : ℝ) * sW + 2 ^ 62 * sp)) * ((rn : ℝ) ^ k * 2 ^ 64) /
        (6 * Dn * 2 ^ 62 * 2 ^ (k * RB))| ≤ 2 := by
  unfold coefOf
  set X := Nat.add F (Nat.mul two62 sn) with hX
  set Y := Nat.add (Nat.mul OKc sW) (Nat.mul two62 sp) with hY
  have hXr : ((F : ℝ) + 2 ^ 62 * sn) = (X : ℝ) := by
    simp only [hX, Nat.add_eq, Nat.mul_eq, two62]; push_cast; ring
  have hYr : ((OKc : ℝ) * sW + 2 ^ 62 * sp) = (Y : ℝ) := by
    simp only [hY, Nat.add_eq, Nat.mul_eq, two62]; push_cast; ring
  rw [hXr, hYr]
  set m := rn ^ k * two64 with hm
  set den := 6 * Dn * two62 * 2 ^ (k * RB) with hden
  have hden0 : 0 < den := by simp only [hden, two62]; positivity
  have hmr : ((rn : ℝ) ^ k * 2 ^ 64) = (m : ℝ) := by simp only [hm, two64]; push_cast; ring
  have hdr : ((6 : ℝ) * Dn * 2 ^ 62 * 2 ^ (k * RB)) = (den : ℝ) := by simp only [hden, two62]; push_cast; ring
  rw [hmr, hdr]
  have key : ∀ A B : ℕ, (A : ℝ) - B = (X : ℝ) - Y ∨ (A : ℝ) - B = -((X : ℝ) - Y) →
      |((⟨Nat.div (Nat.mul A m) den, Nat.div (Nat.add (Nat.mul B m) (den - 1)) den⟩ : Z2)).r -
        ((A : ℝ) - B) * m / den| ≤ 2 := by
    intro A B _
    rw [Z2r_mk]
    have f1 := floor_div_near (A * m) den hden0
    have f2 := ceil_div_near (B * m) den hden0
    simp only [Nat.mul_eq, Nat.add_eq, ndiv] at *
    push_cast at f1 f2 ⊢
    have e : ((A : ℝ) - B) * m / den = (A : ℝ) * m / den - (B : ℝ) * m / den := by ring
    rw [e, abs_le]; constructor <;> linarith [f1.1, f1.2, f2.1, f2.2]
  cases sg with
  | true =>
    have hA : ((Nat.sub X Y : ℕ) : ℝ) - (Nat.sub Y X : ℕ) = (X : ℝ) - Y := by
      rcases le_total Y X with h | h
      · rw [Nat.sub_eq, Nat.sub_eq, Nat.cast_sub h, Nat.sub_eq_zero_of_le h]; simp
      · rw [Nat.sub_eq, Nat.sub_eq, Nat.cast_sub h, Nat.sub_eq_zero_of_le h]; simp
    have := key (Nat.sub X Y) (Nat.sub Y X) (Or.inl hA)
    simp only [Bool.cond_true, one_mul]
    rw [hA] at this
    convert this using 2
  | false =>
    have hA : ((Nat.sub Y X : ℕ) : ℝ) - (Nat.sub X Y : ℕ) = -((X : ℝ) - Y) := by
      rcases le_total Y X with h | h
      · rw [Nat.sub_eq, Nat.sub_eq, Nat.cast_sub h, Nat.sub_eq_zero_of_le h]; simp
      · rw [Nat.sub_eq, Nat.sub_eq, Nat.cast_sub h, Nat.sub_eq_zero_of_le h]; simp
    have := key (Nat.sub Y X) (Nat.sub X Y) (Or.inr hA)
    simp only [Bool.cond_false]
    rw [hA] at this
    convert this using 2
    ring


/-! ## The table hypothesis and phases -/

/-- table quality: field `n` approximates `(cos, sin)(2πn/M) + 1` within `4/2^62`. -/
def TabGood (M tab : ℕ) : Prop := ∀ n < M,
  |((lookE tab M n).1 : ℝ) / 2 ^ 62 - 1 - Real.cos (2 * π * n / M)| ≤ 4 / 2 ^ 62 ∧
  |((lookE tab M n).2 : ℝ) / 2 ^ 62 - 1 - Real.sin (2 * π * n / M)| ≤ 4 / 2 ^ 62

/-- the table index of a term. -/
def idxT (O M J K : ℕ) (t : ℤ × ℤ × ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.mul (t.1 + O).toNat J) (Nat.mul (t.2.1 + O).toNat K)) M

def CfT (tab O M J K : ℕ) (t : ℤ × ℤ × ℕ) : ℕ := (lookE tab M (idxT O M J K t)).1
def SfT (tab O M J K : ℕ) (t : ℤ × ℤ × ℕ) : ℕ := (lookE tab M (idxT O M J K t)).2

theorem phase_eq (U V : ℤ) (O J K M : ℕ) (hM : 0 < M) (hM2 : 2 ∣ M) (hO : M ∣ O) (hU : 0 ≤ U + O) (hV : 0 ≤ V + O) :
    Real.cos (2 * π * (idxT O M J K (U, V, 0) : ℕ) / M) = Real.cos (π * (U * ((J : ℝ) / (M / 2 : ℕ)) + V * ((K : ℝ) / (M / 2 : ℕ)))) ∧
    Real.sin (2 * π * (idxT O M J K (U, V, 0) : ℕ) / M) = Real.sin (π * (U * ((J : ℝ) / (M / 2 : ℕ)) + V * ((K : ℝ) / (M / 2 : ℕ)))) := by
  obtain ⟨h, rfl⟩ := hM2
  obtain ⟨o, rfl⟩ := hO
  have hh : 0 < h := by omega
  have e2 : (2 * h / 2 : ℕ) = h := by omega
  rw [e2]
  set a : ℕ := (U + ↑(2 * h * o)).toNat * J + (V + ↑(2 * h * o)).toNat * K with ha
  have hidx : idxT (2 * h * o) (2 * h) J K (U, V, 0) = a % (2 * h) := rfl
  rw [hidx]
  have haz : (a : ℤ) = U * J + V * K + (2 * h) * (o * (J + K)) := by
    rw [ha]; push_cast
    have hU' : 0 ≤ U + 2 * (h : ℤ) * o := by exact_mod_cast hU
    have hV' : 0 ≤ V + 2 * (h : ℤ) * o := by exact_mod_cast hV
    rw [Int.toNat_of_nonneg hU', Int.toNat_of_nonneg hV']; ring
  have hdm := Nat.div_add_mod a (2 * h)
  set q := a / (2 * h)
  have key : 2 * π * ((a % (2 * h) : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) =
      π * (U * ((J : ℝ) / h) + V * ((K : ℝ) / h)) + ((o * (J + K) - q : ℤ) : ℝ) * (2 * π) := by
    have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    have e1 : ((a % (2 * h) : ℕ) : ℝ) = (a : ℝ) - 2 * h * q := by
      have : (a % (2 * h) : ℕ) = a - 2 * h * q := by omega
      rw [this, Nat.cast_sub (by omega)]; push_cast; ring
    have e3 : (a : ℝ) = U * J + V * K + (2 * h) * (o * (J + K)) := by exact_mod_cast haz
    rw [e1, e3]; push_cast; field_simp; ring
  rw [key, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

/-! ## Accumulation -/

theorem accum_cons (tab M J K : ℕ) (p : PTerm) (ps : List PTerm) :
    accum tab M J K (p :: ps) =
      (Nat.add (accum tab M J K ps).1 (Nat.mul (lookE tab M (Nat.mod (Nat.add (Nat.mul p.Uo J) (Nat.mul p.Vo K)) M)).1 p.KE),
       Nat.add (accum tab M J K ps).2 (Nat.mul (lookE tab M (Nat.mod (Nat.add (Nat.mul p.Uo J) (Nat.mul p.Vo K)) M)).2 p.KO)) := rfl

theorem accum_map (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) :
    accum tab M J K (ts.map (prepT O)) =
      ((ts.map (fun t => CfT tab O M J K t * packE t.1 t.2.1 t.2.2)).sum,
       (ts.map (fun t => SfT tab O M J K t * packO t.1 t.2.1 t.2.2)).sum) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.map_cons, accum_cons, ih]
    simp only [List.map_cons, List.sum_cons, Nat.add_eq, Nat.mul_eq]
    unfold CfT SfT idxT prepT
    simp only [Nat.add_eq, Nat.mul_eq]
    ext <;> simp [add_comm]


/-! ## Validity -/

theorem termOK_spec {O : ℕ} {t : ℤ × ℤ × ℕ} (h : termOK O t = true) :
    0 ≤ t.1 + O ∧ 0 ≤ t.2.1 + O ∧
    ∀ ab ∈ List.zip monA monB, (kap t.1 t.2.1 t.2.2 ab.1 ab.2).natAbs < OKc := by
  unfold termOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem kap_lt {O : ℕ} {t : ℤ × ℤ × ℕ} (h : termOK O t = true) (a b : ℕ) (hab : (a, b) ∈ List.zip monA monB) :
    0 ≤ kap t.1 t.2.1 t.2.2 a b + OKc ∧ (kap t.1 t.2.1 t.2.2 a b + OKc).toNat ≤ 2 * OKc := by
  have := (termOK_spec h).2.2 _ hab
  simp only at this
  have h1 : |kap t.1 t.2.1 t.2.2 a b| < OKc := by rw [Int.abs_eq_natAbs]; exact_mod_cast this
  rw [abs_lt] at h1
  constructor
  · linarith
  · have : (kap t.1 t.2.1 t.2.2 a b + OKc).toNat ≤ (2 * OKc : ℤ).toNat := Int.toNat_le_toNat (by linarith)
    simpa using this

theorem valid_spec {O : ℕ} {ts : List (ℤ × ℤ × ℕ)} {Dn : ℕ} (hv : (prepS O ts Dn).valid = true) :
    0 < Dn ∧ ts.length < 16384 ∧ ∀ t ∈ ts, termOK O t = true := by
  unfold prepS at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

theorem field_lt {α : Type} (l : List α) (w e : α → ℕ) (hl : l.length < 16384) (hw : ∀ x ∈ l, w x < two64)
    (he : ∀ x ∈ l, e x ≤ 2 * OKc) : (l.map (fun x => w x * e x)).sum < BB := by
  have h1 : (l.map (fun x => w x * e x)).sum ≤ l.length * (two64 * (2 * OKc)) :=
    sum_le_len_mul l _ _ (fun x hx => Nat.mul_le_mul (hw x hx).le (he x hx))
  have h2 : l.length * (two64 * (2 * OKc)) < BB := by
    have : l.length * (two64 * (2 * OKc)) ≤ 16383 * (two64 * (2 * OKc)) := Nat.mul_le_mul_right _ (by omega)
    refine lt_of_le_of_lt this ?_
    unfold two64 OKc BB two160; norm_num
  omega

theorem getT_lt (tab n : ℕ) : getT tab n < two128 := by
  unfold getT; exact Nat.mod_lt _ (by unfold two128; norm_num)

theorem lookE_lt (tab M n : ℕ) : (lookE tab M n).1 < two64 ∧ (lookE tab M n).2 < two64 := by
  unfold lookE
  have hw := getT_lt tab n
  constructor
  · exact Nat.mod_lt _ (by unfold two64; norm_num)
  · show Nat.shiftRight (getT tab n) 64 < two64
    rw [shr_eq]; apply Nat.div_lt_of_lt_mul; unfold two128 at hw; unfold two64; norm_num at hw ⊢; omega

theorem CfT_lt (tab O M J K : ℕ) (t : ℤ × ℤ × ℕ) : CfT tab O M J K t < two64 := (lookE_lt _ _ _).1

theorem SfT_lt (tab O M J K : ℕ) (t : ℤ × ℤ × ℕ) : SfT tab O M J K t < two64 := (lookE_lt _ _ _).2

/-- the field sums. -/
noncomputable def FS (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (odd : Bool) (a b : ℕ) : ℕ :=
  (ts.map (fun t => (bif odd then SfT tab O M J K t else CfT tab O M J K t) * (kap t.1 t.2.1 t.2.2 a b + OKc).toNat)).sum

theorem tm_fields (O tab M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (hl : ts.length < 16384) (hok : ∀ t ∈ ts, termOK O t = true) :
    let AE := (accum tab M J K (ts.map (prepT O))).1
    let AO := (accum tab M J K (ts.map (prepT O))).2
    fld AE 0 = FS tab O M J K ts false 0 0 ∧ fld AE 1 = FS tab O M J K ts false 2 0 ∧ fld AE 2 = FS tab O M J K ts false 1 1 ∧
    fld AE 3 = FS tab O M J K ts false 0 2 ∧ Nat.shiftRight AE (Nat.mul HW 4) = (ts.map (fun t => CfT tab O M J K t * 1)).sum ∧
    fld AO 0 = FS tab O M J K ts true 1 0 ∧ fld AO 1 = FS tab O M J K ts true 0 1 ∧ fld AO 2 = FS tab O M J K ts true 3 0 ∧
    fld AO 3 = FS tab O M J K ts true 2 1 ∧ fld AO 4 = FS tab O M J K ts true 1 2 ∧ fld AO 5 = FS tab O M J K ts true 0 3 ∧
    Nat.shiftRight AO (Nat.mul HW 6) = (ts.map (fun t => SfT tab O M J K t * 1)).sum := by
  intro AE AO
  have hAE : AE = (ts.map (fun t => CfT tab O M J K t * packE t.1 t.2.1 t.2.2)).sum := by
    simp only [AE, accum_map]
  have hAO : AO = (ts.map (fun t => SfT tab O M J K t * packO t.1 t.2.1 t.2.2)).sum := by
    simp only [AO, accum_map]
  unfold packE at hAE
  unfold packO at hAO
  rw [sum_pk5] at hAE
  rw [sum_pk7] at hAO
  have hb : ∀ (odd : Bool) (a b : ℕ), (a, b) ∈ List.zip monA monB → FS tab O M J K ts odd a b < BB := by
    intro odd a b hab
    apply field_lt _ _ _ hl
    · intro t _; cases odd
      · exact CfT_lt _ _ _ _ _ _
      · exact SfT_lt _ _ _ _ _ _
    · intro t ht; exact (kap_lt (hok t ht) a b hab).2
  have m : ∀ a b : ℕ, (a, b) ∈ List.zip monA monB ↔ (a, b) ∈ List.zip monA monB := fun _ _ => Iff.rfl
  have z00 : ((0 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z10 : ((1 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z01 : ((0 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z20 : ((2 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z11 : ((1 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z02 : ((0 : ℕ), (2 : ℕ)) ∈ List.zip monA monB := by decide
  have z30 : ((3 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z21 : ((2 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z12 : ((1 : ℕ), (2 : ℕ)) ∈ List.zip monA monB := by decide
  have z03 : ((0 : ℕ), (3 : ℕ)) ∈ List.zip monA monB := by decide
  have e := fld5 (a4 := (ts.map (fun t => CfT tab O M J K t * 1)).sum) (hb false 0 0 z00) (hb false 2 0 z20) (hb false 1 1 z11)
    (hb false 0 2 z02)
  have o := fld7 (a6 := (ts.map (fun t => SfT tab O M J K t * 1)).sum) (hb true 1 0 z10) (hb true 0 1 z01) (hb true 3 0 z30)
    (hb true 2 1 z21) (hb true 1 2 z12) (hb true 0 3 z03)
  simp only [FS, Bool.cond_false, Bool.cond_true] at e o
  rw [hAE, hAO]
  simp only [FS, Bool.cond_false, Bool.cond_true]
  exact ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2, o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2.1, o.2.2.2.2.2.2⟩


theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/-- the weighted `κ` sums `Σ κ_ab (W − 2^62)`. -/
noncomputable def WS (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (odd : Bool) (a b : ℕ) : ℝ :=
  (ts.map (fun t => (kap t.1 t.2.1 t.2.2 a b : ℝ) * (((bif odd then SfT tab O M J K t else CfT tab O M J K t : ℕ) : ℝ) - 2 ^ 62))).sum

theorem sum_termPoly (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (r s u : ℝ) :
    (ts.map (fun t => termPoly t.1 t.2.1 t.2.2 (CfT tab O M J K t) (SfT tab O M J K t) r s u)).sum =
      (1 / (6 * 2 ^ 62)) * (WS tab O M J K ts false 0 0 - r * WS tab O M J K ts true 1 0 * s - r * WS tab O M J K ts true 0 1 * u
        - r ^ 2 * WS tab O M J K ts false 2 0 * s ^ 2 - r ^ 2 * WS tab O M J K ts false 1 1 * (s * u)
        - r ^ 2 * WS tab O M J K ts false 0 2 * u ^ 2 + r ^ 3 * WS tab O M J K ts true 3 0 * s ^ 3
        + r ^ 3 * WS tab O M J K ts true 2 1 * (s ^ 2 * u) + r ^ 3 * WS tab O M J K ts true 1 2 * (s * u ^ 2)
        + r ^ 3 * WS tab O M J K ts true 0 3 * u ^ 3) := by
  induction ts with
  | nil => simp [WS]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, WS, Bool.cond_true, Bool.cond_false] at ih ⊢
    rw [ih, termPoly_eq]
    ring

theorem WS_eq (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (odd : Bool) (a b : ℕ)
    (h : ∀ t ∈ ts, 0 ≤ kap t.1 t.2.1 t.2.2 a b + OKc) :
    WS tab O M J K ts odd a b = (FS tab O M J K ts odd a b : ℝ) -
      (OKc : ℝ) * ((ts.map (fun t => (bif odd then SfT tab O M J K t else CfT tab O M J K t) * 1)).sum : ℕ) -
        2 ^ 62 * (skap ts a b : ℝ) := by
  induction ts with
  | nil => simp [WS, FS, skap]
  | cons t ts ih =>
    have h1 := h t (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp only [WS, FS, skap, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Int.cast_add, cast_toNat _ h1, Int.cast_natCast]
    ring


/-! ## The error of the polynomial part -/

theorem sum_err (tab O M J K : ℕ) (ts : List (ℤ × ℤ × ℕ)) (hM : 0 < M) (hM2 : 2 ∣ M) (hO : M ∣ O) (htab : TabGood M tab)
    (hok : ∀ t ∈ ts, termOK O t = true) (r s u : ℝ) (hr : 0 ≤ r) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |(ts.map (fun t => (t.2.2 : ℝ) * Real.cos (π * (t.1 * ((J : ℝ) / (M / 2 : ℕ) + r * s / π) + t.2.1 * ((K : ℝ) / (M / 2 : ℕ) + r * u / π))))).sum -
      (ts.map (fun t => termPoly t.1 t.2.1 t.2.2 (CfT tab O M J K t) (SfT tab O M J K t) r s u)).sum| ≤
      (8 / 2 ^ 62) * ((ts.map (fun t => t.2.2)).sum : ℕ) +
        (1 + 8 / 2 ^ 62) * r ^ 4 / 24 * ((ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum : ℕ) := by
  rw [lsum_sub]
  have hb := abs_sum_le_sum ts (fun t => (t.2.2 : ℝ) * Real.cos (π * (t.1 * ((J : ℝ) / (M / 2 : ℕ) + r * s / π) + t.2.1 * ((K : ℝ) / (M / 2 : ℕ) + r * u / π))) -
      termPoly t.1 t.2.1 t.2.2 (CfT tab O M J K t) (SfT tab O M J K t) r s u)
    (fun t => (t.2.2 : ℝ) * (8 / 2 ^ 62 + (1 + 8 / 2 ^ 62) * r ^ 4 / 24 * ((t.1.natAbs + t.2.1.natAbs) ^ 4 : ℕ)))
    (by
      intro t ht
      obtain ⟨hU, hV, _⟩ := termOK_spec (hok t ht)
      have hidx : idxT O M J K t = idxT O M J K (t.1, t.2.1, 0) := rfl
      have hn : idxT O M J K t < M := by unfold idxT; exact Nat.mod_lt _ hM
      obtain ⟨hc, hs'⟩ := htab _ hn
      obtain ⟨pc, ps⟩ := phase_eq t.1 t.2.1 O J K M hM hM2 hO hU hV
      rw [← hidx] at pc ps
      rw [pc] at hc; rw [ps] at hs'
      set φ := π * (t.1 * ((J : ℝ) / (M / 2 : ℕ)) + t.2.1 * ((K : ℝ) / (M / 2 : ℕ)))
      set ψ := r * (t.1 * s + t.2.1 * u)
      have harg : π * (t.1 * ((J : ℝ) / (M / 2 : ℕ) + r * s / π) + t.2.1 * ((K : ℝ) / (M / 2 : ℕ) + r * u / π)) = φ + ψ := by
        simp only [φ, ψ]; field_simp; ring
      have hc2 : |(((CfT tab O M J K t : ℕ) : ℝ) / 2 ^ 62 - 1) - Real.cos φ| ≤ 4 / 2 ^ 62 := hc
      have hs2 : |(((SfT tab O M J K t : ℕ) : ℝ) / 2 ^ 62 - 1) - Real.sin φ| ≤ 4 / 2 ^ 62 := hs'
      have tb := term_bound φ ψ _ _ _ hc2 hs2
      have hψ : |ψ| ≤ r * ((t.1.natAbs + t.2.1.natAbs : ℕ) : ℝ) := by
        simp only [ψ, abs_mul, abs_of_nonneg hr]
        apply mul_le_mul_of_nonneg_left _ hr
        push_cast
        rw [Nat.cast_natAbs, Nat.cast_natAbs]
        calc |(t.1 : ℝ) * s + t.2.1 * u| ≤ |(t.1 : ℝ) * s| + |(t.2.1 : ℝ) * u| := abs_add_le _ _
          _ ≤ |(t.1 : ℝ)| * 1 + |(t.2.1 : ℝ)| * 1 := by
              rw [abs_mul, abs_mul]; gcongr
          _ = _ := by simp
      have hψ4 : ψ ^ 4 ≤ r ^ 4 * (((t.1.natAbs + t.2.1.natAbs) ^ 4 : ℕ) : ℝ) := by
        have : ψ ^ 4 = |ψ| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
        rw [this]
        calc |ψ| ^ 4 ≤ (r * ((t.1.natAbs + t.2.1.natAbs : ℕ) : ℝ)) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hψ 4
          _ = _ := by push_cast; ring
      have hcn : (0 : ℝ) ≤ t.2.2 := Nat.cast_nonneg _
      have e : (t.2.2 : ℝ) * Real.cos (π * (t.1 * ((J : ℝ) / (M / 2 : ℕ) + r * s / π) + t.2.1 * ((K : ℝ) / (M / 2 : ℕ) + r * u / π))) -
          termPoly t.1 t.2.1 t.2.2 (CfT tab O M J K t) (SfT tab O M J K t) r s u =
          (t.2.2 : ℝ) * (Real.cos (φ + ψ) - ((((CfT tab O M J K t : ℕ) : ℝ) / 2 ^ 62 - 1) * (1 - ψ ^ 2 / 2) -
            (((SfT tab O M J K t : ℕ) : ℝ) / 2 ^ 62 - 1) * (ψ - ψ ^ 3 / 6))) := by
        rw [harg]; simp only [termPoly, ψ]; ring
      rw [e, abs_mul, abs_of_nonneg hcn]
      apply mul_le_mul_of_nonneg_left _ hcn
      refine le_trans tb ?_
      have : (0 : ℝ) ≤ 1 + 2 * (4 / 2 ^ 62) := by positivity
      calc 2 * (4 / 2 ^ 62) + (1 + 2 * (4 / 2 ^ 62)) * (ψ ^ 4 / 24) ≤
            2 * (4 / 2 ^ 62) + (1 + 2 * (4 / 2 ^ 62)) * (r ^ 4 * (((t.1.natAbs + t.2.1.natAbs) ^ 4 : ℕ) : ℝ) / 24) := by
            gcongr
        _ = _ := by ring)
  refine le_trans hb (le_of_eq ?_)
  clear hb
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul] at ih ⊢
    rw [ih (fun x hx => hok x (by simp [hx]))]
    ring


/-! ## Taylor model of a prepared sum -/

theorem sk_split (z : ℤ) : ((z.toNat : ℕ) : ℝ) - (((-z).toNat : ℕ) : ℝ) = (z : ℝ) := by
  rcases le_total 0 z with h | h
  · rw [cast_toNat z h, Int.toNat_of_nonpos (by linarith)]; simp
  · rw [Int.toNat_of_nonpos h, cast_toNat (-z) (by linarith)]; push_cast; ring

theorem coef_bound (sg : Bool) (k F sW sp sn rn Dn : ℕ) (hDn : 0 < Dn) (W : ℝ)
    (hW : ((F : ℝ) + 2 ^ 62 * sn) - ((OKc : ℝ) * sW + 2 ^ 62 * sp) = W) :
    |(coefOf sg k F sW sp sn rn Dn).r - (bif sg then (1 : ℝ) else -1) * W * ((rn : ℝ) ^ k * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (k * RB))| ≤ 2 := by
  rw [← hW]; exact coefOf_spec sg k F sW sp sn rn Dn hDn

theorem mon_bound (s u : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1) (a b : ℕ) : |s ^ a * u ^ b| ≤ 1 := by
  rw [abs_mul, abs_pow, abs_pow]
  have h1 := pow_le_one₀ (abs_nonneg s) hs (n := a)
  have h2 := pow_le_one₀ (abs_nonneg u) hu (n := b)
  have h3 : 0 ≤ |u| ^ b := by positivity
  nlinarith

theorem tmS_eq (O : ℕ) (ts : List (ℤ × ℤ × ℕ)) (Dn tab M J K : ℕ) (hl : ts.length < 16384) (hok : ∀ t ∈ ts, termOK O t = true) :
    let rn := Rn (M / 2)
    let sC := (ts.map (fun t => CfT tab O M J K t * 1)).sum
    let sS := (ts.map (fun t => SfT tab O M J K t * 1)).sum
    tmS (prepS O ts Dn) tab M J K =
      ⟨⟨coefOf true 0 (FS tab O M J K ts false 0 0) sC (skap ts 0 0).toNat (-(skap ts 0 0)).toNat rn Dn,
        coefOf false 1 (FS tab O M J K ts true 1 0) sS (skap ts 1 0).toNat (-(skap ts 1 0)).toNat rn Dn,
        coefOf false 1 (FS tab O M J K ts true 0 1) sS (skap ts 0 1).toNat (-(skap ts 0 1)).toNat rn Dn,
        coefOf false 2 (FS tab O M J K ts false 2 0) sC (skap ts 2 0).toNat (-(skap ts 2 0)).toNat rn Dn,
        coefOf false 2 (FS tab O M J K ts false 1 1) sC (skap ts 1 1).toNat (-(skap ts 1 1)).toNat rn Dn,
        coefOf false 2 (FS tab O M J K ts false 0 2) sC (skap ts 0 2).toNat (-(skap ts 0 2)).toNat rn Dn,
        coefOf true 3 (FS tab O M J K ts true 3 0) sS (skap ts 3 0).toNat (-(skap ts 3 0)).toNat rn Dn,
        coefOf true 3 (FS tab O M J K ts true 2 1) sS (skap ts 2 1).toNat (-(skap ts 2 1)).toNat rn Dn,
        coefOf true 3 (FS tab O M J K ts true 1 2) sS (skap ts 1 2).toNat (-(skap ts 1 2)).toNat rn Dn,
        coefOf true 3 (FS tab O M J K ts true 0 3) sS (skap ts 0 3).toNat (-(skap ts 0 3)).toNat rn Dn⟩,
        remOf (prepS O ts Dn) rn⟩ := by
  intro rn sC sS
  obtain ⟨e0, e1, e2, e3, e4, o0, o1, o2, o3, o4, o5, o6⟩ := tm_fields O tab M J K ts hl hok
  have hT : (prepS O ts Dn).terms = ts.map (prepT O) := rfl
  simp only [tmS, hT, e0, e1, e2, e3, e4, o0, o1, o2, o3, o4, o5, o6]
  rfl

set_option exponentiation.threshold 2000 in
/-- **Taylor model of a prepared sum.** -/
theorem tmS_sound (O : ℕ) (ts : List (ℤ × ℤ × ℕ)) (Dn tab M J K : ℕ) (hv : (prepS O ts Dn).valid = true)
    (hM : 0 < M) (hM2 : 2 ∣ M) (hO : M ∣ O) (htab : TabGood M tab) :
    TMok (fun s u => sumVal ts Dn ((J : ℝ) / (M / 2 : ℕ) + (Rn (M / 2) : ℝ) / 2 ^ 80 * s / π)
        ((K : ℝ) / (M / 2 : ℕ) + (Rn (M / 2) : ℝ) / 2 ^ 80 * u / π)) (tmS (prepS O ts Dn) tab M J K) := by
  obtain ⟨hDn, hl, hok⟩ := valid_spec hv
  intro s u hs hu
  rw [tmS_eq O ts Dn tab M J K hl hok]
  simp only []
  set rn := Rn (M / 2) with hrn
  set r : ℝ := (rn : ℝ) / 2 ^ 80 with hr
  have hr0 : 0 ≤ r := by positivity
  have E := sum_err tab O M J K ts hM hM2 hO htab hok r s u hr0 hs hu
  have I := sum_termPoly tab O M J K ts r s u
  have hk : ∀ a b, (a, b) ∈ List.zip monA monB → ∀ t ∈ ts, 0 ≤ kap t.1 t.2.1 t.2.2 a b + OKc :=
    fun a b hab t ht => (kap_lt (hok t ht) a b hab).1
  -- the ten coefficients
  have hWb : ∀ (odd : Bool) (a b : ℕ), (a, b) ∈ List.zip monA monB →
      ((FS tab O M J K ts odd a b : ℕ) : ℝ) + 2 ^ 62 * (((-(skap ts a b)).toNat : ℕ) : ℝ) -
        ((OKc : ℝ) * (((ts.map (fun t => (bif odd then SfT tab O M J K t else CfT tab O M J K t) * 1)).sum : ℕ) : ℝ) +
          2 ^ 62 * (((skap ts a b).toNat : ℕ) : ℝ)) = WS tab O M J K ts odd a b := by
    intro odd a b hab
    rw [WS_eq tab O M J K ts odd a b (hk a b hab), ← sk_split (skap ts a b)]
    ring
  have z00 : ((0 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z10 : ((1 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z01 : ((0 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z20 : ((2 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z11 : ((1 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z02 : ((0 : ℕ), (2 : ℕ)) ∈ List.zip monA monB := by decide
  have z30 : ((3 : ℕ), (0 : ℕ)) ∈ List.zip monA monB := by decide
  have z21 : ((2 : ℕ), (1 : ℕ)) ∈ List.zip monA monB := by decide
  have z12 : ((1 : ℕ), (2 : ℕ)) ∈ List.zip monA monB := by decide
  have z03 : ((0 : ℕ), (3 : ℕ)) ∈ List.zip monA monB := by decide
  have b0 := coef_bound true 0 _ _ _ _ rn Dn hDn _ (hWb false 0 0 z00)
  have b1 := coef_bound false 1 _ _ _ _ rn Dn hDn _ (hWb true 1 0 z10)
  have b2 := coef_bound false 1 _ _ _ _ rn Dn hDn _ (hWb true 0 1 z01)
  have b3 := coef_bound false 2 _ _ _ _ rn Dn hDn _ (hWb false 2 0 z20)
  have b4 := coef_bound false 2 _ _ _ _ rn Dn hDn _ (hWb false 1 1 z11)
  have b5 := coef_bound false 2 _ _ _ _ rn Dn hDn _ (hWb false 0 2 z02)
  have b6 := coef_bound true 3 _ _ _ _ rn Dn hDn _ (hWb true 3 0 z30)
  have b7 := coef_bound true 3 _ _ _ _ rn Dn hDn _ (hWb true 2 1 z21)
  have b8 := coef_bound true 3 _ _ _ _ rn Dn hDn _ (hWb true 1 2 z12)
  have b9 := coef_bound true 3 _ _ _ _ rn Dn hDn _ (hWb true 0 3 z03)
  simp only [Bool.cond_true, Bool.cond_false] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  -- names for the targets
  obtain ⟨P, hP⟩ : ∃ P, P = (ts.map (fun t => termPoly t.1 t.2.1 t.2.2 (CfT tab O M J K t) (SfT tab O M J K t) r s u)).sum :=
    ⟨_, rfl⟩
  obtain ⟨Sc, hSc⟩ : ∃ Sc, Sc = (ts.map (fun t => (t.2.2 : ℝ) * Real.cos (π * (t.1 * ((J : ℝ) / (M / 2 : ℕ) + r * s / π) +
    t.2.1 * ((K : ℝ) / (M / 2 : ℕ) + r * u / π))))).sum := ⟨_, rfl⟩
  rw [← hP] at I E
  rw [← hSc] at E
  have hDr : (0 : ℝ) < Dn := by exact_mod_cast hDn
  have hsum : sumVal ts Dn ((J : ℝ) / (M / 2 : ℕ) + r * s / π) ((K : ℝ) / (M / 2 : ℕ) + r * u / π) = Sc / Dn := by
    rw [hSc]; rfl
  rw [hsum]
  -- the polynomial part equals the sum of the targets
  have hPev : P / Dn = (1 * WS tab O M J K ts false 0 0 * ((rn : ℝ) ^ 0 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (0 * RB))
      + -1 * WS tab O M J K ts true 1 0 * ((rn : ℝ) ^ 1 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (1 * RB)) * s
      + -1 * WS tab O M J K ts true 0 1 * ((rn : ℝ) ^ 1 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (1 * RB)) * u
      + -1 * WS tab O M J K ts false 2 0 * ((rn : ℝ) ^ 2 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (2 * RB)) * s ^ 2
      + -1 * WS tab O M J K ts false 1 1 * ((rn : ℝ) ^ 2 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (2 * RB)) * (s * u)
      + -1 * WS tab O M J K ts false 0 2 * ((rn : ℝ) ^ 2 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (2 * RB)) * u ^ 2
      + 1 * WS tab O M J K ts true 3 0 * ((rn : ℝ) ^ 3 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (3 * RB)) * s ^ 3
      + 1 * WS tab O M J K ts true 2 1 * ((rn : ℝ) ^ 3 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (3 * RB)) * (s ^ 2 * u)
      + 1 * WS tab O M J K ts true 1 2 * ((rn : ℝ) ^ 3 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (3 * RB)) * (s * u ^ 2)
      + 1 * WS tab O M J K ts true 0 3 * ((rn : ℝ) ^ 3 * 2 ^ 64) / (6 * Dn * 2 ^ 62 * 2 ^ (3 * RB)) * u ^ 3) / 2 ^ 64 := by
    rw [I, hr]
    unfold RB
    field_simp
    ring
  -- assemble
  have hm := mon_bound s u hs hu
  have hm10 := hm 1 0; have hm01 := hm 0 1; have hm20 := hm 2 0; have hm11 := hm 1 1; have hm02 := hm 0 2
  have hm30 := hm 3 0; have hm21 := hm 2 1; have hm12 := hm 1 2; have hm03 := hm 0 3
  simp only [pow_one, pow_zero, one_mul, mul_one] at hm10 hm01 hm20 hm11 hm02 hm30 hm21 hm12 hm03
  -- the remainder
  have hrem : ((8 / 2 ^ 62) * ((ts.map (fun t => t.2.2)).sum : ℕ) +
      (1 + 8 / 2 ^ 62) * r ^ 4 / 24 * ((ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum : ℕ)) / Dn + 20 / 2 ^ 64 ≤
      (remOf (prepS O ts Dn) rn : ℝ) / 2 ^ 64 := by
    unfold remOf
    simp only []
    have hG0 : (prepS O ts Dn).G0 = (ts.map (fun t => t.2.2)).sum := rfl
    have hG4 : (prepS O ts Dn).G4 = (ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum := rfl
    have hDD : (prepS O ts Dn).Dn = Dn := rfl
    rw [hG0, hG4, hDD]
    set G0 := (ts.map (fun t => t.2.2)).sum
    set G4 := (ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum
    have hden : 0 < 24 * 2 ^ (4 * RB) * two62 * Dn := by unfold two62; positivity
    have hc := (ceil_div_near (two64 * G4 * rn ^ 4 * (two62 + 8) + 8 * G0 * two64 * 24 * 2 ^ (4 * RB))
      (24 * 2 ^ (4 * RB) * two62 * Dn) hden).1
    push_cast
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 64)]
    have e : (((8 / 2 ^ 62) * (G0 : ℝ) + (1 + 8 / 2 ^ 62) * r ^ 4 / 24 * (G4 : ℝ)) / Dn + 20 / 2 ^ 64) * 2 ^ 64 =
        ((two64 * G4 * rn ^ 4 * (two62 + 8) + 8 * G0 * two64 * 24 * 2 ^ (4 * RB) : ℕ) : ℝ) /
          ((24 * 2 ^ (4 * RB) * two62 * Dn : ℕ) : ℝ) + 20 := by
      rw [hr]; unfold two64 two62 RB; push_cast; field_simp; ring
    rw [e]
    linarith
  have hfin : |Sc / Dn - P / Dn| ≤ ((8 / 2 ^ 62) * ((ts.map (fun t => t.2.2)).sum : ℕ) +
      (1 + 8 / 2 ^ 62) * r ^ 4 / 24 * ((ts.map (fun t => t.2.2 * (t.1.natAbs + t.2.1.natAbs) ^ 4)).sum : ℕ)) / Dn := by
    rw [← sub_div, abs_div, abs_of_pos hDr]
    exact div_le_div_of_nonneg_right E hDr.le
  refine le_trans (abs_sub_le _ (P / Dn) _) ?_
  refine le_trans (add_le_add hfin ?_) hrem
  rw [hPev, Poly.ev]
  simp only []
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have t1 : ∀ (a c m : ℝ), |c - a| ≤ 2 → |m| ≤ 1 → |a * m - c * m| ≤ 2 := by
    intro a c m h1 h2
    rw [abs_sub_comm] at h1
    rw [← sub_mul, abs_mul]
    calc |a - c| * |m| ≤ 2 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have h1 := abs_le.1 (t1 _ _ s b1 hm10)
  have h2 := abs_le.1 (t1 _ _ u b2 hm01)
  have h3 := abs_le.1 (t1 _ _ (s ^ 2) b3 hm20)
  have h4 := abs_le.1 (t1 _ _ (s * u) b4 hm11)
  have h5 := abs_le.1 (t1 _ _ (u ^ 2) b5 hm02)
  have h6 := abs_le.1 (t1 _ _ (s ^ 3) b6 hm30)
  have h7 := abs_le.1 (t1 _ _ (s ^ 2 * u) b7 hm21)
  have h8 := abs_le.1 (t1 _ _ (s * u ^ 2) b8 hm12)
  have h9 := abs_le.1 (t1 _ _ (u ^ 3) b9 hm03)
  rw [abs_sub_comm] at b0
  have h0 := abs_le.1 b0
  rw [abs_le]
  constructor
  · linarith [h0.1, h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1, h9.1]
  · linarith [h0.2, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2]

end Palprimes.M2
