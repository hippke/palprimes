import Palprimes.Major2D.Cell
import Palprimes.Major2D.Comp

/-! # Symmetry reduction: from the listed level-0 cells to the whole plane

Invariances of `Good` (all checked on the term lists by `decide`):
* translations by `(a/m, c/m)` for `(a, c)` in a shift list (the lattice `Λ` and `(m, 0)`, `(0, m)`);
* `(x, y) ↦ (−x, −y)`;
* `(x, y) ↦ (y, x)`.
A covering check (bitmap) shows that every level-0 cell is mapped into the list `L` by one group element. -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real

namespace Palprimes.M2

/-! ## Negation -/

theorem sumC_cons (t : ℤ × ℤ × ℕ) (ts : List (ℤ × ℤ × ℕ)) (x y : ℝ) :
    sumC (t :: ts) x y = (t.2.2 : ℝ) * Real.cos (π * (t.1 * x + t.2.1 * y)) + sumC ts x y := by
  unfold sumC; rw [List.map_cons, List.sum_cons]

theorem sumC_nil (x y : ℝ) : sumC [] x y = 0 := by unfold sumC; simp

theorem sumC_neg (ts : List (ℤ × ℤ × ℕ)) (x y : ℝ) : sumC ts (-x) (-y) = sumC ts x y := by
  induction ts with
  | nil => rw [sumC_nil, sumC_nil]
  | cons t ts ih =>
    rw [sumC_cons, sumC_cons, ih, show π * (t.1 * -x + t.2.1 * -y) = -(π * (t.1 * x + t.2.1 * y)) by ring, Real.cos_neg]

/-! ## Translations -/

theorem cos_shift (U V a c m e k : ℤ) (hm : 0 < m) (hk : U * a + V * c - e * m = 2 * m * k) (x y : ℝ) :
    Real.cos (π * (U * (x + a / m) + V * (y + c / m))) = (-1) ^ e.natAbs * Real.cos (π * (U * x + V * y)) := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk' : (U : ℝ) * a + V * c = e * m + 2 * m * k := by
    have : U * a + V * c = e * m + 2 * m * k := by linarith
    exact_mod_cast this
  have h2 : (U : ℝ) * (a / m) + V * (c / m) = e + 2 * k := by
    rw [mul_div_assoc', mul_div_assoc', ← add_div, hk']; field_simp
  have harg : π * (U * (x + a / m) + V * (y + c / m)) = π * (U * x + V * y) + (e : ℝ) * π + (k : ℤ) * (2 * π) := by
    have : π * (U * (x + a / m) + V * (y + c / m)) = π * (U * x + V * y) + π * ((U : ℝ) * (a / m) + V * (c / m)) := by ring
    rw [this, h2]; ring
  rw [harg, Real.cos_add_int_mul_two_pi]
  rcases Int.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · have : (e : ℝ) * π = (j : ℤ) * (2 * π) := by rw [hj]; push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
    have : Even e.natAbs := by rw [Int.natAbs_even]; exact ⟨j, hj⟩
    rw [this.neg_one_pow, one_mul]
  · have : (e : ℝ) * π = π + (j : ℤ) * (2 * π) := by rw [hj]; push_cast; ring
    rw [this, ← add_assoc, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
    have : Odd e.natAbs := by rw [Int.natAbs_odd]; exact ⟨j, hj⟩
    rw [this.neg_one_pow]; ring

theorem sumC_shift (ts : List (ℤ × ℤ × ℕ)) (a c m e : ℤ) (hm : 0 < m) (h : shiftOK ts a c m e = true) (x y : ℝ) :
    sumC ts (x + a / m) (y + c / m) = (-1) ^ e.natAbs * sumC ts x y := by
  induction ts with
  | nil => simp [sumC_nil]
  | cons t ts ih =>
    unfold shiftOK at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h1
    rw [sumC_cons, sumC_cons, ih h2, cos_shift t.1 t.2.1 a c m e k hm hk]
    ring

theorem sumVal_shift_abs (ts : List (ℤ × ℤ × ℕ)) (Dn : ℕ) (a c m e : ℤ) (hm : 0 < m) (h : shiftOK ts a c m e = true) (x y : ℝ) :
    |sumVal ts Dn (x + a / m) (y + c / m)| = |sumVal ts Dn x y| := by
  rw [sumVal_eq, sumVal_eq, sumC_shift ts a c m e hm h, mul_div_assoc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem sumVal_shift (ts : List (ℤ × ℤ × ℕ)) (Dn : ℕ) (a c m : ℤ) (hm : 0 < m) (h : shiftOK ts a c m 0 = true) (x y : ℝ) :
    sumVal ts Dn (x + a / m) (y + c / m) = sumVal ts Dn x y := by
  rw [sumVal_eq, sumVal_eq, sumC_shift ts a c m 0 hm h]; simp

/-! ## Swap -/

theorem term_swap (t : ℤ × ℤ × ℕ) (x y : ℝ) :
    (t.2.2 : ℝ) * Real.cos (π * (t.1 * y + t.2.1 * x)) =
      ((nrmT (swpT t)).2.2 : ℝ) * Real.cos (π * ((nrmT (swpT t)).1 * x + (nrmT (swpT t)).2.1 * y)) := by
  unfold nrmT swpT
  simp only []
  split_ifs
  · simp only []
    push_cast
    rw [show π * (-(t.2.1 : ℝ) * x + -(t.1 : ℝ) * y) = -(π * (t.1 * y + t.2.1 * x)) by ring, Real.cos_neg]
  · simp only []; congr 2; ring

theorem sumC_swap (ts : List (ℤ × ℤ × ℕ)) (x y : ℝ) : sumC ts y x = sumC (ts.map (fun t => nrmT (swpT t))) x y := by
  induction ts with
  | nil => rw [List.map_nil, sumC_nil, sumC_nil]
  | cons t ts ih => rw [List.map_cons, sumC_cons, sumC_cons, ih, term_swap]

theorem sumC_perm (a b : List (ℤ × ℤ × ℕ)) (h : a.Perm b) (x y : ℝ) : sumC a x y = sumC b x y := by
  unfold sumC; exact (h.map _).sum_eq

/-! ## `Good` is invariant -/

/-- the symmetry data of a configuration. -/
structure SymOK (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (m : ℕ) (shifts : List (ℤ × ℤ)) : Prop where
  hm : 0 < m
  hTsh : ∀ ac ∈ shifts, shiftOK Tts ac.1 ac.2 m 0 = true
  hFsh : ∀ ac ∈ shifts, ∀ f ∈ C.facs, shiftOK f.1 ac.1 ac.2 m 0 = true ∨ shiftOK f.1 ac.1 ac.2 m 1 = true
  hTsw : (Tts.map (fun t => nrmT (swpT t))).Perm Tts
  hFsw : C.facs.map (fun f => (f.1.map (fun t => nrmT (swpT t)), f.2)) = C.facs.reverse
  hm0 : ((m : ℤ), (0 : ℤ)) ∈ shifts
  h0m : ((0 : ℤ), (m : ℤ)) ∈ shifts

theorem prod_abs_shift (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (m : ℕ) (shifts : List (ℤ × ℤ)) (hS : SymOK C Tts m shifts)
    (ac : ℤ × ℤ) (hac : ac ∈ shifts) (x y : ℝ) :
    (C.facs.map (fun f => |sumVal f.1 f.2 (x + ac.1 / (m : ℤ)) (y + ac.2 / (m : ℤ))|)).prod =
      (C.facs.map (fun f => |sumVal f.1 f.2 x y|)).prod := by
  have hm : (0 : ℤ) < m := by exact_mod_cast hS.hm
  have key : ∀ f ∈ C.facs, |sumVal f.1 f.2 (x + ac.1 / (m : ℤ)) (y + ac.2 / (m : ℤ))| = |sumVal f.1 f.2 x y| := by
    intro f hf
    rcases hS.hFsh ac hac f hf with h | h
    · exact sumVal_shift_abs f.1 f.2 ac.1 ac.2 m 0 hm h x y
    · exact sumVal_shift_abs f.1 f.2 ac.1 ac.2 m 1 hm h x y
  rw [List.map_congr_left key]

theorem good_shift (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn m : ℕ) (shifts : List (ℤ × ℤ)) (hS : SymOK C Tts m shifts)
    (ac : ℤ × ℤ) (hac : ac ∈ shifts) (x y : ℝ) :
    Good C Tts TDn (x + ac.1 / (m : ℤ)) (y + ac.2 / (m : ℤ)) ↔ Good C Tts TDn x y := by
  unfold Good
  have hm : (0 : ℤ) < m := by exact_mod_cast hS.hm
  rw [prod_abs_shift C Tts m shifts hS ac hac, sumVal_shift Tts TDn ac.1 ac.2 m hm (hS.hTsh ac hac)]

theorem good_neg (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (x y : ℝ) :
    Good C Tts TDn (-x) (-y) ↔ Good C Tts TDn x y := by
  unfold Good
  simp only [sumVal_eq, sumC_neg]

theorem good_swap (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (m : ℕ) (shifts : List (ℤ × ℤ)) (TDn : ℕ) (hS : SymOK C Tts m shifts)
    (x y : ℝ) : Good C Tts TDn y x ↔ Good C Tts TDn x y := by
  unfold Good
  have hT : sumVal Tts TDn y x = sumVal Tts TDn x y := by
    rw [sumVal_eq, sumVal_eq, sumC_swap, sumC_perm _ _ hS.hTsw]
  have hF : (C.facs.map (fun f => |sumVal f.1 f.2 y x|)).prod = (C.facs.map (fun f => |sumVal f.1 f.2 x y|)).prod := by
    have e1 : C.facs.map (fun f => |sumVal f.1 f.2 y x|) =
        (C.facs.map (fun f => (f.1.map (fun t => nrmT (swpT t)), f.2))).map (fun f => |sumVal f.1 f.2 x y|) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro f _
      show |sumVal f.1 f.2 y x| = |sumVal (f.1.map (fun t => nrmT (swpT t))) f.2 x y|
      rw [sumVal_eq, sumVal_eq, sumC_swap]
    rw [e1, hS.hFsw, List.map_reverse, List.prod_reverse]
  rw [hT, hF]

/-- translations by integers. -/
theorem good_int (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn m : ℕ) (shifts : List (ℤ × ℤ)) (hS : SymOK C Tts m shifts)
    (x y : ℝ) (n1 n2 : ℤ) : Good C Tts TDn (x + n1) (y + n2) ↔ Good C Tts TDn x y := by
  have hmr : ((m : ℤ) : ℝ) ≠ 0 := by have := hS.hm; exact_mod_cast this.ne'
  have hx1 : ∀ x y : ℝ, Good C Tts TDn (x + 1) y ↔ Good C Tts TDn x y := by
    intro x y
    have := good_shift C Tts TDn m shifts hS _ hS.hm0 x y
    simp only [Int.cast_zero, zero_div, add_zero] at this
    rwa [div_self hmr] at this
  have hy1 : ∀ x y : ℝ, Good C Tts TDn x (y + 1) ↔ Good C Tts TDn x y := by
    intro x y
    have := good_shift C Tts TDn m shifts hS _ hS.h0m x y
    simp only [Int.cast_zero, zero_div, add_zero] at this
    rwa [div_self hmr] at this
  have hxn : ∀ (n : ℕ) (x y : ℝ), Good C Tts TDn (x + n) y ↔ Good C Tts TDn x y := by
    intro n; induction n with
    | zero => intro x y; simp
    | succ n ih => intro x y; rw [Nat.cast_succ, ← add_assoc, hx1, ih]
  have hyn : ∀ (n : ℕ) (x y : ℝ), Good C Tts TDn x (y + n) ↔ Good C Tts TDn x y := by
    intro n; induction n with
    | zero => intro x y; simp
    | succ n ih => intro x y; rw [Nat.cast_succ, ← add_assoc, hy1, ih]
  have hxz : ∀ (n : ℤ) (x y : ℝ), Good C Tts TDn (x + n) y ↔ Good C Tts TDn x y := by
    intro n x y
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · simpa using hxn k x y
    · have := hxn k (x + ((-(k : ℤ)) : ℤ)) y
      push_cast at this ⊢
      rw [show x + -(k : ℝ) + k = x by ring] at this
      exact this.symm
  have hyz : ∀ (n : ℤ) (x y : ℝ), Good C Tts TDn x (y + n) ↔ Good C Tts TDn x y := by
    intro n x y
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · simpa using hyn k x y
    · have := hyn k x (y + ((-(k : ℤ)) : ℤ))
      push_cast at this ⊢
      rw [show y + -(k : ℝ) + k = y by ring] at this
      exact this.symm
  rw [hxz, hyz]


/-! ## Covering -/

theorem allN_spec (p : ℕ → Bool) (n : ℕ) (h : allN p n = true) : ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [allN, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact ih h.1 i hi
    · rw [hi]; exact h.2

theorem bmap_spec (Q0 : ℕ) (L : List (ℕ × ℕ)) (n : ℕ) (h : Nat.testBit (bmap Q0 L) n = true) :
    ∃ jk ∈ L, jk.1 * Q0 + jk.2 = n := by
  induction L with
  | nil => simp [bmap] at h
  | cons jk L ih =>
    simp only [bmap, List.foldr_cons] at h
    change ((bmap Q0 L) ||| 2 ^ (jk.1 * Q0 + jk.2)).testBit n = true at h
    rw [Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨jk', hm, he⟩ := ih h; exact ⟨jk', List.mem_cons_of_mem _ hm, he⟩
    · rw [Nat.testBit_two_pow] at h
      simp only [decide_eq_true_eq] at h
      exact ⟨jk, List.mem_cons_self, h⟩

/-- membership in a closed level-0 cell. -/
def InCell (Q0 j k : ℕ) (x y : ℝ) : Prop :=
  ((j : ℝ) / Q0 ≤ x ∧ x ≤ (j + 1 : ℝ) / Q0) ∧ ((k : ℝ) / Q0 ≤ y ∧ y ≤ (k + 1 : ℝ) / Q0)

theorem inCell_swap (Q0 j k : ℕ) (x y : ℝ) (h : InCell Q0 j k x y) : InCell Q0 k j y x := ⟨h.2, h.1⟩

theorem inCell_neg (Q0 j k : ℕ) (hj : j < Q0) (hk : k < Q0) (x y : ℝ) (h : InCell Q0 j k x y) :
    InCell Q0 (Q0 - 1 - j) (Q0 - 1 - k) (1 - x) (1 - y) := by
  have hQ : (0 : ℝ) < Q0 := by exact_mod_cast (by omega : 0 < Q0)
  have e1 : ((Q0 - 1 - j : ℕ) : ℝ) = Q0 - 1 - j := by rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have e2 : ((Q0 - 1 - k : ℕ) : ℝ) = Q0 - 1 - k := by rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  rw [div_le_iff₀ hQ] at h1 h3; rw [le_div_iff₀ hQ] at h2 h4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [rw [e1, div_le_iff₀ hQ]; rw [e1, le_div_iff₀ hQ]; rw [e2, div_le_iff₀ hQ];
    rw [e2, le_div_iff₀ hQ]] <;> nlinarith

theorem inCell_shift (Q0 st m j a : ℕ) (hQ : Q0 = m * st) (hm : 0 < m) (hj : j < Q0) (ha : a < m) (x : ℝ)
    (h : (j : ℝ) / Q0 ≤ x ∧ x ≤ (j + 1 : ℝ) / Q0) :
    (((j + a * st) % Q0 : ℕ) : ℝ) / Q0 ≤ x + (a : ℤ) / (m : ℤ) - (((j + a * st) / Q0 : ℕ) : ℤ) ∧
      x + (a : ℤ) / (m : ℤ) - (((j + a * st) / Q0 : ℕ) : ℤ) ≤ (((j + a * st) % Q0 : ℕ) + 1 : ℝ) / Q0 := by
  have hQ0 : 0 < Q0 := by omega
  have hQr : (0 : ℝ) < Q0 := by exact_mod_cast hQ0
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hdm := Nat.div_add_mod (j + a * st) Q0
  have e : ((j + a * st : ℕ) : ℝ) = Q0 * (((j + a * st) / Q0 : ℕ) : ℝ) + (((j + a * st) % Q0 : ℕ) : ℝ) := by
    exact_mod_cast hdm.symm
  have hst0 : 0 < st := by
    rcases Nat.eq_zero_or_pos st with h | h
    · rw [h, mul_zero] at hQ; omega
    · exact h
  have ham : (a : ℝ) / m = (a * st : ℝ) / Q0 := by
    rw [hQ]; push_cast
    have hst : (0 : ℝ) < st := by exact_mod_cast hst0
    field_simp
  push_cast at e
  simp only [Int.cast_natCast]
  rw [ham]
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [div_le_iff₀ hQr] at h1 ⊢
    have : (x + a * st / Q0 - ((j + a * st) / Q0 : ℕ)) * Q0 = x * Q0 + a * st - ((j + a * st) / Q0 : ℕ) * Q0 := by
      field_simp
    rw [this]; nlinarith
  · rw [le_div_iff₀ hQr] at h2 ⊢
    have : (x + a * st / Q0 - ((j + a * st) / Q0 : ℕ)) * Q0 = x * Q0 + a * st - ((j + a * st) / Q0 : ℕ) * Q0 := by
      field_simp
    rw [this]; nlinarith


theorem good_sw (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn m : ℕ) (shifts : List (ℤ × ℤ)) (hS : SymOK C Tts m shifts)
    (sw : Bool) (x y : ℝ) (h : Good C Tts TDn (if sw then y else x) (if sw then x else y)) : Good C Tts TDn x y := by
  cases sw
  · exact h
  · exact (good_swap C Tts m shifts TDn hS x y).1 h

theorem good_ng (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn m : ℕ) (shifts : List (ℤ × ℤ)) (hS : SymOK C Tts m shifts)
    (ng : Bool) (x y : ℝ) (h : Good C Tts TDn (if ng then 1 - x else x) (if ng then 1 - y else y)) : Good C Tts TDn x y := by
  cases ng
  · exact h
  · simp only [ite_true] at h
    have h0 : Good C Tts TDn (-x + ((1 : ℤ) : ℝ)) (-y + ((1 : ℤ) : ℝ)) := by
      push_cast
      rw [show -x + 1 = 1 - x by ring, show -y + 1 = 1 - y by ring]
      exact h
    have h1 := (good_int C Tts TDn m shifts hS (-x) (-y) 1 1).1 h0
    exact (good_neg C Tts TDn x y).1 h1

theorem inCell_sw (Q0 j k : ℕ) (sw : Bool) (x y : ℝ) (h : InCell Q0 j k x y) :
    InCell Q0 (if sw then k else j) (if sw then j else k) (if sw then y else x) (if sw then x else y) := by
  cases sw
  · exact h
  · exact inCell_swap Q0 j k x y h

theorem inCell_ng (Q0 j k : ℕ) (hj : j < Q0) (hk : k < Q0) (ng : Bool) (x y : ℝ) (h : InCell Q0 j k x y) :
    InCell Q0 (if ng then Q0 - 1 - j else j) (if ng then Q0 - 1 - k else k) (if ng then 1 - x else x) (if ng then 1 - y else y) := by
  cases ng
  · exact h
  · exact inCell_neg Q0 j k hj hk x y h

theorem good_unit (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (hC : CfgOK C Tts TDn) (m : ℕ) (shifts : List (ℤ × ℤ))
    (hS : SymOK C Tts m shifts) (st : ℕ) (hQ : C.Q0 = m * st) (G : List (Bool × Bool × ℕ × ℕ))
    (hG : ∀ g ∈ G, ((g.2.2.1 : ℤ), (g.2.2.2 : ℤ)) ∈ shifts ∧ g.2.2.1 < m ∧ g.2.2.2 < m) (L : List (ℕ × ℕ))
    (hL : checkList C L = true) (hLlt : ∀ jk ∈ L, jk.2 < C.Q0) (hcov : coverOK C.Q0 st G L = true)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) : Good C Tts TDn x y := by
  have hm := hS.hm
  have hQ0 := hC.hQ0
  have hQr : (0 : ℝ) < C.Q0 := by exact_mod_cast hQ0
  set Q0 := C.Q0 with hQ0d
  -- the cell of the point
  set j := ⌊x * Q0⌋₊ with hjd
  set k := ⌊y * Q0⌋₊ with hkd
  have hj : j < Q0 := by
    rw [hjd, Nat.floor_lt (by positivity)]; nlinarith
  have hk : k < Q0 := by
    rw [hkd, Nat.floor_lt (by positivity)]; nlinarith
  have hcell : InCell Q0 j k x y := by
    have a1 := Nat.floor_le (by positivity : 0 ≤ x * Q0)
    have a2 := Nat.lt_floor_add_one (x * Q0)
    have b1 := Nat.floor_le (by positivity : 0 ≤ y * Q0)
    have b2 := Nat.lt_floor_add_one (y * Q0)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [div_le_iff₀ hQr]; exact a1
    · rw [le_div_iff₀ hQr]; push_cast; linarith
    · rw [div_le_iff₀ hQr]; exact b1
    · rw [le_div_iff₀ hQr]; push_cast; linarith
  -- the covering element
  unfold coverOK at hcov
  have h1 := allN_spec _ _ hcov j hj
  have h2 := allN_spec _ _ h1 k hk
  rw [List.any_eq_true] at h2
  obtain ⟨⟨sw, ng, a, c⟩, hgG, hbit⟩ := h2
  obtain ⟨hsh, ha, hc⟩ := hG _ hgG
  simp only at hsh ha hc
  obtain ⟨jk, hjk, heq⟩ := bmap_spec _ _ _ hbit
  -- the transformed point
  set j1 := (if sw then k else j) with hj1
  set k1 := (if sw then j else k) with hk1
  have hj1l : j1 < Q0 := by rw [hj1]; split_ifs <;> assumption
  have hk1l : k1 < Q0 := by rw [hk1]; split_ifs <;> assumption
  have c1 := inCell_sw Q0 j k sw x y hcell
  set x1 := (if sw then y else x)
  set y1 := (if sw then x else y)
  have c2 := inCell_ng Q0 j1 k1 hj1l hk1l ng x1 y1 c1
  set j2 := (if ng then Q0 - 1 - j1 else j1) with hj2
  set k2 := (if ng then Q0 - 1 - k1 else k1) with hk2
  have hj2l : j2 < Q0 := by rw [hj2]; split_ifs <;> omega
  have hk2l : k2 < Q0 := by rw [hk2]; split_ifs <;> omega
  set x2 := (if ng then 1 - x1 else x1)
  set y2 := (if ng then 1 - y1 else y1)
  have himg : imgC Q0 st (sw, ng, a, c) j k = ((j2 + a * st) % Q0, (k2 + c * st) % Q0) := by
    unfold imgC; cases sw <;> cases ng <;> rfl
  rw [himg] at heq
  have hjk2 := hLlt jk hjk
  have hjkeq : jk = ((j2 + a * st) % Q0, (k2 + c * st) % Q0) := by
    have hm2 : (k2 + c * st) % Q0 < Q0 := Nat.mod_lt _ (by omega)
    have e1 : jk.2 = (k2 + c * st) % Q0 := by
      have := congrArg (· % Q0) heq
      simp only [Nat.mul_comm _ Q0, Nat.mul_add_mod, Nat.mod_eq_of_lt hjk2, Nat.mod_eq_of_lt hm2] at this
      exact this
    have e2 : jk.1 = (j2 + a * st) % Q0 := by
      have := congrArg (· / Q0) heq
      simp only [Nat.mul_comm _ Q0, Nat.mul_add_div (by omega : 0 < Q0), Nat.div_eq_of_lt hjk2,
        Nat.div_eq_of_lt hm2, add_zero] at this
      exact this
    exact Prod.ext e2 e1
  have sx := inCell_shift Q0 st m j2 a hQ hm hj2l ha x2 c2.1
  have sy := inCell_shift Q0 st m k2 c hQ hm hk2l hc y2 c2.2
  have g3 := checkList_sound C Tts TDn hC L hL jk hjk _ _ (by rw [hjkeq]; exact sx) (by rw [hjkeq]; exact sy)
  have g2 := (good_int C Tts TDn m shifts hS _ _ (((j2 + a * st) / Q0 : ℕ) : ℤ) (((k2 + c * st) / Q0 : ℕ) : ℤ)).2 g3
  simp only [sub_add_cancel] at g2
  have g1 := (good_shift C Tts TDn m shifts hS ((a : ℤ), (c : ℤ)) hsh x2 y2).1 g2
  exact good_sw C Tts TDn m shifts hS sw x y (good_ng C Tts TDn m shifts hS ng x1 y1 g1)

/-- **From the listed cells to the whole plane.** -/
theorem good_all (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (hC : CfgOK C Tts TDn) (m : ℕ) (shifts : List (ℤ × ℤ))
    (hS : SymOK C Tts m shifts) (st : ℕ) (hQ : C.Q0 = m * st) (G : List (Bool × Bool × ℕ × ℕ))
    (hG : ∀ g ∈ G, ((g.2.2.1 : ℤ), (g.2.2.2 : ℤ)) ∈ shifts ∧ g.2.2.1 < m ∧ g.2.2.2 < m) (L : List (ℕ × ℕ))
    (hL : checkList C L = true) (hLlt : ∀ jk ∈ L, jk.2 < C.Q0) (hcov : coverOK C.Q0 st G L = true) :
    ∀ x y : ℝ, Good C Tts TDn x y := by
  intro x y
  have h := good_unit C Tts TDn hC m shifts hS st hQ G hG L hL hLlt hcov (Int.fract x) (Int.fract y)
    (Int.fract_nonneg x) (Int.fract_lt_one x) (Int.fract_nonneg y) (Int.fract_lt_one y)
  have := (good_int C Tts TDn m shifts hS (Int.fract x) (Int.fract y) ⌊x⌋ ⌊y⌋).2 h
  rwa [Int.fract_add_floor, Int.fract_add_floor] at this

end Palprimes.M2
