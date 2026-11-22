import Palprimes.Major2D.Sound

/-! # Soundness of the 2D kernel checker, part 2: lower bounds, products, freezing, cells -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real

namespace Palprimes.M2

/-! ## Signed pairs -/

theorem Z2.ab_eq (z : Z2) : ((z.ab : ℕ) : ℝ) = |z.r| := by
  unfold Z2.ab Z2.r
  simp only [Nat.add_eq, Nat.sub_eq]
  rcases le_total z.n z.p with h | h
  · have h' : (z.n : ℝ) ≤ z.p := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by linarith)]
  · have h' : (z.p : ℝ) ≤ z.n := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by linarith)]; ring

theorem Z2.nrm_r (z : Z2) : z.nrm.r = z.r := by
  unfold Z2.nrm Z2.r
  simp only [Nat.sub_eq]
  rcases le_total z.n z.p with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; simp
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; simp

theorem Z2.mul_r (a b : Z2) : (Z2.mul a b).r = a.r * b.r := by
  unfold Z2.mul Z2.r; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; ring

theorem Z2.add_r (a b : Z2) : (Z2.add a b).r = a.r + b.r := by
  unfold Z2.add Z2.r; simp only [Nat.add_eq]; push_cast; ring

theorem Z2.sub_r (a b : Z2) : (Z2.sub a b).r = a.r - b.r := by
  unfold Z2.sub Z2.r; simp only [Nat.add_eq]; push_cast; ring

theorem Z2.smul_r (k : ℕ) (a : Z2) : (Z2.smul k a).r = k * a.r := by
  unfold Z2.smul Z2.r; simp only [Nat.mul_eq]; push_cast; ring

theorem Z2.neg_r (a : Z2) : a.neg.r = -a.r := by unfold Z2.neg Z2.r; ring

theorem Z2.lt_iff (a b : Z2) : Z2.lt a b = true ↔ a.r < b.r := by
  unfold Z2.lt Z2.r
  simp only [Nat.add_eq, Nat.blt_eq]
  constructor
  · intro h; have : ((a.p + b.n : ℕ) : ℝ) < ((b.p + a.n : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  · intro h; have : ((a.p + b.n : ℕ) : ℝ) < ((b.p + a.n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-! ## Lower bound of a polynomial on the box -/

theorem quad_lb (a b c g1 g2 s u : ℝ) (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) :
    -(c * g1 ^ 2 - b * g1 * g2 + a * g2 ^ 2) / (4 * a * c - b ^ 2) ≤ a * s ^ 2 + b * (s * u) + c * u ^ 2 + g1 * s + g2 * u := by
  set D := 4 * a * c - b ^ 2
  set Nn := c * g1 ^ 2 - b * g1 * g2 + a * g2 ^ 2
  set Qv := a * s ^ 2 + b * (s * u) + c * u ^ 2 + g1 * s + g2 * u
  set X := D * s + 2 * c * g1 - b * g2
  set Y := D * u + 2 * a * g2 - b * g1
  have id1 : a * X ^ 2 + b * X * Y + c * Y ^ 2 = D ^ 2 * Qv + D * Nn := by
    simp only [X, Y, D, Qv, Nn]; ring
  have id2 : 4 * a * (a * X ^ 2 + b * X * Y + c * Y ^ 2) = (2 * a * X + b * Y) ^ 2 + D * Y ^ 2 := by
    simp only [D]; ring
  have h1 : 0 ≤ 4 * a * (D ^ 2 * Qv + D * Nn) := by
    rw [← id1, id2]; positivity
  have h2 : 0 ≤ D * Qv + Nn := by
    have : 0 ≤ (4 * a * D) * (D * Qv + Nn) := by nlinarith
    have h4 : 0 < 4 * a * D := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg h4 hneg
    linarith
  rw [div_le_iff₀ hD]
  linarith

theorem abs_mon_le {c m : ℝ} (hm : |m| ≤ 1) : -|c| ≤ c * m := by
  have : |c * m| ≤ |c| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hm
  linarith [neg_abs_le (c * m)]

/-- **Lower bound**: `lowOK h rem` certifies `h > rem` on `[−1,1]²`. -/
theorem lowOK_sound (h : Poly) (rem : ℕ) (hok : lowOK h rem = true) (s u : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    (rem : ℝ) < h.ev s u := by
  have hm := mon_bound s u hs hu
  have m10 := hm 1 0; have m01 := hm 0 1; have m20 := hm 2 0; have m11 := hm 1 1; have m02 := hm 0 2
  have m30 := hm 3 0; have m21 := hm 2 1; have m12 := hm 1 2; have m03 := hm 0 3
  simp only [pow_one, pow_zero, one_mul, mul_one] at m10 m01 m20 m11 m02 m30 m21 m12 m03
  have c6 := abs_mon_le (c := h.c6.r) m30
  have c7 := abs_mon_le (c := h.c7.r) m21
  have c8 := abs_mon_le (c := h.c8.r) m12
  have c9 := abs_mon_le (c := h.c9.r) m03
  have hc3 : ((h.c3sum : ℕ) : ℝ) = |h.c6.r| + |h.c7.r| + |h.c8.r| + |h.c9.r| := by
    unfold Poly.c3sum; push_cast; rw [Z2.ab_eq, Z2.ab_eq, Z2.ab_eq, Z2.ab_eq]
  have hc12 : ((h.c12sum : ℕ) : ℝ) = |h.c1.r| + |h.c2.r| + |h.c3.r| + |h.c4.r| + |h.c5.r| := by
    unfold Poly.c12sum; push_cast; rw [Z2.ab_eq, Z2.ab_eq, Z2.ab_eq, Z2.ab_eq, Z2.ab_eq]
  unfold lowOK at hok
  simp only [Bool.or_eq_true, Nat.blt_eq] at hok
  unfold Poly.ev
  rcases hok with h1 | h1
  · -- crude bound
    have h1' : ((h.c12sum + (h.c0.n + (h.c3sum + rem)) : ℕ) : ℝ) < (h.c0.p : ℝ) := by exact_mod_cast h1
    push_cast at h1'
    have c1 := abs_mon_le (c := h.c1.r) m10
    have c2 := abs_mon_le (c := h.c2.r) m01
    have c3 := abs_mon_le (c := h.c3.r) m20
    have c4 := abs_mon_le (c := h.c4.r) m11
    have c5 := abs_mon_le (c := h.c5.r) m02
    have e0 : h.c0.r = (h.c0.p : ℝ) - h.c0.n := rfl
    linarith
  · -- positive definite quadratic part
    unfold pdOK at h1
    simp only [Bool.and_eq_true, Nat.blt_eq, Z2.lt_iff, Z2.sub_r, Z2.smul_r, Z2.mul_r, Z2.add_r, Z2.nrm_r] at h1
    obtain ⟨⟨ha, hD⟩, hN⟩ := h1
    have ha' : 0 < h.c3.r := by
      have : h.c3.nrm.n < h.c3.nrm.p := ha
      have h2 : ((h.c3.nrm.n : ℕ) : ℝ) < (h.c3.nrm.p : ℝ) := by exact_mod_cast this
      rw [← Z2.nrm_r]; unfold Z2.r; linarith
    have hD' : 0 < 4 * h.c3.r * h.c5.r - h.c4.r ^ 2 := by
      have e : (⟨0, 0⟩ : Z2).r = 0 := by simp [Z2.r]
      rw [e] at hD; push_cast at hD; nlinarith
    have hq := quad_lb h.c3.r h.c4.r h.c5.r h.c1.r h.c2.r s u ha' hD'
    have hbase : (⟨h.c0.p, h.c0.n + (h.c3sum + rem)⟩ : Z2).r = h.c0.r - h.c3sum - rem := by
      unfold Z2.r; push_cast; ring
    rw [hbase] at hN
    have hN' : (h.c5.r * h.c1.r ^ 2 - h.c4.r * h.c1.r * h.c2.r + h.c3.r * h.c2.r ^ 2) / (4 * h.c3.r * h.c5.r - h.c4.r ^ 2) <
        h.c0.r - h.c3sum - rem := by
      rw [div_lt_iff₀ hD']
      have : (h.c5.r * (h.c1.r * h.c1.r) - h.c4.r * (h.c1.r * h.c2.r) + h.c3.r * (h.c2.r * h.c2.r)) <
        (h.c0.r - h.c3sum - rem) * (4 * (h.c3.r * h.c5.r) - h.c4.r * h.c4.r) := hN
      nlinarith
    rw [neg_div] at hq
    linarith

/-! ## Combination -/

theorem combH_ev (t a : Poly) (K1 K0 : ℕ) (s u : ℝ) :
    (combH t a K1 K0).ev s u = t.ev s u * 2 ^ 64 - K1 * a.ev s u - K0 * 2 ^ 64 := by
  unfold combH combZ Poly.ev
  simp only [Z2.sub_r]
  unfold Z2.r one two64
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

theorem Poly.neg_ev (h : Poly) (s u : ℝ) : h.neg.ev s u = -h.ev s u := by
  unfold Poly.neg Poly.ev; simp only [Z2.neg_r]; ring


/-! ## Products of sums -/

/-- the undivided sum `Σ c cos(π(Ux + Vy))`. -/
noncomputable def sumC (ts : List (ℤ × ℤ × ℕ)) (x y : ℝ) : ℝ :=
  (ts.map (fun t => (t.2.2 : ℝ) * Real.cos (π * (t.1 * x + t.2.1 * y)))).sum

theorem sumC_append (a b : List (ℤ × ℤ × ℕ)) (x y : ℝ) : sumC (a ++ b) x y = sumC a x y + sumC b x y := by
  unfold sumC; rw [List.map_append, List.sum_append]

theorem sumC_inner (a : ℤ × ℤ × ℕ) (t : List (ℤ × ℤ × ℕ)) (x y : ℝ) :
    sumC (t.flatMap (fun c => [(a.1 + c.1, a.2.1 + c.2.1, a.2.2 * c.2.2), (a.1 - c.1, a.2.1 - c.2.1, a.2.2 * c.2.2)])) x y =
      2 * ((a.2.2 : ℝ) * Real.cos (π * (a.1 * x + a.2.1 * y))) * sumC t x y := by
  induction t with
  | nil => simp [sumC]
  | cons c t ih =>
    rw [List.flatMap_cons, sumC_append, ih]
    unfold sumC
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    have e1 : π * ((a.1 + c.1 : ℝ) * x + (a.2.1 + c.2.1 : ℝ) * y) = π * (a.1 * x + a.2.1 * y) + π * (c.1 * x + c.2.1 * y) := by ring
    have e2 : π * ((a.1 - c.1 : ℝ) * x + (a.2.1 - c.2.1 : ℝ) * y) = π * (a.1 * x + a.2.1 * y) - π * (c.1 * x + c.2.1 * y) := by ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    ring

theorem sumC_comb (s t : List (ℤ × ℤ × ℕ)) (x y : ℝ) : sumC (comb s t) x y = 2 * sumC s x y * sumC t x y := by
  unfold comb
  induction s with
  | nil => simp [sumC]
  | cons a s ih =>
    rw [List.flatMap_cons, sumC_append, ih, sumC_inner]
    unfold sumC; simp only [List.map_cons, List.sum_cons]; ring

theorem sumVal_eq (ts : List (ℤ × ℤ × ℕ)) (Dn : ℕ) (x y : ℝ) : sumVal ts Dn x y = sumC ts x y / Dn := rfl

theorem sumVal_prodL (L : List (List (ℤ × ℤ × ℕ) × ℕ)) (hL : ∀ f ∈ L, 0 < f.2) (x y : ℝ) :
    0 < (prodL L).2 ∧ sumVal (prodL L).1 (prodL L).2 x y = (L.map (fun f => sumVal f.1 f.2 x y)).prod := by
  induction L with
  | nil => simp [prodL, sumVal]
  | cons s L ih =>
    have hs := hL s (by simp)
    have ih' := ih (fun f hf => hL f (by simp [hf]))
    cases L with
    | nil => simp [prodL, hs]
    | cons t rest =>
      obtain ⟨h0, h1⟩ := ih'
      simp only [prodL] at h0 h1 ⊢
      refine ⟨by positivity, ?_⟩
      rw [List.map_cons, List.prod_cons, ← h1, sumVal_eq, sumVal_eq, sumVal_eq, sumC_comb]
      have : (0 : ℝ) < s.2 := by exact_mod_cast hs
      have : (0 : ℝ) < (prodL (t :: rest)).2 := by exact_mod_cast h0
      push_cast
      field_simp

/-! ## Selections by a mask -/

/-- the elements at positions `i, i+1, …` whose bit is clear (not frozen). -/
def selV {β : Type} (mask : ℕ) : ℕ → List β → List β
  | _, [] => []
  | i, v :: vs => if Nat.testBit mask i then selV mask (i + 1) vs else v :: selV mask (i + 1) vs

/-- the frozen elements. -/
def selC {β : Type} (mask : ℕ) : ℕ → List β → List β
  | _, [] => []
  | i, v :: vs => if Nat.testBit mask i then v :: selC mask (i + 1) vs else selC mask (i + 1) vs

theorem selF_eq (mask i : ℕ) (L : List (List (ℤ × ℤ × ℕ) × ℕ)) : selF mask i L = selV mask i L := by
  induction L generalizing i with
  | nil => rfl
  | cons f L ih => simp only [selF, selV, ih]

theorem selV_map {β γ : Type} (mask i : ℕ) (L : List β) (φ : β → γ) : (selV mask i L).map φ = selV mask i (L.map φ) := by
  induction L generalizing i with
  | nil => rfl
  | cons f L ih => simp only [selV, List.map_cons]; split_ifs <;> simp [ih]

theorem selV_mem {β : Type} (mask i : ℕ) (L : List β) (x : β) (hx : x ∈ selV mask i L) : x ∈ L := by
  induction L generalizing i with
  | nil => simp [selV] at hx
  | cons f L ih =>
    simp only [selV] at hx
    split_ifs at hx
    · exact List.mem_cons_of_mem _ (ih _ hx)
    · rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h)

theorem selC_mem {β : Type} (mask i : ℕ) (L : List β) (x : β) (hx : x ∈ selC mask i L) : x ∈ L := by
  induction L generalizing i with
  | nil => simp [selC] at hx
  | cons f L ih =>
    simp only [selC] at hx
    split_ifs at hx
    · rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ h)
    · exact List.mem_cons_of_mem _ (ih _ hx)

theorem prod_split (mask i : ℕ) (L : List ℝ) : L.prod = (selC mask i L).prod * (selV mask i L).prod := by
  induction L generalizing i with
  | nil => simp [selC, selV]
  | cons v L ih =>
    simp only [selC, selV, List.prod_cons]
    split_ifs <;> simp only [List.prod_cons] <;> rw [ih (i + 1)] <;> ring

/-- the per-factor facts. -/
def FacR (v : ℝ) (a : Bool × Bool × ℕ × ℕ) : Prop :=
  (a.2.1 = true → (a.1 = true → 0 ≤ v) ∧ (a.1 = false → v ≤ 0)) ∧ |v| ≤ (a.2.2.1 : ℝ) / 2 ^ 64 ∧ a.2.2.1 ≤ one

theorem sgn_sel (mask i : ℕ) (vals : List ℝ) (info : List (Bool × Bool × ℕ × ℕ)) (hR : List.Forall₂ FacR vals info)
    (hd : defAll mask i info = true) :
    (if sgnProd mask i info then (selV mask i vals).prod else -(selV mask i vals).prod) = (selV mask i (vals.map abs)).prod := by
  induction hR generalizing i with
  | nil => simp [sgnProd, selV]
  | @cons v a vs as hva hrest ih =>
    simp only [defAll, Bool.and_eq_true, Bool.or_eq_true] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have ih' := ih (i + 1) hd2
    simp only [sgnProd, selV, List.map_cons]
    by_cases hb : Nat.testBit mask i = true
    · simp only [hb, ite_true]; exact ih'
    · simp only [hb, Bool.false_eq_true, ite_false, List.prod_cons]
      have hdef : a.2.1 = true := by tauto
      obtain ⟨hpos, hneg⟩ := hva.1 hdef
      rw [← ih']
      rcases Bool.eq_false_or_eq_true a.1 with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (sgnProd mask (i + 1) as) with hs | hs
      · rw [ha, hs]; simp only [beq_self_eq_true, ite_true]; rw [abs_of_nonneg (hpos ha)]
      · rw [ha, hs]; simp only [show (false == true) = false from rfl, Bool.false_eq_true, ite_false, ite_true]
        rw [abs_of_nonneg (hpos ha)]; ring
      · rw [ha, hs]; simp only [show (true == false) = false from rfl, Bool.false_eq_true, ite_false, ite_true]
        rw [abs_of_nonpos (hneg ha)]; ring
      · rw [ha, hs]; simp only [beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false]
        rw [abs_of_nonpos (hneg ha)]; ring

theorem supProd_le (mask i : ℕ) (info : List (Bool × Bool × ℕ × ℕ)) (h : ∀ a ∈ info, a.2.2.1 ≤ one) :
    supProd mask i info ≤ one := by
  induction info generalizing i with
  | nil => simp [supProd]
  | cons a info ih =>
    have ih' := ih (i + 1) (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    simp only [supProd]
    split_ifs
    · unfold cdivN
      have hone : 0 < one := by unfold one two64; norm_num
      rw [Nat.div_le_iff_le_mul_add_pred hone]
      have : supProd mask (i + 1) info * a.2.2.1 ≤ one * one := Nat.mul_le_mul ih' ha
      omega
    · exact ih'

theorem frozen_le (mask i : ℕ) (vals : List ℝ) (info : List (Bool × Bool × ℕ × ℕ)) (hR : List.Forall₂ FacR vals info) :
    (selC mask i (vals.map abs)).prod ≤ (supProd mask i info : ℝ) / 2 ^ 64 := by
  induction hR generalizing i with
  | nil => simp [selC, supProd, one, two64]; norm_num
  | @cons v a vs as hva hrest ih =>
    have ih' := ih (i + 1)
    simp only [selC, supProd, List.map_cons]
    split_ifs
    · simp only [List.prod_cons]
      have h1 : |v| ≤ (a.2.2.1 : ℝ) / 2 ^ 64 := hva.2.1
      have h0 : 0 ≤ (selC mask (i + 1) (vs.map abs)).prod := by
        apply List.prod_nonneg; intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 (selC_mem mask (i + 1) _ x hx)
        exact abs_nonneg y
      have h2 : (0 : ℝ) ≤ (supProd mask (i + 1) as : ℝ) / 2 ^ 64 := by positivity
      have hone : 0 < one := by unfold one two64; norm_num
      calc |v| * (selC mask (i + 1) (vs.map abs)).prod ≤ ((a.2.2.1 : ℝ) / 2 ^ 64) * ((supProd mask (i + 1) as : ℝ) / 2 ^ 64) :=
            mul_le_mul h1 ih' h0 (by positivity)
        _ = ((supProd mask (i + 1) as * a.2.2.1 : ℕ) : ℝ) / (one : ℕ) / 2 ^ 64 := by
            unfold one two64; push_cast; ring
        _ ≤ _ := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact (ceil_div_near _ _ hone).1
    · exact ih'


/-! ## Factor information -/

theorem ev_near (h : Poly) (s u : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |h.ev s u - h.c0.r| ≤ ((h.c1.ab + h.c2.ab + h.c3.ab + h.c4.ab + h.c5.ab + h.c6.ab + h.c7.ab + h.c8.ab + h.c9.ab : ℕ) : ℝ) := by
  have hm := mon_bound s u hs hu
  have m10 := hm 1 0; have m01 := hm 0 1; have m20 := hm 2 0; have m11 := hm 1 1; have m02 := hm 0 2
  have m30 := hm 3 0; have m21 := hm 2 1; have m12 := hm 1 2; have m03 := hm 0 3
  simp only [pow_one, pow_zero, one_mul, mul_one] at m10 m01 m20 m11 m02 m30 m21 m12 m03
  have t : ∀ (c m : ℝ), |m| ≤ 1 → |c * m| ≤ |c| := fun c m hm => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hm
  push_cast
  simp only [Z2.ab_eq]
  unfold Poly.ev
  have e : h.c0.r + h.c1.r * s + h.c2.r * u + h.c3.r * s ^ 2 + h.c4.r * (s * u) + h.c5.r * u ^ 2 + h.c6.r * s ^ 3 +
      h.c7.r * (s ^ 2 * u) + h.c8.r * (s * u ^ 2) + h.c9.r * u ^ 3 - h.c0.r =
      h.c1.r * s + h.c2.r * u + h.c3.r * s ^ 2 + h.c4.r * (s * u) + h.c5.r * u ^ 2 + h.c6.r * s ^ 3 +
      h.c7.r * (s ^ 2 * u) + h.c8.r * (s * u ^ 2) + h.c9.r * u ^ 3 := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m03))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m12))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m21))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m30))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m02))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m11))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (t _ _ m20))
  exact le_trans (abs_add_le _ _) (add_le_add (t _ _ m10) (t _ _ m01))

theorem facInfo_sound (m : TM) (v : ℝ) (s u : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1)
    (hv : |v - m.p.ev s u / 2 ^ 64| ≤ (m.r : ℝ) / 2 ^ 64) (h1 : |v| ≤ 1) : FacR v (facInfo m) := by
  have he := ev_near m.p s u hs hu
  set rest := m.p.c1.ab + m.p.c2.ab + m.p.c3.ab + m.p.c4.ab + m.p.c5.ab + m.p.c6.ab + m.p.c7.ab + m.p.c8.ab + m.p.c9.ab
  have hc0 := Z2.ab_eq m.p.c0
  have hone : ((one : ℕ) : ℝ) = 2 ^ 64 := by unfold one two64; norm_num
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ 64 := ⟨_, rfl⟩
  rw [← hK] at hv hone
  have h64 : 0 < K := by rw [hK]; positivity
  have he' := abs_le.1 he
  have hv' := abs_le.1 hv
  have hvv1 : v * K - m.p.ev s u ≤ m.r := by
    have := mul_le_mul_of_nonneg_right hv'.2 h64.le
    rw [sub_mul, div_mul_cancel₀ _ h64.ne', div_mul_cancel₀ _ h64.ne'] at this; exact this
  have hvv2 : -(m.r : ℝ) ≤ v * K - m.p.ev s u := by
    have := mul_le_mul_of_nonneg_right hv'.1 h64.le
    rw [sub_mul, div_mul_cancel₀ _ h64.ne', neg_mul, div_mul_cancel₀ _ h64.ne'] at this; exact this
  have key1 : v * K ≤ m.p.c0.r + rest + m.r := by linarith [he'.2]
  have key2 : m.p.c0.r - rest - m.r ≤ v * K := by linarith [he'.1]
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    simp only [facInfo, Nat.ble_eq] at hd
    have hd' : ((rest + m.r : ℕ) : ℝ) ≤ (m.p.c0.ab : ℝ) := by exact_mod_cast hd
    push_cast at hd'
    rw [hc0] at hd'
    constructor
    · intro hsg
      simp only [facInfo, Nat.ble_eq] at hsg
      have : 0 ≤ m.p.c0.r := by
        unfold Z2.r
        have : (m.p.c0.n : ℝ) ≤ m.p.c0.p := by exact_mod_cast hsg
        linarith
      rw [abs_of_nonneg this] at hd'
      have : 0 ≤ v * K := by linarith
      by_contra hneg; push Not at hneg
      have := mul_neg_of_neg_of_pos hneg h64; linarith
    · intro hsg
      have hsg' : Nat.ble m.p.c0.n m.p.c0.p = false := hsg
      have : m.p.c0.r ≤ 0 := by
        unfold Z2.r
        have : m.p.c0.p < m.p.c0.n := by
          by_contra hh; push Not at hh
          have : Nat.ble m.p.c0.n m.p.c0.p = true := Nat.ble_eq.mpr hh
          rw [this] at hsg'; exact Bool.noConfusion hsg'
        have : (m.p.c0.p : ℝ) < m.p.c0.n := by exact_mod_cast this
        linarith
      rw [abs_of_nonpos this] at hd'
      have : v * K ≤ 0 := by linarith
      by_contra hneg; push Not at hneg
      have := mul_pos hneg h64; linarith
  · simp only [facInfo]
    rw [← hK]
    rcases le_total one (m.p.c0.ab + rest + m.r) with hh | hh
    · rw [min_eq_left hh, hone, div_self h64.ne']; exact h1
    · rw [min_eq_right hh]
      rw [le_div_iff₀ h64]
      have e : ((m.p.c0.ab + rest + m.r : ℕ) : ℝ) = |m.p.c0.r| + rest + m.r := by push_cast; rw [hc0]
      rw [e]
      have := neg_abs_le m.p.c0.r
      have := le_abs_self m.p.c0.r
      rcases le_total 0 v with hv0 | hv0
      · rw [abs_of_nonneg hv0]; linarith
      · rw [abs_of_nonpos hv0]; linarith
  · simp only [facInfo]; exact min_le_left _ _

/-! ## Powers -/

theorem root_le (a b : ℝ) (n : ℕ) (hn : n ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : b ≤ a ^ n) : b ^ ((n : ℝ)⁻¹) ≤ a := by
  calc b ^ ((n : ℝ)⁻¹) ≤ (a ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hb h (by positivity)
    _ = a := Real.pow_rpow_inv_natCast ha hn

/-- **The power bound**: `(X/2^64)^(−1/n0) ≤ powInv/2^64`. -/
theorem powInv_spec (U2 V X n0 : ℕ) (hn0 : 0 < n0) (hU2 : 2 * 2 ^ (64 * n0) ≤ U2 ^ n0)
    (hV : ∀ j < 256, 256 * 2 ^ (64 * n0) ≤ getV V j ^ n0 * (256 + j)) (hX1 : 1 ≤ X) (hX : X ≤ 2 ^ 64) :
    ((X : ℝ) / 2 ^ 64) ^ (-((n0 : ℝ)⁻¹)) ≤ (powInv U2 V X : ℝ) / 2 ^ 64 := by
  unfold powInv
  simp only []
  set L := Nat.log2 X with hL
  have hX0 : X ≠ 0 := by omega
  have hL1 : 2 ^ L ≤ X := (Nat.le_log2 hX0).mp le_rfl
  have hL2 : X < 2 ^ (L + 1) := (Nat.log2_lt hX0).mp (Nat.lt_succ_self _)
  have hL64 : L ≤ 64 := by
    by_contra hc; push Not at hc
    have : 2 ^ 65 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hc
    omega
  set e := QQ - L with he
  have he' : e + L = 64 := by unfold QQ at he; omega
  set j := Nat.shiftRight (Nat.shiftLeft X 8) L - 256 with hj
  have hsh : Nat.shiftRight (Nat.shiftLeft X 8) L = X * 256 / 2 ^ L := by
    rw [shr_eq, show Nat.shiftLeft X 8 = X * 2 ^ 8 from Nat.shiftLeft_eq X 8]; norm_num
  have hjlo : 256 ≤ X * 256 / 2 ^ L := by
    rw [Nat.le_div_iff_mul_le (by positivity)]; nlinarith
  have hjhi : X * 256 / 2 ^ L < 512 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hL2; nlinarith
  have hj256 : j < 256 := by rw [hj, hsh]; omega
  have hjv : 256 + j = X * 256 / 2 ^ L := by rw [hj, hsh]; omega
  set q : ℝ := (n0 : ℝ)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hn0' : n0 ≠ 0 := by omega
  -- the three factors
  have h2 : (2 : ℝ) ^ q ≤ (U2 : ℝ) / 2 ^ 64 := by
    apply root_le _ _ _ hn0' (by positivity) (by norm_num)
    rw [div_pow, le_div_iff₀ (by positivity), ← pow_mul]
    have : ((2 * 2 ^ (64 * n0) : ℕ) : ℝ) ≤ ((U2 ^ n0 : ℕ) : ℝ) := by exact_mod_cast hU2
    push_cast at this; linarith
  have hVj : ((256 : ℝ) / (256 + j)) ^ q ≤ (getV V j : ℝ) / 2 ^ 64 := by
    apply root_le _ _ _ hn0' (by positivity) (by positivity)
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), ← pow_mul]
    have : ((256 * 2 ^ (64 * n0) : ℕ) : ℝ) ≤ ((getV V j ^ n0 * (256 + j) : ℕ) : ℝ) := by exact_mod_cast hV j hj256
    push_cast at this; linarith
  have hν : ((256 + j : ℕ) : ℝ) / 256 ≤ (X : ℝ) / 2 ^ L := by
    rw [hjv, div_le_div_iff₀ (by norm_num) (by positivity)]
    have := Nat.div_mul_le_self (X * 256) (2 ^ L)
    have : (((X * 256 / 2 ^ L) * 2 ^ L : ℕ) : ℝ) ≤ ((X * 256 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  -- assemble
  have hsplit : (X : ℝ) / 2 ^ 64 = ((X : ℝ) / 2 ^ L) * ((2 : ℝ) ^ e)⁻¹ := by
    rw [← he']; rw [pow_add]; field_simp
  have hXL : (0 : ℝ) < (X : ℝ) / 2 ^ L := by
    have : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    positivity
  have hinv : (((2 : ℝ) ^ e)⁻¹) ^ (-q) = ((2 : ℝ) ^ e) ^ q := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  rw [hsplit, Real.mul_rpow hXL.le (by positivity), hinv]
  have hA : ((X : ℝ) / 2 ^ L) ^ (-q) ≤ (getV V j : ℝ) / 2 ^ 64 := by
    calc ((X : ℝ) / 2 ^ L) ^ (-q) ≤ (((256 + j : ℕ) : ℝ) / 256) ^ (-q) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hν (by linarith)
      _ = ((256 : ℝ) / (256 + j)) ^ q := by
          rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]; push_cast; rw [inv_div]
      _ ≤ _ := hVj
  have hB : ((2 : ℝ) ^ e) ^ q ≤ ((U2 : ℝ) / 2 ^ 64) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) h2 e
  have hC := (ceil_div_near (U2 ^ e * getV V j) (2 ^ (QQ * e)) (by positivity)).1
  calc ((X : ℝ) / 2 ^ L) ^ (-q) * ((2 : ℝ) ^ e) ^ q ≤ ((getV V j : ℝ) / 2 ^ 64) * (((U2 : ℝ) / 2 ^ 64) ^ e) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = ((U2 ^ e * getV V j : ℕ) : ℝ) / ((2 ^ (QQ * e) : ℕ) : ℝ) / 2 ^ 64 := by
        unfold QQ; push_cast; rw [div_pow, ← pow_mul]; ring
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        convert hC using 2

/-- weighted AM–GM: `A^p ≤ C^(p−1) (p A + (1−p) C)`. -/
theorem amgm (A C p : ℝ) (hA : 0 ≤ A) (hC : 0 < C) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    A ^ p ≤ C ^ (p - 1) * (p * A + (1 - p) * C) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hp0 (by linarith : 0 ≤ 1 - p) hA hC.le (by ring)
  have hc : C ^ (p - 1) * C ^ (1 - p) = 1 := by
    rw [← Real.rpow_add hC]; simp
  have hpos : 0 < C ^ (p - 1) := Real.rpow_pos_of_pos hC _
  calc A ^ p = C ^ (p - 1) * (A ^ p * C ^ (1 - p)) := by rw [mul_comm (A ^ p), ← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hpos.le


/-! ## One freeze option -/

theorem apsFrom_getD (O : ℕ) (facs : List (List (ℤ × ℤ × ℕ) × ℕ)) (m c k : ℕ) :
    (apsFrom O facs m c).getD k badS =
      if k < c then prepS O (prodL (selF (m + k) 0 facs)).1 (prodL (selF (m + k) 0 facs)).2 else badS := by
  induction c generalizing m k with
  | zero => simp [apsFrom]
  | succ c ih =>
    cases k with
    | zero => simp [apsFrom]
    | succ k =>
      simp only [apsFrom, List.getD_cons_succ, ih]
      have e : m + 1 + k = m + (k + 1) := by ring
      rw [e]; simp only [Nat.add_lt_add_iff_right]

theorem prod_abs_nonneg (L : List ℝ) : 0 ≤ (L.map abs).prod := by
  apply List.prod_nonneg; intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg y

theorem selV_abs_nonneg (mask i : ℕ) (L : List ℝ) : 0 ≤ (selV mask i (L.map abs)).prod := by
  apply List.prod_nonneg; intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 (selV_mem mask i _ x hx); exact abs_nonneg y

theorem selC_abs_nonneg (mask i : ℕ) (L : List ℝ) : 0 ≤ (selC mask i (L.map abs)).prod := by
  apply List.prod_nonneg; intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 (selC_mem mask i _ x hx); exact abs_nonneg y

theorem forall2_sup (vals : List ℝ) (info : List (Bool × Bool × ℕ × ℕ)) (hR : List.Forall₂ FacR vals info) :
    ∀ a ∈ info, a.2.2.1 ≤ one := by
  induction hR with
  | nil => simp
  | cons h _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with e | e
    · rw [e]; exact h.2.2
    · exact ih a e

/-- the real-number core of one freeze option. -/
theorem opt_core (Tv At Fr tev aev : ℝ) (tr ar St Ct X pe Wt K1 K0 n0 : ℕ) (hn0 : 2 ≤ n0)
    (hAt : 0 ≤ At) (hFr0 : 0 ≤ Fr) (hFr : Fr ≤ (St : ℝ) / 2 ^ 64) (hSt : 1 ≤ St) (hCt : 1 ≤ Ct) (hX1 : 1 ≤ X)
    (hX : (X : ℝ) ≤ (St : ℝ) * Ct / 2 ^ 64) (hpe : ((X : ℝ) / 2 ^ 64) ^ (-((n0 : ℝ)⁻¹)) ≤ (pe : ℝ) / 2 ^ 64)
    (hWt : (St : ℝ) * pe / 2 ^ 64 ≤ Wt) (hK1 : (Wt : ℝ) * ((n0 : ℝ) - 1) / n0 ≤ K1)
    (hK0 : (Wt : ℝ) * Ct / (n0 * 2 ^ 64) ≤ K0)
    (hT : |Tv - tev / 2 ^ 64| ≤ (tr : ℝ) / 2 ^ 64) (hA : |At - aev / 2 ^ 64| ≤ (ar : ℝ) / 2 ^ 64)
    (hlow : ((tr * one + K1 * ar : ℕ) : ℝ) < tev * 2 ^ 64 - K1 * aev - K0 * 2 ^ 64) :
    (Fr * At) ^ (1 - 1 / (n0 : ℝ)) ≤ Tv := by
  have hlow2 : ((tr : ℝ) * 2 ^ 64 + K1 * ar) < tev * 2 ^ 64 - K1 * aev - K0 * 2 ^ 64 := by
    have hone : ((one : ℕ) : ℝ) = 2 ^ 64 := by unfold one two64; norm_num
    have e : ((tr * one + K1 * ar : ℕ) : ℝ) = (tr : ℝ) * 2 ^ 64 + K1 * ar := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hone]
    exact lt_of_eq_of_lt e.symm hlow
  clear hlow
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ 64 := ⟨_, rfl⟩
  rw [← hK] at hFr hX hpe hWt hK0 hT hA hlow2
  have h64 : (0 : ℝ) < K := by rw [hK]; positivity
  clear hK
  have hn0r : (2 : ℝ) ≤ n0 := by exact_mod_cast hn0
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (n0 : ℝ)⁻¹ := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hε, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hp : 1 - 1 / (n0 : ℝ) = 1 - ε := by rw [hε, one_div]
  rw [hp]
  rw [← hε] at hpe
  have hStr : (0 : ℝ) < St := by exact_mod_cast (by omega : 0 < St)
  have hCtr : (0 : ℝ) < Ct := by exact_mod_cast (by omega : 0 < Ct)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  obtain ⟨σ, hσd⟩ : ∃ σ : ℝ, σ = (St : ℝ) / K := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = (Ct : ℝ) / K := ⟨_, rfl⟩
  have hσ : 0 < σ := by rw [hσd]; positivity
  have hC : 0 < C := by rw [hCd]; positivity
  rw [← hσd] at hFr
  rw [Real.mul_rpow hFr0 hAt]
  have hq0 : 0 ≤ 1 - ε := by linarith
  have hq1 : 1 - ε ≤ 1 := by linarith
  have s1 : Fr ^ (1 - ε) ≤ σ ^ (1 - ε) := Real.rpow_le_rpow hFr0 hFr hq0
  have s2 := amgm At C (1 - ε) hAt hC hq0 hq1
  -- σ^(1−ε) C^(−ε) ≤ Wt/K
  have s3 : σ ^ (1 - ε) * C ^ (1 - ε - 1) ≤ (Wt : ℝ) / K := by
    have e1 : σ ^ (1 - ε) = σ * σ ^ (-ε) := by
      rw [show (1 - ε) = 1 + -ε by ring, Real.rpow_add hσ, Real.rpow_one]
    have e2 : C ^ (1 - ε - 1) = C ^ (-ε) := by congr 1; ring
    rw [e1, e2, mul_assoc, ← Real.mul_rpow hσ.le hC.le]
    have hXs : (X : ℝ) / K ≤ σ * C := by
      rw [hσd, hCd, div_le_iff₀ h64]
      calc (X : ℝ) ≤ St * Ct / K := hX
        _ = St / K * (Ct / K) * K := by field_simp
    have hm : (σ * C) ^ (-ε) ≤ ((X : ℝ) / K) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hXs (by linarith)
    calc σ * (σ * C) ^ (-ε) ≤ σ * ((pe : ℝ) / K) := mul_le_mul_of_nonneg_left (le_trans hm hpe) hσ.le
      _ = (St : ℝ) * pe / K / K := by rw [hσd]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hWt h64.le
  have hW0 : (0 : ℝ) ≤ Wt := Nat.cast_nonneg _
  -- the bound by K1 At + K0
  have s4 : (Fr ^ (1 - ε)) * (At ^ (1 - ε)) ≤ (K1 : ℝ) / K * At + (K0 : ℝ) / K := by
    have hAp : 0 ≤ At ^ (1 - ε) := by positivity
    have hlin : 0 ≤ (1 - ε) * At + (1 - (1 - ε)) * C := by nlinarith
    have hCp : 0 ≤ C ^ (1 - ε - 1) := by positivity
    have hn0p : (0 : ℝ) < n0 := by linarith
    calc Fr ^ (1 - ε) * At ^ (1 - ε) ≤ σ ^ (1 - ε) * (C ^ (1 - ε - 1) * ((1 - ε) * At + (1 - (1 - ε)) * C)) :=
          mul_le_mul s1 s2 hAp (by positivity)
      _ = (σ ^ (1 - ε) * C ^ (1 - ε - 1)) * ((1 - ε) * At + (1 - (1 - ε)) * C) := by ring
      _ ≤ ((Wt : ℝ) / K) * ((1 - ε) * At + (1 - (1 - ε)) * C) := mul_le_mul_of_nonneg_right s3 hlin
      _ = ((Wt : ℝ) * ((n0 : ℝ) - 1) / n0) / K * At + ((Wt : ℝ) * Ct / (n0 * K)) / K := by
          rw [hCd, hε]; field_simp; ring
      _ ≤ _ := by
          have h1 : ((Wt : ℝ) * ((n0 : ℝ) - 1) / n0) / K * At ≤ (K1 : ℝ) / K * At :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK1 h64.le) hAt
          have h2 : ((Wt : ℝ) * Ct / (n0 * K)) / K ≤ (K0 : ℝ) / K := div_le_div_of_nonneg_right hK0 h64.le
          linarith
  -- the Taylor models
  have hT' := abs_le.1 hT
  have hA' := abs_le.1 hA
  have hK10 : (0 : ℝ) ≤ K1 := Nat.cast_nonneg _
  have hAup : (K1 : ℝ) / K * At ≤ (K1 : ℝ) / K * ((aev + ar) / K) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [add_div]; linarith [hA'.2]
  have hTlo : tev / K - (tr : ℝ) / K ≤ Tv := by linarith [hT'.1]
  have fin : (K1 : ℝ) / K * ((aev + ar) / K) + (K0 : ℝ) / K ≤ tev / K - (tr : ℝ) / K := by
    have e1 : (K1 : ℝ) / K * ((aev + ar) / K) + (K0 : ℝ) / K = ((K1 : ℝ) * (aev + ar) + K0 * K) / K / K := by
      field_simp
    have e2 : tev / K - (tr : ℝ) / K = (tev * K - tr * K) / K / K := by field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ h64.le
    apply div_le_div_of_nonneg_right _ h64.le
    linarith
  linarith

/-- the point of the cell with box coordinates `(s, u)`. -/
noncomputable def cx (M J : ℕ) (s : ℝ) : ℝ := (J : ℝ) / (M / 2 : ℕ) + (Rn (M / 2) : ℝ) / 2 ^ 80 * s / π


/-- **One option**: `optOK` certifies `(Π |f_i|)^p ≤ T` at the point. -/
theorem optOK_sound (C : Cfg) (hA : C.Aps = apsFrom C.O C.facs 0 (2 ^ C.l)) (hn0 : 2 ≤ C.n0)
    (hU2 : 2 * 2 ^ (64 * C.n0) ≤ C.U2 ^ C.n0) (hV : ∀ j < 256, 256 * 2 ^ (64 * C.n0) ≤ getV C.V j ^ C.n0 * (256 + j))
    (hfacs : ∀ f ∈ C.facs, 0 < f.2) (tab M J K : ℕ) (hM : 0 < M) (hM2 : 2 ∣ M) (hO : M ∣ C.O) (htab : TabGood M tab)
    (tT : TM) (info : List (Bool × Bool × ℕ × ℕ)) (mask : ℕ) (hopt : optOK C tab M J K tT info mask = true)
    (s u : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1) (Tv : ℝ) (hT : |Tv - tT.p.ev s u / 2 ^ 64| ≤ (tT.r : ℝ) / 2 ^ 64)
    (hR : List.Forall₂ FacR (C.facs.map (fun f => sumVal f.1 f.2 (cx M J s) (cx M K u))) info) :
    ((C.facs.map (fun f => sumVal f.1 f.2 (cx M J s) (cx M K u))).map abs).prod ^ (1 - 1 / (C.n0 : ℝ)) ≤ Tv := by
  generalize hvals : C.facs.map (fun f => sumVal f.1 f.2 (cx M J s) (cx M K u)) = vals at hR ⊢
  unfold optOK at hopt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hopt
  obtain ⟨⟨⟨hval, hdef⟩, hX1⟩, hlow⟩ := hopt
  -- the product sum
  have hS' : C.Aps.getD mask badS = prepS C.O (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2 := by
    rw [hA, apsFrom_getD]
    split_ifs with hm
    · simp
    · exfalso; rw [hA, apsFrom_getD, if_neg hm] at hval; exact Bool.noConfusion hval
  rw [hS'] at hval hlow hX1
  have hselpos : ∀ f ∈ selF mask 0 C.facs, 0 < f.2 := by
    intro f hf; rw [selF_eq] at hf; exact hfacs f (selV_mem _ _ _ _ hf)
  obtain ⟨_, hPSv⟩ := sumVal_prodL (selF mask 0 C.facs) hselpos (cx M J s) (cx M K u)
  have hAv : sumVal (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2 (cx M J s) (cx M K u) =
      (selV mask 0 vals).prod := by
    rw [hPSv, selF_eq, selV_map, hvals]
  have hTMA := tmS_sound C.O (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2 tab M J K hval hM hM2 hO
    htab s u hs hu
  simp only [] at hTMA
  have hTMA' : |(selV mask 0 vals).prod - (tmS (prepS C.O (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2) tab M J K).p.ev s u / 2 ^ 64| ≤
      ((tmS (prepS C.O (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2) tab M J K).r : ℝ) / 2 ^ 64 := by
    rw [← hAv]; exact hTMA
  generalize tmS (prepS C.O (prodL (selF mask 0 C.facs)).1 (prodL (selF mask 0 C.facs)).2) tab M J K = mA at hTMA' hlow hX1
  -- signs
  have hsgn := sgn_sel mask 0 vals info hR hdef
  have hAt0 : 0 ≤ (selV mask 0 (vals.map abs)).prod := selV_abs_nonneg _ _ _
  have hTa : |(selV mask 0 (vals.map abs)).prod - (if sgnProd mask 0 info = true then mA.p else mA.p.neg).ev s u / 2 ^ 64| ≤
      (mA.r : ℝ) / 2 ^ 64 := by
    rw [← hsgn]
    split_ifs
    · exact hTMA'
    · rw [Poly.neg_ev, neg_div, sub_neg_eq_add, show -(selV mask 0 vals).prod + mA.p.ev s u / 2 ^ 64 =
        -((selV mask 0 vals).prod - mA.p.ev s u / 2 ^ 64) by ring, abs_neg]; exact hTMA'
  generalize (if sgnProd mask 0 info = true then mA.p else mA.p.neg) = pa at hTa hlow hX1
  have hfr := frozen_le mask 0 vals info hR
  have hSt1 : supProd mask 0 info ≤ one := supProd_le mask 0 info (forall2_sup vals info hR)
  have hFr0 : 0 ≤ (selC mask 0 (vals.map abs)).prod := selC_abs_nonneg _ _ _
  rw [prod_split mask 0 (vals.map abs)]
  generalize (selV mask 0 (vals.map abs)).prod = At at hTa hAt0 ⊢
  generalize (selC mask 0 (vals.map abs)).prod = Fr at hfr hFr0 ⊢
  -- the constants
  generalize hCt : min one (max (Nat.sub pa.c0.p pa.c0.n) 1) = Ct at hlow hX1
  generalize hSt : supProd mask 0 info = St at hlow hX1 hfr hSt1
  generalize hX : St * Ct / one = X at hlow hX1
  generalize hpe : powInv C.U2 C.V X = pe at hlow
  generalize hWt : cdivN (St * pe) one = Wt at hlow
  generalize hK1 : cdivN (Wt * (C.n0 - 1)) C.n0 = K1 at hlow
  generalize hK0 : cdivN (Wt * Ct) (C.n0 * one) = K0 at hlow
  have hlow' := lowOK_sound _ _ hlow s u hs hu
  rw [combH_ev] at hlow'
  have hone0 : 0 < one := by unfold one two64; norm_num
  have hone : ((one : ℕ) : ℝ) = 2 ^ 64 := by unfold one two64; norm_num
  have hCt1 : 1 ≤ Ct := by rw [← hCt]; exact le_min (by unfold one two64; norm_num) (le_max_right _ _)
  have hCt2 : Ct ≤ one := by rw [← hCt]; exact min_le_left _ _
  have hXle : X ≤ 2 ^ 64 := by
    rw [← hX]; apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul hSt1 hCt2
    unfold one two64 at *; omega
  have hpe' := powInv_spec C.U2 C.V X C.n0 (by omega) hU2 hV hX1 hXle
  rw [hpe] at hpe'
  have hSt1' : 1 ≤ St := by
    by_contra hc; push Not at hc
    have : St = 0 := by omega
    rw [← hX, this] at hX1; simp at hX1
  have hXr : (X : ℝ) ≤ (St : ℝ) * Ct / 2 ^ 64 := by
    rw [← hX, ← hone]
    have := (Nat.cast_div_le (m := St * Ct) (n := one) (α := ℝ))
    push_cast at this; exact this
  have hWtr : (St : ℝ) * pe / 2 ^ 64 ≤ Wt := by
    rw [← hWt, ← hone]; unfold cdivN; have := (ceil_div_near (St * pe) one hone0).1; push_cast at this; exact this
  have hK1r : (Wt : ℝ) * ((C.n0 : ℝ) - 1) / C.n0 ≤ K1 := by
    rw [← hK1]; unfold cdivN
    have := (ceil_div_near (Wt * (C.n0 - 1)) C.n0 (by omega)).1
    rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this; push_cast at this; exact this
  have hK0r : (Wt : ℝ) * Ct / (C.n0 * 2 ^ 64) ≤ K0 := by
    rw [← hK0, ← hone]; unfold cdivN
    have := (ceil_div_near (Wt * Ct) (C.n0 * one) (by positivity)).1; push_cast at this; exact this
  have hfr' : Fr ≤ (St : ℝ) / 2 ^ 64 := hfr
  exact opt_core Tv At Fr (tT.p.ev s u) (pa.ev s u) tT.r mA.r St Ct X pe Wt K1 K0 C.n0 hn0 hAt0 hFr0 hfr' hSt1' hCt1 hX1
    hXr hpe' hWtr hK1r hK0r hT hTa hlow'


/-! ## Cells -/

theorem tryOpts_sound (C : Cfg) (tab M J K : ℕ) (tT : TM) (info : List (Bool × Bool × ℕ × ℕ)) (thr : List ℕ) (prev : ℕ)
    (h : tryOpts C tab M J K tT info thr prev = true) : ∃ mask, optOK C tab M J K tT info mask = true := by
  induction thr generalizing prev with
  | nil => simp [tryOpts] at h
  | cons θ rest ih =>
    simp only [tryOpts, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨_, h⟩ | h
    · exact ⟨_, h⟩
    · exact ih _ h

/-- the hypotheses on a configuration. -/
structure CfgOK (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) : Prop where
  hT : C.T = prepS C.O Tts TDn
  hfP : C.facP = C.facs.map (fun f => prepS C.O f.1 f.2)
  hA : C.Aps = apsFrom C.O C.facs 0 (2 ^ C.l)
  hn0 : 2 ≤ C.n0
  hU2 : 2 * 2 ^ (64 * C.n0) ≤ C.U2 ^ C.n0
  hV : ∀ j < 256, 256 * 2 ^ (64 * C.n0) ≤ getV C.V j ^ C.n0 * (256 + j)
  hfacs : ∀ f ∈ C.facs, 0 < f.2
  hfac1 : ∀ f ∈ C.facs, ∀ x y : ℝ, |sumVal f.1 f.2 x y| ≤ 1
  hQ0 : 0 < C.Q0
  htab : ∀ d ≤ C.dmax, TabGood (4 * C.Q0 * 2 ^ d) (C.tab d)
  hO : ∀ d ≤ C.dmax, 4 * C.Q0 * 2 ^ d ∣ C.O

theorem pi_lt_hi : π < (piHiN : ℝ) / piD := by
  have := Real.pi_lt_d20; unfold piHiN piD; norm_num at this ⊢; linarith

theorem Rn_ge (N : ℕ) (hN : 0 < N) : π / N ≤ (Rn N : ℝ) / 2 ^ 80 := by
  unfold Rn
  have hd : 0 < piD * N := by unfold piD; positivity
  have hc := (ceil_div_near (piHiN * 2 ^ RB) (piD * N) hd).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := pi_lt_hi
  rw [le_div_iff₀ (by positivity)]
  refine le_trans ?_ hc
  have hD : (0 : ℝ) < piD := by unfold piD; norm_num
  have e : ((piHiN * 2 ^ RB : ℕ) : ℝ) / ((piD * N : ℕ) : ℝ) = ((piHiN : ℝ) / piD) / N * 2 ^ RB := by
    push_cast; field_simp
  rw [e]
  unfold RB
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_right hpi.le hN'.le

theorem forall2_map {α : Type} (L : List α) (f : α → ℝ) (g : α → Bool × Bool × ℕ × ℕ) (h : ∀ a ∈ L, FacR (f a) (g a)) :
    List.Forall₂ FacR (L.map f) (L.map g) := by
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L ih => exact List.Forall₂.cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- **Cell soundness.** -/
theorem cellOK_sound (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (hC : CfgOK C Tts TDn) (d J K : ℕ) (hd : d ≤ C.dmax)
    (h : cellOK C d J K = true) (x y : ℝ) (hx : |x - J / (2 * C.Q0 * 2 ^ d : ℕ)| ≤ 1 / (2 * C.Q0 * 2 ^ d : ℕ))
    (hy : |y - K / (2 * C.Q0 * 2 ^ d : ℕ)| ≤ 1 / (2 * C.Q0 * 2 ^ d : ℕ)) :
    ((C.facs.map (fun f => |sumVal f.1 f.2 x y|)).prod) ^ (1 - 1 / (C.n0 : ℝ)) ≤ sumVal Tts TDn x y := by
  unfold cellOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨_, hTv⟩, hFv⟩, hopt⟩ := h
  set M := 4 * C.Q0 * 2 ^ d with hM
  have hM0 : 0 < M := by have := hC.hQ0; positivity
  have hM2 : 2 ∣ M := ⟨2 * C.Q0 * 2 ^ d, by rw [hM]; ring⟩
  have hN : M / 2 = 2 * C.Q0 * 2 ^ d := by rw [hM]; exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  have hN0 : 0 < 2 * C.Q0 * 2 ^ d := by have := hC.hQ0; positivity
  have htab := hC.htab d hd
  have hO := hC.hO d hd
  -- box coordinates
  set r : ℝ := (Rn (M / 2) : ℝ) / 2 ^ 80 with hr
  have hrpos : π / (2 * C.Q0 * 2 ^ d : ℕ) ≤ r := by rw [hr, hN]; exact Rn_ge _ hN0
  have hr0 : 0 < r := lt_of_lt_of_le (by have : (0 : ℝ) < (2 * C.Q0 * 2 ^ d : ℕ) := by exact_mod_cast hN0
                                         positivity) hrpos
  set s := π * (x - J / (2 * C.Q0 * 2 ^ d : ℕ)) / r with hs
  set u := π * (y - K / (2 * C.Q0 * 2 ^ d : ℕ)) / r with hu
  have hNr : (0 : ℝ) < (2 * C.Q0 * 2 ^ d : ℕ) := by exact_mod_cast hN0
  have hbox : ∀ z c : ℝ, |z - c| ≤ 1 / (2 * C.Q0 * 2 ^ d : ℕ) → |π * (z - c) / r| ≤ 1 := by
    intro z c hz
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hr0, div_le_one hr0]
    calc π * |z - c| ≤ π * (1 / (2 * C.Q0 * 2 ^ d : ℕ)) := mul_le_mul_of_nonneg_left hz Real.pi_pos.le
      _ = π / (2 * C.Q0 * 2 ^ d : ℕ) := by ring
      _ ≤ r := hrpos
  have hs1 : |s| ≤ 1 := hbox _ _ hx
  have hu1 : |u| ≤ 1 := hbox _ _ hy
  have hxs : cx M J s = x := by
    unfold cx; rw [← hr, hN, hs]; field_simp; ring
  have hyu : cx M K u = y := by
    unfold cx; rw [← hr, hN, hu]; field_simp; ring
  -- the T model
  have hTM := tmS_sound C.O Tts TDn (C.tab d) M J K (by rw [← hC.hT]; exact hTv) hM0 hM2 hO htab s u hs1 hu1
  rw [← hC.hT] at hTM
  simp only [] at hTM
  -- the factors
  have hR : List.Forall₂ FacR (C.facs.map (fun f => sumVal f.1 f.2 (cx M J s) (cx M K u)))
      (C.facP.map (fun S => facInfo (tmS S (C.tab d) M J K))) := by
    rw [hC.hfP, List.map_map]
    apply forall2_map
    intro f hf
    have hv : (prepS C.O f.1 f.2).valid = true := by
      apply hFv; rw [hC.hfP]; exact List.mem_map.2 ⟨f, hf, rfl⟩
    have hTMf := tmS_sound C.O f.1 f.2 (C.tab d) M J K hv hM0 hM2 hO htab s u hs1 hu1
    simp only [] at hTMf
    apply facInfo_sound _ _ s u hs1 hu1 hTMf
    exact hC.hfac1 f hf _ _
  obtain ⟨mask, hm⟩ := tryOpts_sound C _ M J K _ _ _ _ hopt
  have := optOK_sound C hC.hA hC.hn0 hC.hU2 hC.hV hC.hfacs (C.tab d) M J K hM0 hM2 hO htab _ _ mask hm s u hs1 hu1
    (sumVal Tts TDn x y) (by rw [← hxs, ← hyu]; exact hTM) hR
  rw [hxs, hyu, List.map_map] at this
  exact this


/-- the inequality certified at a point. -/
def Good (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (x y : ℝ) : Prop :=
  ((C.facs.map (fun f => |sumVal f.1 f.2 x y|)).prod) ^ (1 - 1 / (C.n0 : ℝ)) ≤ sumVal Tts TDn x y

theorem child_choice (J : ℕ) (hJ : 1 ≤ J) (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : |x - J / N| ≤ 1 / N) :
    |x - ((2 * J - 1 : ℕ) : ℝ) / (2 * N : ℕ)| ≤ 1 / (2 * N : ℕ) ∨ |x - ((2 * J + 1 : ℕ) : ℝ) / (2 * N : ℕ)| ≤ 1 / (2 * N : ℕ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ((2 * J - 1 : ℕ) : ℝ) = 2 * J - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1]
  push_cast
  rw [abs_le] at hx
  rcases le_total x (J / N) with h | h
  · left
    rw [abs_le]; constructor
    · have : (2 * (J : ℝ) - 1) / (2 * N) - 1 / (2 * N) = J / N - 1 / N := by field_simp; ring
      linarith [hx.1]
    · have : (2 * (J : ℝ) - 1) / (2 * N) + 1 / (2 * N) = J / N := by field_simp; ring
      linarith
  · right
    rw [abs_le]; constructor
    · have : (2 * (J : ℝ) + 1) / (2 * N) - 1 / (2 * N) = J / N := by field_simp; ring
      linarith
    · have : (2 * (J : ℝ) + 1) / (2 * N) + 1 / (2 * N) = J / N + 1 / N := by field_simp; ring
      linarith [hx.2]

theorem checkRec_sound (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (hC : CfgOK C Tts TDn) :
    ∀ f d J K : ℕ, d + f ≤ C.dmax → 1 ≤ J → 1 ≤ K → checkRec C f d J K = true → ∀ x y : ℝ,
      |x - J / (2 * C.Q0 * 2 ^ d : ℕ)| ≤ 1 / (2 * C.Q0 * 2 ^ d : ℕ) →
      |y - K / (2 * C.Q0 * 2 ^ d : ℕ)| ≤ 1 / (2 * C.Q0 * 2 ^ d : ℕ) → Good C Tts TDn x y := by
  intro f
  induction f with
  | zero =>
    intro d J K hd _ _ h x y hx hy
    exact cellOK_sound C Tts TDn hC d J K (by omega) h x y hx hy
  | succ f ih =>
    intro d J K hd hJ hK h x y hx hy
    simp only [checkRec, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact cellOK_sound C Tts TDn hC d J K (by omega) h x y hx hy
    · have hN : 0 < 2 * C.Q0 * 2 ^ d := by have := hC.hQ0; positivity
      have e : 2 * C.Q0 * 2 ^ (d + 1) = 2 * (2 * C.Q0 * 2 ^ d) := by ring
      have cx := child_choice J hJ _ hN x hx
      have cy := child_choice K hK _ hN y hy
      rw [← e] at cx cy
      have hd' : d + 1 + f ≤ C.dmax := by omega
      rcases cx with cx | cx <;> rcases cy with cy | cy
      · exact ih (d + 1) _ _ hd' (by omega) (by omega) h1 x y cx cy
      · exact ih (d + 1) _ _ hd' (by omega) (by omega) h3 x y cx cy
      · exact ih (d + 1) _ _ hd' (by omega) (by omega) h2 x y cx cy
      · exact ih (d + 1) _ _ hd' (by omega) (by omega) h4 x y cx cy

/-- **All listed level-0 cells.** -/
theorem checkList_sound (C : Cfg) (Tts : List (ℤ × ℤ × ℕ)) (TDn : ℕ) (hC : CfgOK C Tts TDn) (L : List (ℕ × ℕ))
    (h : checkList C L = true) (jk : ℕ × ℕ) (hjk : jk ∈ L) (x y : ℝ)
    (hx : (jk.1 : ℝ) / C.Q0 ≤ x ∧ x ≤ (jk.1 + 1 : ℝ) / C.Q0) (hy : (jk.2 : ℝ) / C.Q0 ≤ y ∧ y ≤ (jk.2 + 1 : ℝ) / C.Q0) :
    Good C Tts TDn x y := by
  unfold checkList at h
  rw [List.all_eq_true] at h
  have h1 := h jk hjk
  have hQ : (0 : ℝ) < C.Q0 := by exact_mod_cast hC.hQ0
  have conv : ∀ (j : ℕ) (z : ℝ), (j : ℝ) / C.Q0 ≤ z ∧ z ≤ (j + 1 : ℝ) / C.Q0 →
      |z - ((2 * j + 1 : ℕ) : ℝ) / (2 * C.Q0 * 2 ^ 0 : ℕ)| ≤ 1 / (2 * C.Q0 * 2 ^ 0 : ℕ) := by
    intro j z hz
    push_cast
    simp only [pow_zero, mul_one]
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hz
    constructor
    · have : (2 * (j : ℝ) + 1) / (2 * C.Q0) - 1 / (2 * C.Q0) = j / C.Q0 := by field_simp; ring
      linarith
    · have : (2 * (j : ℝ) + 1) / (2 * C.Q0) + 1 / (2 * C.Q0) = (j + 1) / C.Q0 := by field_simp; ring
      linarith
  exact checkRec_sound C Tts TDn hC C.dmax 0 _ _ (by omega) (by omega) (by omega) h1 x y (conv _ _ hx) (conv _ _ hy)

end Palprimes.M2
