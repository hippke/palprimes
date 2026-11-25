import Omega3.Items.S10_Box

/-!
# S10 helpers, part 7: the `c_η` bound (K enclosures by monotone Riemann sums, quadratic form)
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

def kfl (N1 N2 : ℕ) : ℕ := (TP * min (N1 * N2) ((QN - N1) * (QN - N2))) / (N1 * N2)
def kcl (N1 N2 : ℕ) : ℕ := (TP * min (N1 * N2) ((QN - N1) * (QN - N2)) + N1 * N2 - 1) / (N1 * N2)

def KloN (c' c : Cell) : ℕ := (c'.B - c'.A) * (c.B - c.A) *
  ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS, kfl (c'.A * NS + (i + 1) * (c'.B - c'.A)) (c.A * NS + (j + 1) * (c.B - c.A))
def KhiN (c' c : Cell) : ℕ := (c'.B - c'.A) * (c.B - c.A) *
  ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS, kcl (c'.A * NS + i * (c'.B - c'.A)) (c.A * NS + j * (c.B - c.A))

/-- The real `K(c', c) = ∫_{c'} ∫_{c} k`. -/
noncomputable def KR (c' c : Cell) : ℝ := ∫ u in (rc c').1..(rc c').2.1, PhiK (rc c).1 (rc c).2.1 u

lemma QN_eq : (QN : ℝ) = Qn * NS := by simp [QN]
lemma NS_pos : (0 : ℝ) < NS := by norm_num [NS]

lemma kk_grid (N1 N2 : ℕ) (h1 : 0 < N1) (h2 : 0 < N2) (h1' : N1 ≤ QN) (h2' : N2 ≤ QN) :
    (kfl N1 N2 : ℝ) ≤ TP * kk ((N1 : ℝ) / QN) ((N2 : ℝ) / QN) ∧
    TP * kk ((N1 : ℝ) / QN) ((N2 : ℝ) / QN) ≤ kcl N1 N2 := by
  have hQN : (0 : ℝ) < QN := by norm_num [QN, Qn, NS]
  have hN1 : (0 : ℝ) < N1 := by exact_mod_cast h1
  have hN2 : (0 : ℝ) < N2 := by exact_mod_cast h2
  have hp : 0 < N1 * N2 := Nat.mul_pos h1 h2
  have hpR : (0 : ℝ) < ((N1 * N2 : ℕ) : ℝ) := by exact_mod_cast hp
  have hkk : TP * kk ((N1 : ℝ) / QN) ((N2 : ℝ) / QN) =
      ((TP * min (N1 * N2) ((QN - N1) * (QN - N2)) : ℕ) : ℝ) / ((N1 * N2 : ℕ) : ℝ) := by
    unfold kk
    push_cast [Nat.cast_sub h1', Nat.cast_sub h2']
    have hpR' : (0 : ℝ) < (N1 : ℝ) * N2 := by positivity
    rw [mul_div_assoc, ← min_div_div_right hpR'.le]
    congr 2
    · field_simp
    · field_simp
  rw [hkk]
  exact ⟨ndiv_le _ _, by
    have := cdiv_ge (TP * min (N1 * N2) ((QN - N1) * (QN - N2))) (N1 * N2) hp
    simpa [kcl] using this⟩

theorem K_bounds (A0 : ℕ) (c' c : Cell) (hc' : CellOK A0 c') (hc : CellOK A0 c) :
    (KloN c' c : ℝ) ≤ (QN : ℝ) ^ 2 * TP * KR c' c ∧ (QN : ℝ) ^ 2 * TP * KR c' c ≤ KhiN c' c := by
  obtain ⟨_, hA0', hAB', hBQ', _, _⟩ := hc'
  obtain ⟨_, hA0, hAB, hBQ, _, _⟩ := hc
  have hQ := Qn_pos
  have hT := TP_pos
  have hNS := NS_pos
  have hQN : (QN : ℝ) = Qn * NS := QN_eq
  have hNSn : 0 < NS := by norm_num [NS]
  set a' : ℝ := (c'.A : ℝ) / Qn
  set b' : ℝ := (c'.B : ℝ) / Qn
  set a : ℝ := (c.A : ℝ) / Qn
  set b : ℝ := (c.B : ℝ) / Qn
  have ha' : 0 < a' := div_pos (by exact_mod_cast hA0') hQ
  have hab' : a' ≤ b' := div_le_div_of_nonneg_right (by exact_mod_cast hAB'.le) hQ.le
  have hb' : b' ≤ 1 := by rw [div_le_one hQ]; exact_mod_cast hBQ'
  have ha : 0 < a := div_pos (by exact_mod_cast hA0) hQ
  have hab : a ≤ b := div_le_div_of_nonneg_right (by exact_mod_cast hAB.le) hQ.le
  have hb : b ≤ 1 := by rw [div_le_one hQ]; exact_mod_cast hBQ
  -- grid points
  have gp : ∀ (A B : ℕ) (k : ℕ), A ≤ B → ((A : ℝ) / Qn + ((B : ℝ) / Qn - (A : ℝ) / Qn) * k / NS) =
      (((A * NS + k * (B - A) : ℕ) : ℝ)) / QN := by
    intro A B k hAB; rw [hQN]; push_cast [Nat.cast_sub hAB]; field_simp
  have gpos : ∀ (A B k : ℕ), 0 < A → 0 < A * NS + k * (B - A) := fun A B k hA => by positivity
  have gle : ∀ (A B k : ℕ), A ≤ B → B ≤ Qn → k ≤ NS → A * NS + k * (B - A) ≤ QN := by
    intro A B k hAB hB hk
    have : k * (B - A) ≤ NS * (B - A) := Nat.mul_le_mul_right _ hk
    have : A * NS + NS * (B - A) = B * NS := by
      have := Nat.sub_add_cancel hAB; nlinarith
    calc A * NS + k * (B - A) ≤ B * NS := by omega
      _ ≤ Qn * NS := Nat.mul_le_mul_right _ hB
      _ = QN := rfl
  have hw : ∀ (A B : ℕ), A ≤ B → ((B : ℝ) / Qn - (A : ℝ) / Qn) / NS = ((B - A : ℕ) : ℝ) / QN := by
    intro A B hAB; rw [hQN]; push_cast [Nat.cast_sub hAB]; field_simp
  have hanti : AntitoneOn (PhiK a b) (Icc a' b') :=
    (PhiK_anti ha hab hb).mono (fun x hx => lt_of_lt_of_le ha' hx.1)
  obtain ⟨R1, R2⟩ := anti_riemann hNSn hab' hanti
  -- inner bounds at a grid point x
  have inner : ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∑ j ∈ Finset.range NS, (b - a) / NS * kk x (a + (b - a) * (j + 1) / NS) ≤ PhiK a b x ∧
      PhiK a b x ≤ ∑ j ∈ Finset.range NS, (b - a) / NS * kk x (a + (b - a) * j / NS) := by
    intro x hx hx1
    have hk : AntitoneOn (kk x) (Icc a b) := by
      intro y hy z hz hyz
      exact kk_anti2 (lt_of_lt_of_le ha hy.1) hyz hx hx1
    exact anti_riemann hNSn hab hk
  have hxin : ∀ k : ℕ, k ≤ NS → 0 < a' + (b' - a') * k / NS ∧ a' + (b' - a') * k / NS ≤ 1 := by
    intro k hk
    have hkR : (k : ℝ) ≤ NS := by exact_mod_cast hk
    have h0 : 0 ≤ (b' - a') * k / NS := by positivity
    have h1 : (b' - a') * k / NS ≤ b' - a' := by
      rw [div_le_iff₀ hNS]; nlinarith
    constructor <;> linarith
  simp only [KR, rc]
  set w' : ℝ := ((c'.B - c'.A : ℕ) : ℝ) / QN
  set w : ℝ := ((c.B - c.A : ℕ) : ℝ) / QN
  have hw' : (b' - a') / NS = w' := hw c'.A c'.B hAB'.le
  have hw0 : (b - a) / NS = w := hw c.A c.B hAB.le
  set X' : ℕ → ℝ := fun k => (((c'.A * NS + k * (c'.B - c'.A) : ℕ) : ℝ)) / QN
  set X : ℕ → ℝ := fun k => (((c.A * NS + k * (c.B - c.A) : ℕ) : ℝ)) / QN
  have hX' : ∀ k : ℕ, a' + (b' - a') * k / NS = X' k := fun k => gp c'.A c'.B k hAB'.le
  have hX : ∀ k : ℕ, a + (b - a) * k / NS = X k := fun k => gp c.A c.B k hAB.le
  have hX'1 : ∀ k : ℕ, a' + (b' - a') * (k + 1) / NS = X' (k + 1) := fun k => by rw [← hX']; push_cast; ring
  have hX1 : ∀ k : ℕ, a + (b - a) * (k + 1) / NS = X (k + 1) := fun k => by rw [← hX]; push_cast; ring
  simp only [hw', hw0, hX'1, hX1, hX', hX] at R1 R2 inner
  have hxin' : ∀ k : ℕ, k ≤ NS → 0 < X' k ∧ X' k ≤ 1 := fun k hk => by rw [← hX']; exact hxin k hk
  have hQN2 : (QN : ℝ) ^ 2 * w' * w = ((c'.B - c'.A : ℕ) : ℝ) * ((c.B - c.A : ℕ) : ℝ) := by
    simp only [w', w]; have : (0 : ℝ) < QN := by norm_num [QN, Qn, NS]
    field_simp
  have hS0 : (0 : ℝ) ≤ (QN : ℝ) ^ 2 * TP := by positivity
  have hw'0 : 0 ≤ w' := by positivity
  constructor
  · calc (KloN c' c : ℝ) = ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS,
          ((c'.B - c'.A : ℕ) : ℝ) * ((c.B - c.A : ℕ) : ℝ) * (kfl (c'.A * NS + (i + 1) * (c'.B - c'.A)) (c.A * NS + (j + 1) * (c.B - c.A)) : ℝ) := by
          simp only [KloN]; push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS, (QN : ℝ) ^ 2 * TP * (w' * (w * kk (X' (i + 1)) (X (j + 1)))) := by
          apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro j hj
          have hi' : i + 1 ≤ NS := Finset.mem_range.mp hi
          have hj' : j + 1 ≤ NS := Finset.mem_range.mp hj
          have hk := (kk_grid _ _ (gpos c'.A c'.B (i + 1) hA0') (gpos c.A c.B (j + 1) hA0)
            (gle c'.A c'.B (i + 1) hAB'.le hBQ' hi') (gle c.A c.B (j + 1) hAB.le hBQ hj')).1
          have e : (QN : ℝ) ^ 2 * TP * (w' * (w * kk (X' (i + 1)) (X (j + 1)))) =
              ((c'.B - c'.A : ℕ) : ℝ) * ((c.B - c.A : ℕ) : ℝ) * (TP * kk (X' (i + 1)) (X (j + 1))) := by
            rw [← hQN2]; ring
          rw [e]; exact mul_le_mul_of_nonneg_left hk (by positivity)
      _ = (QN : ℝ) ^ 2 * TP * ∑ i ∈ Finset.range NS, w' * ∑ j ∈ Finset.range NS, w * kk (X' (i + 1)) (X (j + 1)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (QN : ℝ) ^ 2 * TP * ∑ i ∈ Finset.range NS, w' * PhiK a b (X' (i + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hS0
          apply Finset.sum_le_sum; intro i hi
          have hi' : i + 1 ≤ NS := Finset.mem_range.mp hi
          obtain ⟨x0, x1⟩ := hxin' (i + 1) hi'
          exact mul_le_mul_of_nonneg_left (inner _ x0 x1).1 hw'0
      _ ≤ _ := mul_le_mul_of_nonneg_left R1 hS0
  · calc (QN : ℝ) ^ 2 * TP * ∫ u in a'..b', PhiK a b u ≤ (QN : ℝ) ^ 2 * TP * ∑ i ∈ Finset.range NS, w' * PhiK a b (X' i) :=
          mul_le_mul_of_nonneg_left R2 hS0
      _ ≤ (QN : ℝ) ^ 2 * TP * ∑ i ∈ Finset.range NS, w' * ∑ j ∈ Finset.range NS, w * kk (X' i) (X j) := by
          apply mul_le_mul_of_nonneg_left _ hS0
          apply Finset.sum_le_sum; intro i hi
          have hi' : i ≤ NS := (Finset.mem_range.mp hi).le
          obtain ⟨x0, x1⟩ := hxin' i hi'
          exact mul_le_mul_of_nonneg_left (inner _ x0 x1).2 hw'0
      _ = ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS, (QN : ℝ) ^ 2 * TP * (w' * (w * kk (X' i) (X j))) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range NS, ∑ j ∈ Finset.range NS,
          ((c'.B - c'.A : ℕ) : ℝ) * ((c.B - c.A : ℕ) : ℝ) * (kcl (c'.A * NS + i * (c'.B - c'.A)) (c.A * NS + j * (c.B - c.A)) : ℝ) := by
          apply Finset.sum_le_sum; intro i hi; apply Finset.sum_le_sum; intro j hj
          have hi' : i ≤ NS := (Finset.mem_range.mp hi).le
          have hj' : j ≤ NS := (Finset.mem_range.mp hj).le
          have hk := (kk_grid _ _ (gpos c'.A c'.B i hA0') (gpos c.A c.B j hA0)
            (gle c'.A c'.B i hAB'.le hBQ' hi') (gle c.A c.B j hAB.le hBQ hj')).2
          have e : (QN : ℝ) ^ 2 * TP * (w' * (w * kk (X' i) (X j))) =
              ((c'.B - c'.A : ℕ) : ℝ) * ((c.B - c.A : ℕ) : ℝ) * (TP * kk (X' i) (X j)) := by
            rw [← hQN2]; ring
          rw [e]; exact mul_le_mul_of_nonneg_left hk (by positivity)
      _ = (KhiN c' c : ℝ) := by
          simp only [KhiN]; push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]


/-! ## The quadratic form -/

def dsum (cs : List Cell) : ℕ := (cs.map (fun c => c.m.natAbs ^ 2 * phiHi Qn 0 c * (Qn * NS ^ 2))).sum
def khs (cs : List Cell) : ℕ :=
  (cs.map (fun c' => (cs.map (fun c => if c'.m * c.m < 0 then (c'.m * c.m).natAbs * KhiN c' c else 0)).sum)).sum
def kls (cs : List Cell) : ℕ :=
  (cs.map (fun c' => (cs.map (fun c => if 0 < c'.m * c.m then (c'.m * c.m).natAbs * KloN c' c else 0)).sum)).sum
def costOK (cs : List Cell) (cn : ℕ) : Bool :=
  decide (1000000 * (dsum cs + khs cs) ≤ cn * (En ^ 2 * QN ^ 2 * TP) + 1000000 * kls cs)

lemma lsum_le {ι : Type*} (L : List ι) (f g : ι → ℝ) (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma lsum_cast {ι : Type*} (L : List ι) (f : ι → ℕ) : (((L.map f).sum : ℕ) : ℝ) = (L.map (fun x => (f x : ℝ))).sum := by
  rw [Nat.cast_list_sum, List.map_map]; rfl

lemma lsum_div {ι : Type*} (L : List ι) (f : ι → ℝ) (d : ℝ) : (L.map f).sum / d = (L.map (fun x => f x / d)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, add_div, ih]

lemma lsum_mul {ι : Type*} (L : List ι) (f : ι → ℝ) (a : ℝ) : a * (L.map f).sum = (L.map (fun x => a * f x)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

lemma lsum_sub {ι : Type*} (L : List ι) (f g : ι → ℝ) : (L.map f).sum - (L.map g).sum = (L.map (fun x => f x - g x)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

lemma natAbs_sq_R (m : ℤ) : ((m.natAbs ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by
  push_cast; rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

lemma natAbs_R (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

theorem cEta_bound (A0 : ℕ) (cs : List Cell) (hcs : ∀ c ∈ cs, CellOK A0 c) (cn : ℕ) (hc : costOK cs cn = true) :
    1 + (cs.map (fun c => (rc c).2.2 ^ 2 * phiC (rc c).1 (rc c).2.1 1)).sum -
      (cs.map (fun c' => (rc c').2.2 * (cs.map (fun c => (rc c).2.2 * KR c' c)).sum)).sum ≤ 1 + (cn : ℝ) / 1000000 := by
  simp only [costOK, decide_eq_true_eq] at hc
  have hQ := Qn_pos
  have hT := TP_pos
  have hE := En_pos
  have hQN : (QN : ℝ) = Qn * NS := QN_eq
  have hNS := NS_pos
  set sc : ℝ := (En : ℝ) ^ 2 * (QN : ℝ) ^ 2 * TP
  have hQNp : (0 : ℝ) < QN := by norm_num [QN, Qn, NS]
  have hsc : 0 < sc := by positivity
  have hcR : (1000000 : ℝ) * ((dsum cs : ℝ) + khs cs) ≤ cn * sc + 1000000 * kls cs := by
    have := (Nat.cast_le (α := ℝ)).mpr hc; push_cast at this; simpa [sc] using this
  -- (1) diagonal
  have h1 : (cs.map (fun c => (rc c).2.2 ^ 2 * phiC (rc c).1 (rc c).2.1 1)).sum ≤ (dsum cs : ℝ) / sc := by
    rw [dsum, lsum_cast, lsum_div]
    apply lsum_le
    intro c hcm
    obtain ⟨_, p2⟩ := phi_ok A0 c (hcs c hcm) Qn 0 0 (by norm_num [Qn]) (fun _ => LogOK_Q)
    rw [div_self hQ.ne'] at p2
    have hnn := phi_nonneg_c A0 c (hcs c hcm) 1 one_pos
    simp only [rc] at p2 hnn ⊢
    rw [Nat.cast_mul, Nat.cast_mul, natAbs_sq_R]
    push_cast
    rw [le_div_iff₀ hsc]
    simp only [sc]; rw [hQN]
    have e : ((c.m : ℝ) / En) ^ 2 * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1 * ((En : ℝ) ^ 2 * (Qn * NS) ^ 2 * TP) =
        (c.m : ℝ) ^ 2 * (Qn * NS ^ 2) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1) := by
      field_simp
    rw [e]
    have : (0 : ℝ) ≤ (c.m : ℝ) ^ 2 * (Qn * NS ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left p2 this]
  -- (2) off-diagonal
  have h2 : ((kls cs : ℝ) - khs cs) / sc ≤
      (cs.map (fun c' => (rc c').2.2 * (cs.map (fun c => (rc c).2.2 * KR c' c)).sum)).sum := by
    rw [kls, khs, lsum_cast, lsum_cast, lsum_sub, lsum_div]
    apply lsum_le
    intro c' hc'
    rw [lsum_cast, lsum_cast, lsum_sub, lsum_div, lsum_mul]
    apply lsum_le
    intro c hcm
    obtain ⟨k1, k2⟩ := K_bounds A0 c' c (hcs c' hc') (hcs c hcm)
    simp only [rc]
    rw [div_le_iff₀ hsc]
    have e : (c'.m : ℝ) / En * ((c.m : ℝ) / En * KR c' c) * sc = ((c'.m * c.m : ℤ) : ℝ) * ((QN : ℝ) ^ 2 * TP * KR c' c) := by
      simp only [sc]; push_cast; field_simp
    rw [e]
    rcases lt_trichotomy (c'.m * c.m) 0 with hm | hm | hm
    · rw [if_neg (not_lt.mpr hm.le), if_pos hm]
      have hmR : ((c'.m * c.m : ℤ) : ℝ) < 0 := by exact_mod_cast hm
      rw [Nat.cast_zero, Nat.cast_mul, natAbs_R, abs_of_neg hmR]
      have := mul_le_mul_of_nonpos_left k2 hmR.le
      linarith
    · simp [hm]
    · rw [if_pos hm, if_neg (not_lt.mpr hm.le)]
      have hmR : (0 : ℝ) < ((c'.m * c.m : ℤ) : ℝ) := by exact_mod_cast hm
      rw [Nat.cast_zero, Nat.cast_mul, natAbs_R, abs_of_pos hmR]
      have := mul_le_mul_of_nonneg_left k1 hmR.le
      linarith
  have h3 : (dsum cs : ℝ) / sc - ((kls cs : ℝ) - khs cs) / sc ≤ (cn : ℝ) / 1000000 := by
    rw [← sub_div, div_le_div_iff₀ hsc (by norm_num)]
    linarith
  linarith

end S10
end Omega3
