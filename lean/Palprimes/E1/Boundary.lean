import Palprimes.MainTerm.E1

/-! # E1, Part A: the boundary identity for the Rosser sums (blueprint A.1–A.6)

For a density `g` and a list `l` put `V_l = Π_{q∈l} (1 − g q)` (`Vl`). The depth-graded boundary sums
`Bp g k z l` (chains of `2k+1` primes, the last one fails the upper Rosser condition) and `Bm g k z l`
(chains of `2k` primes, `Bm g 0 = 0`) satisfy (A.2)
`Sg g true z l = V_l + Σ_k Bp g k z l`, `Sg g false z l = V_l − Σ_k Bm g k z l`.

On the primes below `w` (`BP b k D w`, `BM b k D w` for the density `gB b`):
* signs and the crude bound `0 ≤ B ≤ Π_{p<w} (1 + g p)` (A.3);
* the unrolled form (A.4) `B⁺_0(D,w) = Σ_{p<w, D<p³} g(p)V(p)`,
  `B⁺_{k+1}(D,w) = Σ_{p<w, p³≤D} g(p) B⁻_{k+1}(D/p,p)`, `B⁻_{k+1}(D,w) = Σ_{p<w} g(p) B⁺_k(D/p,p)`;
* vanishing (A.5): `B⁺_k = 0` if `w^{2k+3} ≤ D`, `B⁻_k = 0` if `w^{2k+2} ≤ D`, and by list length;
* no chains below `W₀` (A.6).

Convention: the upper condition is `headOK true z P ↔ P³ ≤ z` (with `≤`), as in `Sg`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

section Generic

variable (g : ℕ → ℝ)

/-- `V_l = Π_{q ∈ l} (1 − g q)`. -/
noncomputable def Vl (l : List ℕ) : ℝ := (l.map (fun q => 1 - g q)).prod

/-- Both boundary sums in one recursion (`true`: `Bp`, `false`: `Bm`). -/
noncomputable def Bd : Bool → ℕ → ℝ → List ℕ → ℝ
  | _, _, _, [] => 0
  | true, 0, z, P :: l => Bd true 0 z l + g P * (if z < (P : ℝ) ^ 3 then Vl g l else 0)
  | true, k + 1, z, P :: l =>
      Bd true (k + 1) z l + g P * (if (P : ℝ) ^ 3 ≤ z then Bd false (k + 1) (z / P) l else 0)
  | false, 0, _, _ :: _ => 0
  | false, k + 1, z, P :: l => Bd false (k + 1) z l + g P * Bd true k (z / P) l

/-- **Def A.1** `B⁺_k`: upper boundary sum of depth `k` (chains of `2k+1` primes). -/
noncomputable def Bp (k : ℕ) (z : ℝ) (l : List ℕ) : ℝ := Bd g true k z l

/-- **Def A.1** `B⁻_k`: lower boundary sum of depth `k` (chains of `2k` primes, `Bm 0 = 0`). -/
noncomputable def Bm (k : ℕ) (z : ℝ) (l : List ℕ) : ℝ := Bd g false k z l

theorem Vl_nil : Vl g [] = 1 := by simp [Vl]

theorem Vl_cons (P : ℕ) (l : List ℕ) : Vl g (P :: l) = (1 - g P) * Vl g l := by simp [Vl]

theorem Bp_nil (k : ℕ) (z : ℝ) : Bp g k z [] = 0 := by unfold Bp; cases k <;> rfl

theorem Bm_nil (k : ℕ) (z : ℝ) : Bm g k z [] = 0 := by unfold Bm; cases k <;> rfl

theorem Bm_zero (z : ℝ) (l : List ℕ) : Bm g 0 z l = 0 := by unfold Bm; cases l <;> rfl

theorem Bp_zero_cons (z : ℝ) (P : ℕ) (l : List ℕ) :
    Bp g 0 z (P :: l) = Bp g 0 z l + g P * (if z < (P : ℝ) ^ 3 then Vl g l else 0) := rfl

theorem Bp_succ_cons (k : ℕ) (z : ℝ) (P : ℕ) (l : List ℕ) :
    Bp g (k + 1) z (P :: l) =
      Bp g (k + 1) z l + g P * (if (P : ℝ) ^ 3 ≤ z then Bm g (k + 1) (z / P) l else 0) := rfl

theorem Bm_succ_cons (k : ℕ) (z : ℝ) (P : ℕ) (l : List ℕ) :
    Bm g (k + 1) z (P :: l) = Bm g (k + 1) z l + g P * Bp g k (z / P) l := rfl

/-- The blueprint form of the recursion (A.1), with `if k = 0`. -/
theorem Bp_cons (k : ℕ) (z : ℝ) (P : ℕ) (l : List ℕ) :
    Bp g k z (P :: l) = Bp g k z l + g P * (if k = 0 then (if z < (P : ℝ) ^ 3 then Vl g l else 0)
      else (if (P : ℝ) ^ 3 ≤ z then Bm g k (z / P) l else 0)) := by
  cases k with
  | zero => rw [Bp_zero_cons, ite_eq_left rfl]
  | succ k => rw [Bp_succ_cons, ite_eq_right (Nat.succ_ne_zero k)]

theorem Bm_cons (k : ℕ) (z : ℝ) (P : ℕ) (l : List ℕ) :
    Bm g k z (P :: l) = Bm g k z l + (if k = 0 then 0 else g P * Bp g (k - 1) (z / P) l) := by
  cases k with
  | zero => rw [Bm_zero, Bm_zero, ite_eq_left rfl, add_zero]
  | succ k => rw [Bm_succ_cons, ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]

/-- **Lemma A.2 (boundary identity)**, with any number `N > |l|` of depths. -/
theorem boundary_identity : ∀ (l : List ℕ) (N : ℕ), l.length < N → ∀ z : ℝ,
    Sg g true z l = Vl g l + ∑ k ∈ range N, Bp g k z l ∧
    Sg g false z l = Vl g l - ∑ k ∈ range N, Bm g k z l := by
  intro l
  induction l with
  | nil => intro N _ z; simp [Sg, Vl_nil, Bp_nil, Bm_nil]
  | cons P l ih =>
    intro N hN z
    simp only [List.length_cons] at hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hM : l.length < M := by omega
    have hN' : l.length < M + 1 := by omega
    obtain ⟨ihT, ihF⟩ := ih (M + 1) hN' z
    obtain ⟨-, ihF'⟩ := ih (M + 1) hN' (z / P)
    obtain ⟨ihT', -⟩ := ih M hM (z / P)
    have hBm : ∀ (z' : ℝ) (l' : List ℕ), ∑ k ∈ range (M + 1), Bm g k z' l' =
        ∑ k ∈ range M, Bm g (k + 1) z' l' := by
      intro z' l'; rw [sum_range_succ', Bm_zero, add_zero]
    have hBp : ∑ k ∈ range (M + 1), Bp g k z l = ∑ k ∈ range M, Bp g (k + 1) z l + Bp g 0 z l :=
      sum_range_succ' _ _
    constructor
    · rw [sum_range_succ', Bp_zero_cons, Vl_cons]
      simp only [Bp_succ_cons, sum_add_distrib, ← mul_sum]
      simp only [Sg]
      by_cases h : (P : ℝ) ^ 3 ≤ z
      · have hh : headOK true z P := h
        have hn : ¬ z < (P : ℝ) ^ 3 := not_lt.2 h
        simp only [ite_eq_left hh, ite_eq_left h, ite_eq_right hn, Bool.not_true]
        rw [← hBm, ihT, ihF']
        linarith
      · have hh : ¬ headOK true z P := h
        have hn : z < (P : ℝ) ^ 3 := not_le.1 h
        simp only [ite_eq_right hh, ite_eq_right h, ite_eq_left hn, sum_const_zero, mul_zero, sub_zero]
        rw [ihT]
        linarith
    · rw [hBm, Vl_cons]
      simp only [Bm_succ_cons, sum_add_distrib, ← mul_sum]
      simp only [Sg, ite_eq_left (show headOK false z P from trivial), Bool.not_false]
      rw [← hBm, ihF, ihT']
      ring

theorem Sg_true_eq (l : List ℕ) (z : ℝ) :
    Sg g true z l = Vl g l + ∑ k ∈ range (l.length + 1), Bp g k z l :=
  (boundary_identity g l (l.length + 1) (Nat.lt_succ_self _) z).1

theorem Sg_false_eq (l : List ℕ) (z : ℝ) :
    Sg g false z l = Vl g l - ∑ k ∈ range (l.length + 1), Bm g k z l :=
  (boundary_identity g l (l.length + 1) (Nat.lt_succ_self _) z).2

/-- **A.2, range remark**: `Bp k = 0` if `|l| < 2k+1`, `Bm k = 0` if `|l| < 2k`. -/
theorem Bd_eq_zero_of_length : ∀ (l : List ℕ) (k : ℕ) (z : ℝ),
    (l.length < 2 * k + 1 → Bp g k z l = 0) ∧ (l.length < 2 * k → Bm g k z l = 0) := by
  intro l
  induction l with
  | nil => intro k z; exact ⟨fun _ => Bp_nil g k z, fun _ => Bm_nil g k z⟩
  | cons P l ih =>
    intro k z
    simp only [List.length_cons]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases k with
      | zero => omega
      | succ k =>
        rw [Bp_succ_cons, (ih (k + 1) z).1 (by omega), (ih (k + 1) (z / P)).2 (by omega)]
        simp
    · cases k with
      | zero => exact Bm_zero g z _
      | succ k =>
        rw [Bm_succ_cons, (ih (k + 1) z).2 (by omega), (ih k (z / P)).1 (by omega)]
        simp

theorem Bp_eq_zero_of_length {l : List ℕ} {k : ℕ} (z : ℝ) (h : l.length < 2 * k + 1) : Bp g k z l = 0 :=
  (Bd_eq_zero_of_length g l k z).1 h

theorem Bm_eq_zero_of_length {l : List ℕ} {k : ℕ} (z : ℝ) (h : l.length < 2 * k) : Bm g k z l = 0 :=
  (Bd_eq_zero_of_length g l k z).2 h

theorem Vl_nonneg (hg1 : ∀ p, g p ≤ 1) (l : List ℕ) : 0 ≤ Vl g l := by
  induction l with
  | nil => simp [Vl_nil]
  | cons P l ih => rw [Vl_cons]; exact mul_nonneg (by linarith [hg1 P]) ih

theorem Vl_le_one (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (l : List ℕ) : Vl g l ≤ 1 := by
  induction l with
  | nil => simp [Vl_nil]
  | cons P l ih =>
    rw [Vl_cons]
    have := Vl_nonneg g hg1 l
    have := hg0 P
    nlinarith

theorem one_le_prod_one_add (hg0 : ∀ p, 0 ≤ g p) (l : List ℕ) : 1 ≤ (l.map (fun q => 1 + g q)).prod := by
  induction l with
  | nil => simp
  | cons P l ih =>
    simp only [List.map_cons, List.prod_cons]
    have := hg0 P
    nlinarith

/-- **Lemma A.3 (sign and crude size)**: `0 ≤ Bp, Bm ≤ Π_{q∈l} (1 + g q)`. -/
theorem Bd_bounds (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) : ∀ (l : List ℕ) (k : ℕ) (z : ℝ),
    (0 ≤ Bp g k z l ∧ Bp g k z l ≤ (l.map (fun q => 1 + g q)).prod) ∧
    (0 ≤ Bm g k z l ∧ Bm g k z l ≤ (l.map (fun q => 1 + g q)).prod) := by
  intro l
  induction l with
  | nil => intro k z; simp [Bp_nil, Bm_nil]
  | cons P l ih =>
    intro k z
    simp only [List.map_cons, List.prod_cons]
    have hP0 := hg0 P
    have hPi := one_le_prod_one_add g hg0 l
    have hV0 := Vl_nonneg g hg1 l
    have hV1 := Vl_le_one g hg0 hg1 l
    -- a generic step: `X + g P * Y` with `0 ≤ X, Y ≤ Π`
    have step : ∀ X Y : ℝ, 0 ≤ X → X ≤ (l.map (fun q => 1 + g q)).prod → 0 ≤ Y →
        Y ≤ (l.map (fun q => 1 + g q)).prod →
        0 ≤ X + g P * Y ∧ X + g P * Y ≤ (1 + g P) * (l.map (fun q => 1 + g q)).prod := by
      intro X Y hX0 hX1 hY0 hY1
      constructor
      · positivity
      · nlinarith
    refine ⟨?_, ?_⟩
    · cases k with
      | zero =>
        rw [Bp_zero_cons]
        obtain ⟨h1, h2⟩ := (ih 0 z).1
        apply step _ _ h1 h2
        · split_ifs <;> linarith
        · split_ifs <;> linarith
      | succ k =>
        rw [Bp_succ_cons]
        obtain ⟨h1, h2⟩ := (ih (k + 1) z).1
        obtain ⟨h3, h4⟩ := (ih (k + 1) (z / P)).2
        apply step _ _ h1 h2
        · split_ifs <;> linarith
        · split_ifs <;> linarith
    · cases k with
      | zero => rw [Bm_zero]; exact ⟨le_refl _, by nlinarith⟩
      | succ k =>
        rw [Bm_succ_cons]
        obtain ⟨h1, h2⟩ := (ih (k + 1) z).2
        obtain ⟨h3, h4⟩ := (ih k (z / P)).1
        exact step _ _ h1 h2 h3 h4

/-- **A.4, list part**: a recursion `F (P :: l) = F l + c P l` unrolls on `toDec S` to
`Σ_{P∈S} c P (toDec {q ∈ S | q < P})`. -/
theorem unroll_toDec (F : List ℕ → ℝ) (c : ℕ → List ℕ → ℝ) (h0 : F [] = 0)
    (h1 : ∀ P l, F (P :: l) = F l + c P l) (S : Finset ℕ) :
    F (toDec S) = ∑ P ∈ S, c P (toDec (S.filter (· < P))) := by
  induction S using Finset.induction_on_max with
  | empty => simp [toDec_empty, h0]
  | insert M S hM ih =>
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, h1, ih, sum_insert hMS]
    have e1 : (insert M S).filter (· < M) = S := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hM x hx⟩
    have e2 : ∀ P ∈ S, (insert M S).filter (· < P) = S.filter (· < P) := by
      intro P hP; ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd (lt_trans hlt (hM P hP)) (lt_irrefl _)
        · exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
    rw [e1, add_comm]
    congr 1
    exact sum_congr rfl (fun P hP => by rw [e2 P hP])

theorem prod_toDec (f : ℕ → ℝ) (S : Finset ℕ) : ((toDec S).map f).prod = ∏ x ∈ S, f x := by
  induction S using Finset.induction_on_max with
  | empty => simp [toDec_empty]
  | insert M S hM ih =>
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, List.map_cons, List.prod_cons, ih, prod_insert hMS]

theorem length_toDec (S : Finset ℕ) : (toDec S).length = S.card := by
  unfold toDec; exact Finset.length_sort _

theorem Vl_toDec (S : Finset ℕ) : Vl g (toDec S) = ∏ x ∈ S, (1 - g x) := prod_toDec _ S

end Generic

/-! ## On the primes below `w`, density `gB b` -/

theorem primesBelow_filter_lt (w : ℝ) (P : ℕ) (hP : P ∈ primesBelow w) :
    (primesBelow w).filter (· < P) = primesBelow (P : ℝ) := by
  ext q
  rw [mem_filter, mem_primesBelow, mem_primesBelow]
  have hPw := ((mem_primesBelow w P).1 hP).2
  constructor
  · rintro ⟨⟨hq, _⟩, hqP⟩; exact ⟨hq, by exact_mod_cast hqP⟩
  · rintro ⟨hq, hqP⟩
    have hqP' : q < P := by exact_mod_cast hqP
    exact ⟨⟨hq, lt_trans hqP hPw⟩, hqP'⟩

private theorem gB_nonneg_aux (b p : ℕ) : 0 ≤ gB b p := by
  unfold gB; split_ifs <;> positivity

private theorem gB_le_one_aux (b p : ℕ) : gB b p ≤ 1 := by
  unfold gB; split_ifs with h
  · have : (1 : ℝ) ≤ p := by exact_mod_cast h.1.one_lt.le
    rw [div_le_one (by linarith)]; exact this
  · norm_num

/-- `B⁺_k(D, w)` for the density `gB b` on the primes below `w`. -/
noncomputable def BP (b k : ℕ) (D w : ℝ) : ℝ := Bp (gB b) k D (toDec (primesBelow w))

/-- `B⁻_k(D, w)` for the density `gB b` on the primes below `w`. -/
noncomputable def BM (b k : ℕ) (D w : ℝ) : ℝ := Bm (gB b) k D (toDec (primesBelow w))

theorem VB_eq_Vl (b : ℕ) (w : ℝ) : VB b w = Vl (gB b) (toDec (primesBelow w)) := by
  rw [Vl_toDec]; rfl

theorem BM_zero (b : ℕ) (D w : ℝ) : BM b 0 D w = 0 := Bm_zero _ _ _

/-- **A.2 on the primes below `w`**, any number `N > π(w)` of depths. -/
theorem Sg_true_primesBelow (b : ℕ) (D w : ℝ) (N : ℕ) (hN : (primesBelow w).card < N) :
    Sg (gB b) true D (toDec (primesBelow w)) = VB b w + ∑ k ∈ range N, BP b k D w := by
  rw [VB_eq_Vl]
  exact (boundary_identity (gB b) _ N (by rw [length_toDec]; exact hN) D).1

theorem Sg_false_primesBelow (b : ℕ) (D w : ℝ) (N : ℕ) (hN : (primesBelow w).card < N) :
    Sg (gB b) false D (toDec (primesBelow w)) = VB b w - ∑ k ∈ range N, BM b k D w := by
  rw [VB_eq_Vl]
  exact (boundary_identity (gB b) _ N (by rw [length_toDec]; exact hN) D).2

/-- **A.2 for `Splus`**: `S⁺(z, s) = V(w) + Σ_k B⁺_k(z, w)`, `w = z^{1/s}`. -/
theorem Splus_eq (b : ℕ) (z s : ℝ) :
    Splus b z s = VB b (z ^ (1 / s)) +
      ∑ k ∈ range ((primesBelow (z ^ (1 / s))).card + 1), BP b k z (z ^ (1 / s)) :=
  Sg_true_primesBelow b z _ _ (Nat.lt_succ_self _)

/-- **A.2 for `Sminus`**: `S⁻(z, s) = V(w) − Σ_k B⁻_k(z, w)`, `w = z^{1/s}`. -/
theorem Sminus_eq (b : ℕ) (z s : ℝ) :
    Sminus b z s = VB b (z ^ (1 / s)) -
      ∑ k ∈ range ((primesBelow (z ^ (1 / s))).card + 1), BM b k z (z ^ (1 / s)) :=
  Sg_false_primesBelow b z _ _ (Nat.lt_succ_self _)

/-- **A.3** `B⁺_k ≥ 0`. -/
theorem BP_nonneg (b k : ℕ) (D w : ℝ) : 0 ≤ BP b k D w :=
  ((Bd_bounds (gB b) (gB_nonneg_aux b) (gB_le_one_aux b) _ k D).1).1

/-- **A.3** `B⁻_k ≥ 0`. -/
theorem BM_nonneg (b k : ℕ) (D w : ℝ) : 0 ≤ BM b k D w :=
  ((Bd_bounds (gB b) (gB_nonneg_aux b) (gB_le_one_aux b) _ k D).2).1

/-- **A.3** crude bound `B⁺_k ≤ Π_{p<w} (1 + g p)`. -/
theorem BP_le_prod (b k : ℕ) (D w : ℝ) : BP b k D w ≤ ∏ p ∈ primesBelow w, (1 + gB b p) := by
  rw [← prod_toDec]
  exact ((Bd_bounds (gB b) (gB_nonneg_aux b) (gB_le_one_aux b) _ k D).1).2

/-- **A.3** crude bound `B⁻_k ≤ Π_{p<w} (1 + g p)`. -/
theorem BM_le_prod (b k : ℕ) (D w : ℝ) : BM b k D w ≤ ∏ p ∈ primesBelow w, (1 + gB b p) := by
  rw [← prod_toDec]
  exact ((Bd_bounds (gB b) (gB_nonneg_aux b) (gB_le_one_aux b) _ k D).2).2

/-- **A.4** `B⁺_0(D, w) = Σ_{p<w, D<p³} g(p) V(p)`. -/
theorem BP_zero_eq (b : ℕ) (D w : ℝ) :
    BP b 0 D w = ∑ p ∈ (primesBelow w).filter (fun p : ℕ => D < (p : ℝ) ^ 3), gB b p * VB b p := by
  unfold BP
  rw [unroll_toDec (fun l => Bp (gB b) 0 D l) (fun P l => gB b P * (if D < (P : ℝ) ^ 3 then Vl (gB b) l else 0))
    (Bp_nil _ _ _) (fun P l => Bp_zero_cons _ _ _ _), sum_filter]
  refine sum_congr rfl (fun p hp => ?_)
  rw [primesBelow_filter_lt w p hp, ← VB_eq_Vl]
  split_ifs <;> simp

/-- **A.4** `B⁺_{k+1}(D, w) = Σ_{p<w, p³≤D} g(p) B⁻_{k+1}(D/p, p)`. -/
theorem BP_succ_eq (b k : ℕ) (D w : ℝ) :
    BP b (k + 1) D w = ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D),
      gB b p * BM b (k + 1) (D / p) p := by
  unfold BP BM
  rw [unroll_toDec (fun l => Bp (gB b) (k + 1) D l)
    (fun P l => gB b P * (if (P : ℝ) ^ 3 ≤ D then Bm (gB b) (k + 1) (D / P) l else 0))
    (Bp_nil _ _ _) (fun P l => Bp_succ_cons _ _ _ _ _), sum_filter]
  refine sum_congr rfl (fun p hp => ?_)
  rw [primesBelow_filter_lt w p hp]
  split_ifs <;> simp

/-- **A.4** `B⁻_{k+1}(D, w) = Σ_{p<w} g(p) B⁺_k(D/p, p)`. -/
theorem BM_succ_eq (b k : ℕ) (D w : ℝ) :
    BM b (k + 1) D w = ∑ p ∈ primesBelow w, gB b p * BP b k (D / p) p := by
  unfold BP BM
  rw [unroll_toDec (fun l => Bm (gB b) (k + 1) D l) (fun P l => gB b P * Bp (gB b) k (D / P) l)
    (Bm_nil _ _ _) (fun P l => Bm_succ_cons _ _ _ _ _)]
  exact sum_congr rfl (fun p hp => by rw [primesBelow_filter_lt w p hp])

/-- **A.5 (ii)** `B⁺_k = 0` if `π(w) < 2k+1`. -/
theorem BP_eq_zero_of_card (b k : ℕ) (D w : ℝ) (h : (primesBelow w).card < 2 * k + 1) : BP b k D w = 0 :=
  Bp_eq_zero_of_length _ D (by rw [length_toDec]; exact h)

/-- **A.5 (ii)** `B⁻_k = 0` if `π(w) < 2k`. -/
theorem BM_eq_zero_of_card (b k : ℕ) (D w : ℝ) (h : (primesBelow w).card < 2 * k) : BM b k D w = 0 :=
  Bm_eq_zero_of_length _ D (by rw [length_toDec]; exact h)

private theorem prime_pos_lt (w : ℝ) (p : ℕ) (hp : p ∈ primesBelow w) : (0 : ℝ) < p ∧ (p : ℝ) < w := by
  rw [mem_primesBelow] at hp
  exact ⟨by exact_mod_cast hp.1.pos, hp.2⟩

/-- **A.5 (i)** in power form: `B⁺_k(D,w) = 0` if `w^{2k+3} ≤ D`, `B⁻_k(D,w) = 0` if `w^{2k+2} ≤ D`. -/
theorem B_eq_zero_of_pow_le (b : ℕ) : ∀ k : ℕ,
    (∀ D w : ℝ, w ^ (2 * k + 3) ≤ D → BP b k D w = 0) ∧ (∀ D w : ℝ, w ^ (2 * k + 2) ≤ D → BM b k D w = 0) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun D w h => ?_, fun D w _ => BM_zero b D w⟩
    rw [BP_zero_eq]
    apply sum_eq_zero
    intro p hp
    exfalso
    rw [mem_filter] at hp
    obtain ⟨hp0, hpw⟩ := prime_pos_lt w p hp.1
    have : (p : ℝ) ^ 3 < w ^ 3 := pow_lt_pow_left₀ hpw hp0.le (by norm_num)
    simp only [Nat.mul_zero, Nat.zero_add] at h
    linarith [hp.2]
  | succ k ih =>
    have hM : ∀ D w : ℝ, w ^ (2 * (k + 1) + 2) ≤ D → BM b (k + 1) D w = 0 := by
      intro D w h
      rw [BM_succ_eq]
      apply sum_eq_zero
      intro p hp
      obtain ⟨hp0, hpw⟩ := prime_pos_lt w p hp
      have h1 : (p : ℝ) ^ (2 * k + 3) ≤ D / p := by
        rw [le_div_iff₀ hp0, ← pow_succ]
        have : (p : ℝ) ^ (2 * k + 3 + 1) ≤ w ^ (2 * k + 3 + 1) := pow_le_pow_left₀ hp0.le hpw.le _
        have e : 2 * (k + 1) + 2 = 2 * k + 3 + 1 := by ring
        rw [e] at h; linarith
      rw [ih.1 _ _ h1, mul_zero]
    refine ⟨fun D w h => ?_, hM⟩
    rw [BP_succ_eq]
    apply sum_eq_zero
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hp0, hpw⟩ := prime_pos_lt w p hp.1
    have h1 : (p : ℝ) ^ (2 * (k + 1) + 2) ≤ D / p := by
      rw [le_div_iff₀ hp0, ← pow_succ]
      have : (p : ℝ) ^ (2 * (k + 1) + 2 + 1) ≤ w ^ (2 * (k + 1) + 2 + 1) := pow_le_pow_left₀ hp0.le hpw.le _
      have e : 2 * (k + 1) + 3 = 2 * (k + 1) + 2 + 1 := by ring
      rw [e] at h; linarith
    rw [hM _ _ h1, mul_zero]

theorem BP_eq_zero_of_pow_le (b k : ℕ) {D w : ℝ} (h : w ^ (2 * k + 3) ≤ D) : BP b k D w = 0 :=
  (B_eq_zero_of_pow_le b k).1 D w h

theorem BM_eq_zero_of_pow_le (b k : ℕ) {D w : ℝ} (h : w ^ (2 * k + 2) ≤ D) : BM b k D w = 0 :=
  (B_eq_zero_of_pow_le b k).2 D w h

private theorem pow_le_of_le_log_div {D w : ℝ} (n : ℕ) (hD : 0 < D) (hw : 1 < w)
    (hs : (n : ℝ) ≤ Real.log D / Real.log w) : w ^ n ≤ D := by
  have hlw : 0 < Real.log w := Real.log_pos hw
  have h1 : (n : ℝ) * Real.log w ≤ Real.log D := (le_div_iff₀ hlw).1 hs
  rw [← Real.log_pow] at h1
  exact (Real.log_le_log_iff (by positivity) hD).1 h1

/-- **A.5 (i)** in `s`-form: `B⁺_k = 0` for `s ≥ 2k+3`, `s = log D / log w`. -/
theorem BP_eq_zero_of_s (b k : ℕ) {D w : ℝ} (hD : 0 < D) (hw : 1 < w)
    (hs : (2 * k + 3 : ℝ) ≤ Real.log D / Real.log w) : BP b k D w = 0 :=
  BP_eq_zero_of_pow_le b k (pow_le_of_le_log_div (2 * k + 3) hD hw (by push_cast; exact hs))

/-- **A.5 (i)** in `s`-form: `B⁻_k = 0` for `s ≥ 2k+2`. -/
theorem BM_eq_zero_of_s (b k : ℕ) {D w : ℝ} (hD : 0 < D) (hw : 1 < w)
    (hs : (2 * k + 2 : ℝ) ≤ Real.log D / Real.log w) : BM b k D w = 0 :=
  BM_eq_zero_of_pow_le b k (pow_le_of_le_log_div (2 * k + 2) hD hw (by push_cast; exact hs))

/-- `π(w) < w` for `w ≥ 2`. -/
theorem card_primesBelow_lt (w : ℝ) (hw : 2 ≤ w) : ((primesBelow w).card : ℝ) < w := by
  have hsub : primesBelow w ⊆ Finset.Ico 2 ⌈w⌉₊ := by
    intro p hp
    rw [mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.1.two_le, Nat.lt_ceil.2 hp.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 : 2 ≤ ⌈w⌉₊ := by
    have : (2 : ℝ) ≤ ⌈w⌉₊ := le_trans hw (Nat.le_ceil w)
    exact_mod_cast this
  have h3 : ((primesBelow w).card : ℝ) ≤ (⌈w⌉₊ : ℝ) - 2 := by
    have : ((primesBelow w).card : ℝ) ≤ ((⌈w⌉₊ - 2 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub h2] at this; simpa using this
  have h4 : (⌈w⌉₊ : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

/-- **Corollary A.6 (no chains below `W₀`)**: if `2 ≤ w < W₀` and `D ≥ W₀^{W₀+3}`, all `B^±_k(D, w)` vanish. -/
theorem no_chains_below (b : ℕ) {W₀ w D : ℝ} (hw : 2 ≤ w) (hwW : w < W₀) (hD : W₀ ^ (W₀ + 3) ≤ D) (k : ℕ) :
    BP b k D w = 0 ∧ BM b k D w = 0 := by
  have hπ := card_primesBelow_lt w hw
  have hW1 : 1 ≤ W₀ := by linarith
  have hw0 : 0 ≤ w := by linarith
  -- `w^n ≤ D` whenever `(n : ℝ) ≤ W₀ + 3`
  have key : ∀ n : ℕ, (n : ℝ) ≤ W₀ + 3 → w ^ n ≤ D := by
    intro n hn
    calc w ^ n ≤ W₀ ^ n := pow_le_pow_left₀ hw0 hwW.le n
      _ = W₀ ^ (n : ℝ) := (Real.rpow_natCast W₀ n).symm
      _ ≤ W₀ ^ (W₀ + 3) := Real.rpow_le_rpow_of_exponent_le hW1 hn
      _ ≤ D := hD
  constructor
  · by_cases h : (primesBelow w).card < 2 * k + 1
    · exact BP_eq_zero_of_card b k D w h
    · rw [not_lt] at h
      have h' : ((2 * k + 1 : ℕ) : ℝ) ≤ (primesBelow w).card := by exact_mod_cast h
      apply BP_eq_zero_of_pow_le
      apply key
      push_cast at h' ⊢
      linarith
  · by_cases h : (primesBelow w).card < 2 * k
    · exact BM_eq_zero_of_card b k D w h
    · rw [not_lt] at h
      have h' : ((2 * k : ℕ) : ℝ) ≤ (primesBelow w).card := by exact_mod_cast h
      apply BM_eq_zero_of_pow_le
      apply key
      push_cast at h' ⊢
      linarith

end Palprimes.E1
