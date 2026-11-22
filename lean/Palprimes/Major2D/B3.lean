import Palprimes.Major2D.B3Check
import Palprimes.Major2D.B3Chunks
import Palprimes.Major2D.Final

/-! # TL¹ for base 3 (`l = 3`, `p = 49/50`, `θ = 0.2608`, `δ = 0.47`)

The majorant `T3full` (73 terms) satisfies `‖Γ₃(x, y)‖^{49/50} ≤ T(x, y)` everywhere by the kernel-checked cell
certificate `chk3` (148 level-0 cells, `Q₀ = 64`) and the symmetry group `Λ × swap × negation` (order 32). -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real Finset Complex

namespace Palprimes.M2

/-! ## `‖D₃(t)‖ = |1 + 2 cos 2πt| / 3` -/

theorem ee_mul (s t : ℝ) : ee s * ee t = ee (s + t) := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ee_add_neg (t : ℝ) : ee t + ee (-t) = ((2 * Real.cos (2 * π * t) : ℝ) : ℂ) := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show 2 * (π : ℂ) * Complex.I * ((-t : ℝ) : ℂ) = (-((2 * π * t : ℝ) : ℂ)) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_mul (2 : ℝ),
    Complex.ofReal_cos]
  push_cast; ring

theorem norm_Dfun3 (t : ℝ) : ‖Dfun 3 t‖ = |1 + 2 * Real.cos (2 * π * t)| / 3 := by
  unfold Dfun
  have hs : ∑ j ∈ range 3, ee (j * t) = ee t * ((1 + 2 * Real.cos (2 * π * t) : ℝ) : ℂ) := by
    have e0 : ee 0 = 1 := by unfold ee; simp
    have e2 : ee (2 * t) = ee t * ee t := by rw [ee_mul]; congr 1; ring
    have e1 : ee t * ee (-t) = 1 := by rw [ee_mul]; simp [e0]
    have hc : ((1 + 2 * Real.cos (2 * π * t) : ℝ) : ℂ) = 1 + (ee t + ee (-t)) := by
      rw [ee_add_neg]; push_cast; ring
    rw [hc]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      Nat.cast_ofNat]
    rw [e0, e2]
    linear_combination (-1 : ℂ) * e1
  rw [hs, norm_mul, norm_mul, norm_ee, Complex.norm_real, norm_inv]
  simp only [Real.norm_eq_abs, one_mul]
  rw [show ‖((3 : ℕ) : ℂ)‖ = 3 by simp]
  ring

/-! ## The factors and the block function -/

theorem fac3_val (U V : ℤ) (x y : ℝ) :
    sumVal [(0, 0, 1), (U, V, 2)] 3 x y = (1 + 2 * Real.cos (π * (U * x + V * y))) / 3 := by
  unfold sumVal; simp

theorem gam3 (x y : ℝ) : ‖Gam 3 3 x y‖ = (facs3.map (fun f => |sumVal f.1 f.2 x y|)).prod := by
  unfold Gam
  rw [norm_prod]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, norm_Dfun3, facs3, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, fac3_val]
  rw [abs_div, abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num
  ring_nf

theorem fac3_le (f : List (ℤ × ℤ × ℕ) × ℕ) (hf : f ∈ facs3) (x y : ℝ) : |sumVal f.1 f.2 x y| ≤ 1 := by
  have key : ∀ U V : ℤ, |sumVal [(0, 0, 1), (U, V, 2)] 3 x y| ≤ 1 := by
    intro U V
    rw [fac3_val, abs_le]
    have := Real.neg_one_le_cos (π * (U * x + V * y))
    have := Real.cos_le_one (π * (U * x + V * y))
    constructor <;> linarith
  simp only [facs3, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> exact key _ _

/-! ## The configuration is sound -/

theorem cfg3_ok : CfgOK cfg3 T3terms 4503599627370496 where
  hT := rfl
  hfP := rfl
  hA := rfl
  hn0 := by decide
  hU2 := U2_3_ok
  hV := V3_ok
  hfacs := by decide
  hfac1 := fac3_le
  hQ0 := by decide
  htab := by
    intro d hd
    have hd' : d ≤ 5 := hd
    interval_cases d
    exacts [tab3_lv0, tab3_lv1, tab3_lv2, tab3_lv3, tab3_lv4, tab3_lv5]
  hO := by
    intro d hd
    show 4 * 64 * 2 ^ d ∣ 4 * 64 * 2 ^ 24
    have hd' : d ≤ 24 := le_trans hd (by decide)
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 hd')

theorem sym3_ok : SymOK cfg3 T3terms 8 shifts3 where
  hm := by norm_num
  hTsh := shiftT3
  hFsh := shiftF3
  hTsw := swapT3
  hFsw := swapF3
  hm0 := by decide
  h0m := by decide

theorem good3 : ∀ x y : ℝ, Good cfg3 T3terms 4503599627370496 x y :=
  good_all cfg3 T3terms _ cfg3_ok 8 shifts3 sym3_ok 8 rfl G3 G3ok L3 chk3 L3lt cover3

/-! ## The block majorant -/

theorem hmaj3 (x y : ℝ) : ‖Gam 3 3 x y‖ ^ (49 / 50 : ℝ) ≤ Tval (Sset T3full) (tauF T3full) x y := by
  have h := good3 x y
  unfold Good at h
  rw [gam3, tval_eq T3full T3terms nodup3 perm3 even3]
  have e : (1 - 1 / (cfg3.n0 : ℝ)) = 49 / 50 := by simp [cfg3]; norm_num
  rw [e] at h
  exact h

noncomputable def M3 : BlockMaj 3 3 where
  S := Sset T3full
  τ := tauF T3full
  p := 49 / 50
  hp0 := by norm_num
  hp1 := by norm_num
  h00 := by unfold Sset; rw [List.mem_toFinset]; exact zero3
  hS := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    obtain ⟨h1, h2⟩ := bounds3 e he
    constructor
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  hneg := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    unfold Sset; rw [List.mem_toFinset, List.mem_map]
    exact ⟨_, neg3 e he, rfl⟩
  hsym := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    unfold tauF
    rw [lk_mem _ nodup3 e he, show -e.1 = ((-e.1.1, -e.1.2), e.2).1 from rfl, lk_mem _ nodup3 _ (neg3 e he)]
  hmaj := hmaj3

theorem M3_t00 : M3.t00 = (809729125563748 : ℝ) / 2 ^ 52 := by
  show tauF T3full (0, 0) = _
  unfold tauF; rw [t00_3]; norm_num

theorem M3_A : M3.A = (4518200408842788 : ℝ) / 2 ^ 52 := by
  show ∑ w ∈ Sset T3full, |tauF T3full w| = _
  rw [A_list _ nodup3, A3]; norm_num

/-! ## TL¹ for base 3 -/

/-- **TL¹ for base `3`** at `θ = 0.2608`, `δ = 0.47` (`κ = 1/750000`). -/
theorem tl1_three : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, (((3 : ℕ) : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ (((3 : ℕ) : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q 3) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod 3 N ((h : ℝ) / q + β) ≤ R0 * ((((3 : ℕ) : ℝ)) ^ N) ^ (-κ) := by
  set κ : ℝ := 1 / 750000 with hκ
  refine ⟨κ, by norm_num, by norm_num, ?_⟩
  have hb1 : (1 : ℝ) < ((3 : ℕ) : ℝ) := by norm_num
  have hb0 : (0 : ℝ) < ((3 : ℕ) : ℝ) := by norm_num
  have ht0 : (0 : ℝ) < (809729125563748 : ℝ) / 2 ^ 52 := by norm_num
  have hA0 : (0 : ℝ) < (4518200408842788 : ℝ) / 2 ^ 52 := by norm_num
  set ψ := -Real.logb ((3 : ℕ) : ℝ) ((809729125563748 : ℝ) / 2 ^ 52) / 3 with hψ
  set lamA := Real.logb ((3 : ℕ) : ℝ) ((4518200408842788 : ℝ) / 2 ^ 52) / 3 with hlam
  have c2 := cond_from_int 3 (by norm_num) 3 62500 97801 652 809729125563748 (by norm_num) (by norm_num) (by norm_num) cond2_3
  have c3 := cond_from_int 3 (by norm_num) 3 125000 3 1175 4518200408842788 (by norm_num) (by norm_num) (by norm_num) cond3_3
  push_cast at c2 c3
  have hlogt : Real.logb ((3 : ℕ) : ℝ) ((809729125563748 : ℝ) / 2 ^ 52) ≤ 0 :=
    Real.logb_nonpos hb1 ht0.le (by norm_num)
  have hlogA : 0 ≤ Real.logb ((3 : ℕ) : ℝ) ((4518200408842788 : ℝ) / 2 ^ 52) :=
    Real.logb_nonneg hb1 (by norm_num)
  have hMp : M3.p = 49 / 50 := rfl
  apply tl1_eventually M3 (by norm_num) (by norm_num) ψ lamA (2608 / 10000) (47 / 100) κ κ
    (by rw [hψ]; linarith) (by rw [hlam]; positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hMp]; norm_num)
  · rw [M3_t00]; exact ht0.le
  · rw [M3_t00, hψ]
    rw [show -(((3 : ℕ) : ℝ) * (-Real.logb ((3 : ℕ) : ℝ) ((809729125563748 : ℝ) / 2 ^ 52) / 3)) =
      Real.logb ((3 : ℕ) : ℝ) ((809729125563748 : ℝ) / 2 ^ 52) by push_cast; ring]
    rw [Real.rpow_logb hb0 hb1.ne' ht0]
  · rw [M3_A, hlam]
    rw [show ((3 : ℕ) : ℝ) * (Real.logb ((3 : ℕ) : ℝ) ((4518200408842788 : ℝ) / 2 ^ 52) / 3) =
      Real.logb ((3 : ℕ) : ℝ) ((4518200408842788 : ℝ) / 2 ^ 52) by push_cast; ring]
    rw [Real.rpow_logb hb0 hb1.ne' hA0]
  · rw [hMp, hψ, hκ]; push_cast at c2 ⊢; norm_num at c2 ⊢; linarith
  · rw [hMp, hlam, hκ]; push_cast at c3 ⊢; norm_num at c3 ⊢; linarith

end Palprimes.M2
