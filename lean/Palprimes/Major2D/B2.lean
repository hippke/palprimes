import Palprimes.Major2D.B2Check
import Palprimes.Major2D.B2Chunks
import Palprimes.Major2D.B3
import Palprimes.Major2D.Spec2

/-! # TL¹ for base 2 (`l = 7`, `p = 999/1000`, `θ = 0.2608`, `δ = 0.47`)

The majorant `T2full` (551 terms) satisfies `‖Γ₇(x, y)‖^{999/1000} ≤ T(x, y)` everywhere by the kernel-checked cell
certificate (`B2C*.lean`, 3136 level-0 cells, `Q₀ = 192`) and the symmetry group `Λ × swap × negation` (order 12). -/

set_option linter.style.longLine false
set_option maxRecDepth 8000

open Real Finset Complex

namespace Palprimes.M2

/-! ## `‖D₂(t)‖ = |cos πt|` -/

theorem norm_Dfun2 (t : ℝ) : ‖Dfun 2 t‖ = |Real.cos (π * t)| := by
  unfold Dfun
  have hs : ∑ j ∈ range 2, ee (j * t) = ee (t / 2) * ((2 * Real.cos (π * t) : ℝ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul]
    have e0 : ee 0 = 1 := by unfold ee; simp
    have h1 := ee_add_neg (t / 2)
    rw [show 2 * π * (t / 2) = π * t by ring] at h1
    rw [← h1, mul_add, ee_mul, ee_mul, show t / 2 + t / 2 = t by ring, show t / 2 + -(t / 2) = 0 by ring, e0]
    ring
  rw [hs, norm_mul, norm_mul, norm_ee, Complex.norm_real, norm_inv]
  simp only [Real.norm_eq_abs, one_mul]
  rw [show ‖((2 : ℕ) : ℂ)‖ = 2 by simp, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-! ## The factors and the block function -/

theorem fac2_val (U V : ℤ) (x y : ℝ) :
    sumVal [(U, V, 1)] 1 x y = Real.cos (π * (U * x + V * y)) := by
  unfold sumVal; simp

theorem gam2 (x y : ℝ) : ‖Gam 2 7 x y‖ = (facs2.map (fun f => |sumVal f.1 f.2 x y|)).prod := by
  unfold Gam
  rw [norm_prod]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, norm_Dfun2, facs2, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, fac2_val]
  norm_num
  ring_nf

theorem fac2_le (f : List (ℤ × ℤ × ℕ) × ℕ) (hf : f ∈ facs2) (x y : ℝ) : |sumVal f.1 f.2 x y| ≤ 1 := by
  simp only [facs2, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [fac2_val]; exact Real.abs_cos_le_one _)

/-! ## The configuration is sound -/

theorem cfg2_ok : CfgOK cfg2 T2terms 4503599627370496 where
  hT := rfl
  hfP := rfl
  hA := rfl
  hn0 := by decide
  hU2 := u2Chk_spec _ _ U2_2_ok
  hV := vChk_spec _ _ V2_ok
  hfacs := by decide
  hfac1 := fac2_le
  hQ0 := by decide
  htab := by
    intro d hd
    have hd' : d ≤ 5 := hd
    interval_cases d
    exacts [tab2_lv0, tab2_lv1, tab2_lv2, tab2_lv3, tab2_lv4, tab2_lv5]
  hO := by
    intro d hd
    show 4 * 192 * 2 ^ d ∣ 4 * 192 * 2 ^ 24
    have hd' : d ≤ 24 := le_trans hd (by decide)
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow 2 hd')

theorem sym2_ok : SymOK cfg2 T2terms 3 shifts2 where
  hm := by norm_num
  hTsh := shiftT2
  hFsh := shiftF2
  hTsw := swapT2
  hFsw := swapF2
  hm0 := by decide
  h0m := by decide

theorem good2 : ∀ x y : ℝ, Good cfg2 T2terms 4503599627370496 x y :=
  good_all cfg2 T2terms _ cfg2_ok 3 shifts2 sym2_ok 64 rfl G2 G2ok L2 chk2 L2lt cover2

/-! ## The block majorant -/

theorem hmaj2 (x y : ℝ) : ‖Gam 2 7 x y‖ ^ (999 / 1000 : ℝ) ≤ Tval (Sset T2full) (tauF T2full) x y := by
  have h := good2 x y
  unfold Good at h
  rw [gam2, tval_eq T2full T2terms nodup2 perm2 even2]
  have e : (1 - 1 / (cfg2.n0 : ℝ)) = 999 / 1000 := by simp [cfg2]; norm_num
  rw [e] at h
  exact h

noncomputable def M2 : BlockMaj 2 7 where
  S := Sset T2full
  τ := tauF T2full
  p := 999 / 1000
  hp0 := by norm_num
  hp1 := by norm_num
  h00 := by unfold Sset; rw [List.mem_toFinset]; exact zero2
  hS := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    obtain ⟨h1, h2⟩ := bounds2 e he
    constructor
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  hneg := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    unfold Sset; rw [List.mem_toFinset, List.mem_map]
    exact ⟨_, neg2 e he, rfl⟩
  hsym := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := mem_Sset _ _ hw
    unfold tauF
    rw [lk_mem _ nodup2 e he, show -e.1 = ((-e.1.1, -e.1.2), e.2).1 from rfl, lk_mem _ nodup2 _ (neg2 e he)]
  hmaj := hmaj2

theorem M2_t00 : M2.t00 = (358572778288936 : ℝ) / 2 ^ 52 := by
  show tauF T2full (0, 0) = _
  unfold tauF; rw [t00_2]; norm_num

theorem M2_A : M2.A = (4504889504128116 : ℝ) / 2 ^ 52 := by
  show ∑ w ∈ Sset T2full, |tauF T2full w| = _
  rw [A_list _ nodup2, A2]; norm_num

/-! ## TL¹ for base 2 -/

/-- **TL¹ for base `2`** at `θ = 0.2608`, `δ = 0.47` (`κ = 1/1050000`). -/
theorem tl1_two : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R0 : ℕ, (((2 : ℕ) : ℝ) ^ N) ^ (47 / 100 : ℝ) ≤ R0 →
      (R0 : ℝ) ≤ (((2 : ℕ) : ℝ) ^ (2 * N + 1)) ^ (2608 / 10000 : ℝ) →
      ∀ Qs : Finset ℕ, (∀ q ∈ Qs, R0 ≤ q ∧ q ≤ 2 * R0 ∧ Nat.Coprime q 2) → ∀ β : ℝ,
        ∑ q ∈ Qs, ∑ h ∈ redRes q, Fprod 2 N ((h : ℝ) / q + β) ≤ R0 * ((((2 : ℕ) : ℝ)) ^ N) ^ (-κ) := by
  set κ : ℝ := 1 / 1050000 with hκ
  refine ⟨κ, by norm_num, by norm_num, ?_⟩
  have hb1 : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  have hb0 : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
  have ht0 : (0 : ℝ) < (358572778288936 : ℝ) / 2 ^ 52 := by norm_num
  have hA0 : (0 : ℝ) < (4504889504128116 : ℝ) / 2 ^ 52 := by norm_num
  set ψ := -Real.logb ((2 : ℕ) : ℝ) ((358572778288936 : ℝ) / 2 ^ 52) / 7 with hψ
  set lamA := Real.logb ((2 : ℕ) : ℝ) ((4504889504128116 : ℝ) / 2 ^ 52) / 7 with hlam
  have c2 := cond_from_int 2 (by norm_num) 7 937500 3423025 1141 358572778288936 (by norm_num) (by norm_num) (by norm_num) cond2_2
  have c3 := cond_from_int 2 (by norm_num) 7 300000 12 329 4504889504128116 (by norm_num) (by norm_num) (by norm_num) cond3_2
  push_cast at c2 c3
  have hlogt : Real.logb ((2 : ℕ) : ℝ) ((358572778288936 : ℝ) / 2 ^ 52) ≤ 0 :=
    Real.logb_nonpos hb1 ht0.le (by norm_num)
  have hlogA : 0 ≤ Real.logb ((2 : ℕ) : ℝ) ((4504889504128116 : ℝ) / 2 ^ 52) :=
    Real.logb_nonneg hb1 (by norm_num)
  have hMp : M2.p = 999 / 1000 := rfl
  apply tl1_eventually M2 (by norm_num) (by norm_num) ψ lamA (2608 / 10000) (47 / 100) κ κ
    (by rw [hψ]; linarith) (by rw [hlam]; positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hMp]; norm_num)
  · rw [M2_t00]; exact ht0.le
  · rw [M2_t00, hψ]
    rw [show -(((7 : ℕ) : ℝ) * (-Real.logb ((2 : ℕ) : ℝ) ((358572778288936 : ℝ) / 2 ^ 52) / 7)) =
      Real.logb ((2 : ℕ) : ℝ) ((358572778288936 : ℝ) / 2 ^ 52) by push_cast; ring]
    rw [Real.rpow_logb hb0 hb1.ne' ht0]
  · rw [M2_A, hlam]
    rw [show ((7 : ℕ) : ℝ) * (Real.logb ((2 : ℕ) : ℝ) ((4504889504128116 : ℝ) / 2 ^ 52) / 7) =
      Real.logb ((2 : ℕ) : ℝ) ((4504889504128116 : ℝ) / 2 ^ 52) by push_cast; ring]
    rw [Real.rpow_logb hb0 hb1.ne' hA0]
  · rw [hMp, hψ, hκ]; push_cast at c2 ⊢; norm_num at c2 ⊢; linarith
  · rw [hMp, hlam, hκ]; push_cast at c3 ⊢; norm_num at c3 ⊢; linarith

end Palprimes.M2
