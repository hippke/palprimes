import KappaOmega2.Items.M10_Sets
import Palprimes.E1.Mertens

/-!
# M10 helper: the sum over `p > y^m` of `K(y)³/p²` is `o(V(y))` (`M10_PLAN.md` §4.6)

`K(y) = Π_{q < y} (1 + γ(q)/q) ≤ 1/V(y)`, `Σ_{p > y^m} p^{−2} ≤ 2 y^{−m}`, `V(y) log y ≥ κ/2`, `y^m ≥ (m log y)^5/120`.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves

/-- `K(y) = Π_{q < y} (1 + γ(q)/q)`. -/
noncomputable def Kp (b : ℕ) (y : ℝ) : ℝ := ∏ q ∈ primesBelow y, (1 + rhoB b q / q)

theorem rhoB_div_eq_gB (b : ℕ) {q : ℕ} (hq : q.Prime) : rhoB b q / q = MT.gB b q := by
  unfold rhoB MT.gB
  by_cases h : Nat.Coprime q (bigB b)
  · rw [if_pos h, if_pos ⟨hq, h⟩]
  · rw [if_neg h, if_neg (fun h' => h h'.2), zero_div]

theorem Kp_pos (b : ℕ) (y : ℝ) : 0 < Kp b y := by
  unfold Kp; apply prod_pos; intro q _
  have : 0 ≤ rhoB b q / q := by unfold rhoB; split_ifs <;> positivity
  linarith

theorem Kp_mul_VB_le_one (b : ℕ) (y : ℝ) : Kp b y * MT.VB b y ≤ 1 := by
  unfold Kp MT.VB
  rw [← prod_mul_distrib]
  apply prod_le_one₀
  · intro q hq
    rw [rhoB_div_eq_gB b (primes_PB y q hq)]
    have h1 := MT.gB_nonneg b q
    have h2 := E1.gB_le_half' b q
    nlinarith
  · intro q hq
    rw [rhoB_div_eq_gB b (primes_PB y q hq)]
    have h1 := MT.gB_nonneg b q
    nlinarith

theorem Kp_le_inv_VB (b : ℕ) (y : ℝ) (hV : 0 < MT.VB b y) : Kp b y ≤ 1 / MT.VB b y := by
  rw [le_div_iff₀ hV]; exact Kp_mul_VB_le_one b y

theorem Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf
  split_ifs with h1 h2 h3
  · exact le_rfl
  · push_neg at h1
    exact le_min (by unfold kSq; positivity) (by linarith)
  · push_neg at h1 h2; unfold mm at *; linarith
  · unfold W1; norm_num

theorem wy_nonneg (y : ℝ) (p : ℕ) : 0 ≤ wy y p := Wf_nonneg _

theorem Wf_le_one (t : ℝ) : Wf t ≤ 1 := by
  unfold Wf
  split_ifs with h1 h2 h3
  · norm_num
  · push_neg at h1
    exact le_trans (min_le_right _ _) (by unfold mm at *; linarith)
  · unfold mm UU at *; linarith
  · unfold W1; norm_num

/-- `Σ_{p prime, y^m < p < X} p^{−2} ≤ 2 y^{−m}`. -/
theorem sum_inv_sq_primes {y X : ℝ} (hy : 1 < y) :
    ∑ p ∈ (primesBelow X).filter (fun p : ℕ => y ^ mm < (p : ℝ)), 1 / ((p : ℝ) ^ 2) ≤ 2 / y ^ mm := by
  set k := ⌊y ^ mm⌋₊ with hk
  set n := ⌈X⌉₊ + 1 with hn
  have hsub : (primesBelow X).filter (fun p : ℕ => y ^ mm < (p : ℝ)) ⊆ Ioo k n := by
    intro p hp
    rw [mem_filter, mem_primesBelow] at hp
    rw [mem_Ioo]
    constructor
    · have : (k : ℝ) < p := lt_of_le_of_lt (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) hp.2
      exact_mod_cast this
    · have : (p : ℝ) < n := by
        rw [hn]; push_cast; linarith [Nat.le_ceil X, hp.1.2]
      exact_mod_cast this
  have hpos : 0 < y ^ mm := Real.rpow_pos_of_pos (by linarith) _
  calc ∑ p ∈ (primesBelow X).filter (fun p : ℕ => y ^ mm < (p : ℝ)), 1 / ((p : ℝ) ^ 2)
      ≤ ∑ i ∈ Ioo k n, ((i : ℝ) ^ 2)⁻¹ := by
        simp only [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / (k + 1) := sum_Ioo_inv_sq_le k n
    _ ≤ 2 / y ^ mm := by
        apply div_le_div_of_nonneg_left (by norm_num) hpos
        exact (Nat.lt_floor_add_one _).le

/-- §4.6 asymptotics: `Σ_{y^m < p < y^{1/4}} w(p) K(y)³/p² ≤ ε V(y)` for large `y`. -/
theorem X_sum (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
      wy y p * (Kp b y ^ 3 / (p : ℝ) ^ 2) ≤ ε * MT.VB b y := by
  obtain ⟨x₀, hx₀, hV⟩ := E1.VB_log_ge_half b hb
  set κ := MT.kappaB b with hκ
  have hκ0 : 0 < κ := MT.kappaB_pos b
  set L₀ := 3840 / (κ ^ 4 * mm ^ 5 * ε) with hL₀
  refine ⟨max x₀ (Real.exp L₀), fun y hy => ?_⟩
  have hyx : x₀ ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 < y := lt_of_lt_of_le hx₀ hyx
  have hL : L₀ ≤ Real.log y := by
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hy)
  set L := Real.log y with hLdef
  have hLpos : 0 < L := Real.log_pos hy1
  have hVL := hV y hyx
  have hV0 : 0 < MT.VB b y := by
    by_contra h; push_neg at h; nlinarith
  have hK := Kp_le_inv_VB b y hV0
  have hK0 := Kp_pos b y
  have hm0 : (0 : ℝ) < mm := by unfold mm; norm_num
  -- step 1: drop w ≤ 1, pull out K³
  have h1 : ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
      wy y p * (Kp b y ^ 3 / (p : ℝ) ^ 2) ≤ Kp b y ^ 3 * (2 / y ^ mm) := by
    calc _ ≤ ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
          Kp b y ^ 3 * (1 / (p : ℝ) ^ 2) := by
          apply sum_le_sum; intro p _
          have hw0 := wy_nonneg y p
          have hw1 : wy y p ≤ 1 := Wf_le_one _
          have : 0 ≤ Kp b y ^ 3 / (p : ℝ) ^ 2 := by positivity
          calc wy y p * (Kp b y ^ 3 / (p : ℝ) ^ 2) ≤ 1 * (Kp b y ^ 3 / (p : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right hw1 this
            _ = Kp b y ^ 3 * (1 / (p : ℝ) ^ 2) := by ring
      _ = Kp b y ^ 3 * ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
          1 / (p : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ Kp b y ^ 3 * (2 / y ^ mm) := mul_le_mul_of_nonneg_left (sum_inv_sq_primes hy1) (by positivity)
  refine le_trans h1 ?_
  -- step 2: y^m ≥ (mL)^5/120
  have hexp : (mm * L) ^ 5 / 120 ≤ y ^ mm := by
    have := Real.pow_div_factorial_le_exp (mm * L) (by positivity) 5
    rw [show (Nat.factorial 5 : ℝ) = 120 by norm_num [Nat.factorial]] at this
    rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log y) mm]; exact this
  have hym : 0 < y ^ mm := Real.rpow_pos_of_pos (by linarith) _
  -- step 3: K ≤ 1/V ≤ 2L/κ
  have hKL : Kp b y ≤ 2 * L / κ := by
    refine le_trans hK ?_
    rw [div_le_div_iff₀ hV0 hκ0]; nlinarith
  have hVlow : κ / (2 * L) ≤ MT.VB b y := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hK3 : Kp b y ^ 3 ≤ (2 * L / κ) ^ 3 := pow_le_pow_left₀ hK0.le hKL 3
  calc Kp b y ^ 3 * (2 / y ^ mm) ≤ (2 * L / κ) ^ 3 * (2 / ((mm * L) ^ 5 / 120)) := by
        apply mul_le_mul hK3 _ (by positivity) (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hexp
    _ = ε * (κ / (2 * L)) * (3840 / (κ ^ 4 * mm ^ 5 * ε * L)) := by
        field_simp; ring
    _ ≤ ε * (κ / (2 * L)) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by positivity)]
        have : 3840 / (κ ^ 4 * mm ^ 5 * ε) ≤ L := hL
        rw [div_le_iff₀ (by positivity)] at this; nlinarith
    _ ≤ ε * MT.VB b y := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hVlow hε.le

end KappaOmega2.M10
