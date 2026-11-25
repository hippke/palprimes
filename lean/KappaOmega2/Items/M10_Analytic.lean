import KappaOmega2.Items.M10_Exact
import KappaOmega2.Items.M10_Rosser

/-!
# M10, analytic part (`M10_PLAN.md` §4): `|Σ_{p < y^{1/4}} w(p) Δ_p| ≤ ε V(y)` for large `y`

`Δ_p = L_p + X_p` with `L_p = −H_p − S_p` (Lemma 9 errors, §4.5) and `X_p = S_p − E_p` (terms with `(d₁, t) > 1`, §4.6),
`S_p` = `H_p` with every `T^±(y/(pd₁), p)` replaced by the Lemma 9 sum `R^±(y/(pd₁), p)`.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

/-- §4.5: the Lemma 9 errors (uses `Lemma9Stmt` through the uniform Claim U and Palprimes' Rosser and Mertens bounds). -/
theorem L_bound (b : ℕ) (hb : 2 ≤ b) (h9 : Lemma9Stmt b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
      wy y p * |-Hp b y p - Sp b y p| ≤ ε * MT.VB b y := by
  exact L_bound_of b hb (lemma9U_of b hb h9) ε hε

/-- §4.1 (ii) and §4.6: the coprime part of `S_p` is `E_p` (`Lemma10Stmt`), the rest is `O(y^{−m} log³ y)`. -/
theorem X_bound (b : ℕ) (hb : 2 ≤ b) (h10 : Lemma10LtStmt) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
      wy y p * |Sp b y p - Ep b y p| ≤ ε * MT.VB b y := by
  obtain ⟨y₁, hy₁⟩ := M10.X_sum b hb (ε / 2) (by linarith)
  refine ⟨max y₁ 16, fun y hy => ?_⟩
  have hy16 : (16 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  calc _ ≤ ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
        2 * (wy y p * (M10.Kp b y ^ 3 / (p : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum; intro p hp
        rw [Finset.mem_filter, mem_primesBelow] at hp
        rw [regroup b h10 hy16 hp.1.1 hp.1.2]
        have h := M10.Xd_bound b hy16 hp.1.1
        have hw := M10.wy_nonneg y p
        calc wy y p * |Xd b y p| ≤ wy y p * (2 * M10.Kp b y ^ 3 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h hw
          _ = 2 * (wy y p * (M10.Kp b y ^ 3 / (p : ℝ) ^ 2)) := by ring
    _ = 2 * ∑ p ∈ (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)),
        wy y p * (M10.Kp b y ^ 3 / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 2 * (ε / 2 * MT.VB b y) := by
        apply mul_le_mul_of_nonneg_left (hy₁ y (le_trans (le_max_left _ _) hy)) (by norm_num)
    _ = ε * MT.VB b y := by ring

/-- The analytic part. -/
theorem analytic_bound_U (b : ℕ) (hb : 2 ≤ b) (h9U : Lemma9UStmt b) (h10 : Lemma10LtStmt) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, |∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 4)), wy y p * DeltaP b y p| ≤ ε * MT.VB b y := by
  classical
  obtain ⟨y₁, hy₁⟩ := L_bound_of b hb h9U (ε / 2) (by linarith)
  obtain ⟨y₂, hy₂⟩ := X_bound b hb h10 (ε / 2) (by linarith)
  refine ⟨max (max y₁ y₂) 2, fun y hy => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hy2 : y₂ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hy3 : (1 : ℝ) < y := by linarith [le_trans (le_max_right _ _) hy]
  set F := (primesBelow (y ^ ((1 : ℝ) / 4))).filter (fun p : ℕ => y ^ mm < (p : ℝ)) with hF
  have hrestrict : ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 4)), wy y p * DeltaP b y p =
      ∑ p ∈ F, wy y p * DeltaP b y p := by
    rw [hF, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro p hp
    split_ifs with h
    · rfl
    · push_neg at h
      rw [wy_eq_zero hy3 ((mem_primesBelow _ p).1 hp).1.pos h, zero_mul]
  rw [hrestrict]
  calc |∑ p ∈ F, wy y p * DeltaP b y p|
      ≤ ∑ p ∈ F, |wy y p * DeltaP b y p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ F, (wy y p * |-Hp b y p - Sp b y p| + wy y p * |Sp b y p - Ep b y p|) := by
        apply Finset.sum_le_sum; intro p _
        rw [abs_mul, abs_of_nonneg (M10.wy_nonneg y p), ← mul_add]
        apply mul_le_mul_of_nonneg_left _ (M10.wy_nonneg y p)
        unfold DeltaP
        have : -Hp b y p - Ep b y p = (-Hp b y p - Sp b y p) + (Sp b y p - Ep b y p) := by ring
        rw [this]; exact abs_add_le _ _
    _ = ∑ p ∈ F, wy y p * |-Hp b y p - Sp b y p| + ∑ p ∈ F, wy y p * |Sp b y p - Ep b y p| :=
        Finset.sum_add_distrib
    _ ≤ ε / 2 * MT.VB b y + ε / 2 * MT.VB b y := add_le_add (hy₁ y hy1) (hy₂ y hy2)
    _ = ε * MT.VB b y := by ring

/-- The analytic part from the frozen hypotheses. -/
theorem analytic_bound (b : ℕ) (hb : 2 ≤ b) (h9 : Lemma9Stmt b) (h10 : Lemma10Stmt) (ε : ℝ) (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y ≥ y₀, |∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 4)), wy y p * DeltaP b y p| ≤ ε * MT.VB b y :=
  analytic_bound_U b hb (lemma9U_of b hb h9) (lemma10Lt_of h10) ε hε

end KappaOmega2
