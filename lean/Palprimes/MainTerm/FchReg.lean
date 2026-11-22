import Palprimes.MainTerm.Regular
import Palprimes.MainTerm.Tuples3

/-! # `fch` and `fbig`: explicit form, a.e. continuity, measurability, bounds -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Palprimes.MT

open Palprimes.Greaves

/-- The condition of `fch`. -/
def Cch (n : ℕ) (σ : Fin (n + 1) → ℝ) : Prop :=
  StrictAnti σ ∧ (∀ j ∈ Finset.Icc 1 ((n + 1) / 2), ∑ i : Fin (n + 1), rc j i * Real.exp (σ i) ≤ 1) ∧
    Real.exp (σ (Fin.last n)) < 1 / 2

/-- The value of `fch` on its condition. -/
noncomputable def gch (P : WPar) (n : ℕ) (σ : Fin (n + 1) → ℝ) : ℝ :=
  (-1) ^ n * P.W (Real.exp (σ (Fin.last n))) *
    Gs (stF false (n + 1)) ((1 - ∑ i, Real.exp (σ i)) / Real.exp (σ (Fin.last n))) / Real.exp (σ (Fin.last n))

theorem fch_eq (P : WPar) (n : ℕ) (σ : Fin (n + 1) → ℝ) :
    fch P n σ = open Classical in if Cch n σ then gch P n σ else 0 := by
  classical
  unfold fch PhiL Cch gch
  rw [getLastD_ofFn, List.length_ofFn, List.sum_ofFn, RosX_ofFn_iff, Nat.add_sub_cancel]
  by_cases h1 : StrictAnti σ
  · rw [if_pos h1]
    by_cases h2 : (∀ j ∈ Finset.Icc 1 ((n + 1) / 2), ∑ i : Fin (n + 1), rc j i * Real.exp (σ i) ≤ 1) ∧
        Real.exp (σ (Fin.last n)) < 1 / 2
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem sum_single_exp {m : ℕ} (k : Fin m) (σ : Fin m → ℝ) :
    ∑ i, (if i = k then (1 : ℝ) else 0) * Real.exp (σ i) = Real.exp (σ k) := by
  simp [ite_mul]

/-- The finite bad set of `fch`. -/
noncomputable def Bch (P : WPar) (n : ℕ) : Finset ((Fin (n + 1) → ℝ) × ℝ) :=
  (((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun ij => ij.1 < ij.2)).image
      (fun ij => (fun k => (if k = ij.1 then (1 : ℝ) else 0) - (if k = ij.2 then 1 else 0), (0 : ℝ)))) ∪
  ((Finset.Icc 1 ((n + 1) / 2)).image (fun j => (fun k : Fin (n + 1) => rc j k, (1 : ℝ)))) ∪
  (({1 / 2, P.T0, 1 / 4, P.U} : Finset ℝ).image (fun c => (fun k => if k = Fin.last n then (1 : ℝ) else 0, c))) ∪
  {(fun k => 1 + if k = Fin.last n then (1 : ℝ) else 0, (1 : ℝ))}

theorem Bch_ne (P : WPar) (n : ℕ) : ∀ p ∈ Bch P n, p.1 ≠ 0 := by
  intro p hp
  unfold Bch at hp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_Icc] at hp
  rcases hp with ((⟨ij, hij, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨c, _, rfl⟩) | rfl
  · intro h; have := congr_fun h ij.1; simp [hij.ne] at this
  · intro h
    have h2 : 2 * j - 1 < n + 1 := by omega
    have := congr_fun h ⟨2 * j - 1, h2⟩
    simp [rc] at this
  · intro h; have := congr_fun h (Fin.last n); simp at this
  · intro h; have := congr_fun h (Fin.last n); norm_num at this

theorem fch_continuousAt (P : WPar) (n : ℕ) (σ0 : Fin (n + 1) → ℝ)
    (hg : ∀ p ∈ Bch P n, ∑ i, p.1 i * Real.exp (σ0 i) ≠ p.2) : ContinuousAt (fch P n) σ0 := by
  classical
  set L := Fin.last n
  have mem1 : ∀ i j : Fin (n + 1), i < j → ((fun k => (if k = i then (1 : ℝ) else 0) - (if k = j then 1 else 0)), (0 : ℝ)) ∈ Bch P n := by
    intro i j hij; unfold Bch
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    left; left; left; exact ⟨(i, j), hij, rfl⟩
  have mem2 : ∀ j ∈ Finset.Icc 1 ((n + 1) / 2), ((fun k : Fin (n + 1) => rc j k), (1 : ℝ)) ∈ Bch P n := by
    intro j hj; unfold Bch
    simp only [Finset.mem_union, Finset.mem_image]
    left; left; right; exact ⟨j, hj, rfl⟩
  have mem3 : ∀ c ∈ ({1 / 2, P.T0, 1 / 4, P.U} : Finset ℝ), ((fun k => if k = L then (1 : ℝ) else 0), c) ∈ Bch P n := by
    intro c hc; unfold Bch
    simp only [Finset.mem_union, Finset.mem_image]
    left; right; exact ⟨c, hc, rfl⟩
  have mem4 : ((fun k => 1 + if k = L then (1 : ℝ) else 0), (1 : ℝ)) ∈ Bch P n := by
    unfold Bch; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  -- consequences at `σ0`
  have hdist : ∀ i j : Fin (n + 1), i < j → σ0 j - σ0 i ≠ 0 := by
    intro i j hij h
    have := hg _ (mem1 i j hij)
    simp only [sub_mul, Finset.sum_sub_distrib, sum_single_exp] at this
    apply this; rw [show σ0 j = σ0 i by linarith]; ring
  have hros : ∀ j ∈ Finset.Icc 1 ((n + 1) / 2), ∑ i : Fin (n + 1), rc j i * Real.exp (σ0 i) ≠ 1 :=
    fun j hj => hg _ (mem2 j hj)
  have hlast : ∀ c ∈ ({1 / 2, P.T0, 1 / 4, P.U} : Finset ℝ), Real.exp (σ0 L) ≠ c := by
    intro c hc
    have := hg _ (mem3 c hc)
    rwa [sum_single_exp] at this
  have hsum : ∑ i, Real.exp (σ0 i) + Real.exp (σ0 L) ≠ 1 := by
    have := hg _ mem4
    simp only [add_mul, one_mul, Finset.sum_add_distrib, sum_single_exp] at this
    exact this
  have hx0 : 0 < Real.exp (σ0 L) := Real.exp_pos _
  have cL : Continuous (fun σ : Fin (n + 1) → ℝ => Real.exp (σ L)) := Real.continuous_exp.comp (continuous_apply L)
  have cS : Continuous (fun σ : Fin (n + 1) → ℝ => ∑ i, Real.exp (σ i)) :=
    continuous_finsetSum _ (fun i _ => Real.continuous_exp.comp (continuous_apply i))
  have cR : ∀ j : ℕ, Continuous (fun σ : Fin (n + 1) → ℝ => ∑ i : Fin (n + 1), rc j i * Real.exp (σ i)) := fun j =>
    continuous_finsetSum _ (fun i _ => continuous_const.mul (Real.continuous_exp.comp (continuous_apply i)))
  apply continuousAt_ite_of_eventually (fch P n) (gch P n) (Cch n) σ0 (fun σ => fch_eq P n σ)
  · -- the condition is locally constant
    have hSA : ∀ᶠ σ in 𝓝 σ0, ∀ i j : Fin (n + 1), i < j → (σ j - σ i < 0 ↔ σ0 j - σ0 i < 0) := by
      rw [Filter.eventually_all]; intro i
      rw [Filter.eventually_all]; intro j
      by_cases hij : i < j
      · filter_upwards [eventually_lt_iff (fun σ : Fin (n + 1) → ℝ => σ j - σ i) σ0
          ((continuous_apply j).sub (continuous_apply i)).continuousAt 0 (hdist i j hij)] with σ h _
        exact h
      · exact Filter.Eventually.of_forall (fun σ h => absurd h hij)
    have hR : ∀ᶠ σ in 𝓝 σ0, ∀ j ∈ Finset.Icc 1 ((n + 1) / 2),
        (∑ i : Fin (n + 1), rc j i * Real.exp (σ i) ≤ 1 ↔ ∑ i : Fin (n + 1), rc j i * Real.exp (σ0 i) ≤ 1) := by
      rw [Filter.eventually_all_finset]
      intro j hj
      exact eventually_le_iff (fun σ : Fin (n + 1) → ℝ => ∑ i : Fin (n + 1), rc j i * Real.exp (σ i)) σ0
        (cR j).continuousAt 1 (hros j hj)
    have hL : ∀ᶠ σ in 𝓝 σ0, (Real.exp (σ L) < 1 / 2 ↔ Real.exp (σ0 L) < 1 / 2) :=
      eventually_lt_iff (fun σ : Fin (n + 1) → ℝ => Real.exp (σ L)) σ0 cL.continuousAt (1 / 2)
        (hlast _ (by simp))
    filter_upwards [hSA, hR, hL] with σ h1 h2 h3
    unfold Cch
    have hsa : StrictAnti σ ↔ StrictAnti σ0 := by
      constructor
      · intro h i j hij; have := (h1 i j hij).1 (by linarith [h hij]); linarith
      · intro h i j hij; have := (h1 i j hij).2 (by linarith [h hij]); linarith
    rw [hsa, h3]
    apply and_congr_right; intro _
    apply and_congr_left; intro _
    constructor
    · intro h j hj; exact (h2 j hj).1 (h j hj)
    · intro h j hj; exact (h2 j hj).2 (h j hj)
  · -- the value is continuous
    intro _
    unfold gch
    have hW : ContinuousAt (fun σ : Fin (n + 1) → ℝ => P.W (Real.exp (σ L))) σ0 :=
      ContinuousAt.comp (g := P.W) (W_continuousAt P _ (hlast _ (by simp)) (hlast _ (by simp)) (hlast _ (by simp)))
        cL.continuousAt
    have hs1 : (1 - ∑ i, Real.exp (σ0 i)) / Real.exp (σ0 L) ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hx0.ne'] at h; apply hsum; linarith
    have hG : ContinuousAt (fun σ : Fin (n + 1) → ℝ =>
        Gs (stF false (n + 1)) ((1 - ∑ i, Real.exp (σ i)) / Real.exp (σ L))) σ0 :=
      ContinuousAt.comp (g := Gs (stF false (n + 1))) (Gs_continuousAt _ _ hs1)
        (ContinuousAt.div (continuous_const.sub cS).continuousAt cL.continuousAt hx0.ne')
    exact ((continuousAt_const.mul hW).mul hG).div cL.continuousAt hx0.ne'

theorem fch_ae_continuous (P : WPar) (n : ℕ) :
    ∀ᵐ σ ∂(volume : Measure (Fin (n + 1) → ℝ)), ContinuousAt (fch P n) σ :=
  ae_continuousAt_of_bad (fch P n) (Bch P n) (Bch_ne P n) (fch_continuousAt P n)

theorem fch_measurable (P : WPar) (n : ℕ) : Measurable (fch P n) := by
  classical
  have hC : MeasurableSet {σ : Fin (n + 1) → ℝ | Cch n σ} := by
    have cL : Continuous (fun σ : Fin (n + 1) → ℝ => Real.exp (σ (Fin.last n))) :=
      Real.continuous_exp.comp (continuous_apply _)
    have cR : ∀ j : ℕ, Continuous (fun σ : Fin (n + 1) → ℝ => ∑ i : Fin (n + 1), rc j i * Real.exp (σ i)) := fun j =>
      continuous_finsetSum _ (fun i _ => continuous_const.mul (Real.continuous_exp.comp (continuous_apply i)))
    apply measurableSet_setOfPred.2
    unfold Cch
    refine Measurable.and measurable_strictAnti (Measurable.and ?_ ?_)
    · refine Measurable.forall (fun j => measurable_const.imp ?_)
      exact measurable_le_fun (cR j).measurable measurable_const
    · exact measurable_lt_fun cL.measurable measurable_const
  have hg : Measurable (gch P n) := by
    unfold gch
    have cL : Continuous (fun σ : Fin (n + 1) → ℝ => Real.exp (σ (Fin.last n))) :=
      Real.continuous_exp.comp (continuous_apply _)
    have cS : Continuous (fun σ : Fin (n + 1) → ℝ => ∑ i, Real.exp (σ i)) :=
      continuous_finsetSum _ (fun i _ => Real.continuous_exp.comp (continuous_apply i))
    have hW : Measurable (fun σ : Fin (n + 1) → ℝ => P.W (Real.exp (σ (Fin.last n)))) :=
      (W_measurable P).comp cL.measurable
    have hG : Measurable (fun σ : Fin (n + 1) → ℝ =>
        Gs (stF false (n + 1)) ((1 - ∑ i, Real.exp (σ i)) / Real.exp (σ (Fin.last n)))) :=
      (Gs_measurable _).comp ((continuous_const.sub cS).measurable.div cL.measurable)
    exact ((measurable_const.mul hW).mul hG).div cL.measurable
  have : fch P n = fun σ => if Cch n σ then gch P n σ else 0 := funext (fch_eq P n)
  rw [this]
  exact Measurable.ite hC hg measurable_const

end Palprimes.MT
