import Palprimes.MainTerm.AeCont
import Palprimes.MainTerm.Approx3
import Palprimes.MainTerm.LogCoord

/-! # Regularity of the pieces of `fch`, `fbig`

* `W_mono`, `W_continuousAt` (off `{T₀, 1/4, U}`), `FjrC_continuousAt`, `Gs_continuousAt` (off `s = 1`),
  measurability of `W`, `FjrC`, `Gs`;
* `RosX_ofFn_iff`: Rosser's conditions on a tuple as finitely many linear inequalities `Σ_i rc j i x_i ≤ 1`. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology

namespace Palprimes.MT

open Palprimes.Greaves

theorem W_mono (P : WPar) : Monotone P.W := by
  intro s t hst
  have := P.V_lt; have := P.c_lt_T0; have := P.c_ge_V; have := P.hU; have := P.hT1; have := P.c_nonneg
  unfold WPar.W
  split_ifs <;> linarith

theorem W_measurable (P : WPar) : Measurable P.W := (W_mono P).measurable

theorem W_continuousAt (P : WPar) (t : ℝ) (h1 : t ≠ P.T0) (h2 : t ≠ 1 / 4) (h3 : t ≠ P.U) :
    ContinuousAt P.W t := by
  have := P.hU; have := P.hT1
  rcases lt_or_gt_of_ne h3 with hU | hU
  · rcases lt_or_gt_of_ne h2 with h4 | h4
    · rcases lt_or_gt_of_ne h1 with hT | hT
      · -- `t < T₀`: `W = 0`
        have : P.W =ᶠ[𝓝 t] fun _ => 0 := by
          filter_upwards [gt_mem_nhds hT] with s hs
          unfold WPar.W; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
        exact continuousAt_const.congr this.symm
      · -- `T₀ < t < 1/4`
        have : P.W =ᶠ[𝓝 t] fun s => s - P.c := by
          filter_upwards [lt_mem_nhds hT, gt_mem_nhds h4] with s hs1 hs2
          unfold WPar.W; rw [if_neg (by linarith), if_neg (by linarith), if_pos hs1]
        exact (continuousAt_id.sub continuousAt_const).congr this.symm
    · -- `1/4 < t < U`
      have : P.W =ᶠ[𝓝 t] fun s => s - P.V := by
        filter_upwards [lt_mem_nhds h4, gt_mem_nhds hU] with s hs1 hs2
        unfold WPar.W; rw [if_neg (by linarith), if_pos hs1]
      exact (continuousAt_id.sub continuousAt_const).congr this.symm
  · have : P.W =ᶠ[𝓝 t] fun _ => P.U - P.V := by
      filter_upwards [lt_mem_nhds hU] with s hs
      unfold WPar.W; rw [if_pos hs]
    exact continuousAt_const.congr this.symm

theorem FjrC_continuousAt (s : ℝ) (hs : s ≠ 1) : ContinuousAt FjrC s := by
  rcases lt_or_gt_of_ne hs with h | h
  · have : FjrC =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [gt_mem_nhds h] with u hu
      unfold FjrC; rw [if_neg hu.ne, Fjr_le_one hu.le]
    exact continuousAt_const.congr this.symm
  · have h1 : FjrC =ᶠ[𝓝 s] Fjr := by
      filter_upwards [lt_mem_nhds h] with u hu
      unfold FjrC; rw [if_neg hu.ne']
    exact (continuousOn_Fjr.continuousAt (Ioi_mem_nhds h)).congr h1.symm

theorem Gs_continuousAt (σ : Bool) (s : ℝ) (hs : s ≠ 1) : ContinuousAt (Gs σ) s := by
  cases σ with
  | true => exact FjrC_continuousAt s hs
  | false => exact continuous_fjr.continuousAt

theorem FjrC_measurable : Measurable FjrC := by
  apply measurable_of_continuousOn_compl_singleton 1
  intro s hs
  exact (FjrC_continuousAt s hs).continuousWithinAt

theorem Gs_measurable (σ : Bool) : Measurable (Gs σ) := by
  cases σ with
  | true => exact FjrC_measurable
  | false => exact continuous_fjr.measurable

/-! ## Rosser's conditions on tuples -/

/-- Rosser coefficients: `x_0 + ⋯ + x_{2j−2} + 3 x_{2j−1}`. -/
def rc (j k : ℕ) : ℝ := if k < 2 * j - 1 then 1 else if k = 2 * j - 1 then 3 else 0

theorem getD_ofFn {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    (List.ofFn x).getD k 0 = if h : k < n then x ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem sum_range_ite_lt (G : ℕ → ℝ) : ∀ (N m : ℕ), m ≤ N →
    ∑ k ∈ Finset.range N, (if k < m then G k else 0) = ∑ k ∈ Finset.range m, G k := by
  intro N
  induction N with
  | zero => intro m hm; have : m = 0 := by omega
            subst this; simp
  | succ N ih =>
    intro m hm
    rcases Nat.lt_or_ge N m with h | h
    · have hm' : m = N + 1 := by omega
      subst hm'
      apply Finset.sum_congr rfl
      intro k hk; rw [if_pos (Finset.mem_range.1 hk)]
    · rw [Finset.sum_range_succ, if_neg (by omega), add_zero, ih m h]

theorem rosser_lin {n : ℕ} (x : Fin (n + 1) → ℝ) (j : ℕ) (hj : 1 ≤ j) (h2 : 2 * j ≤ n + 1) :
    psum (List.ofFn x) (2 * j - 1) + 3 * (List.ofFn x).getD (2 * j - 1) 0 = ∑ i : Fin (n + 1), rc j i * x i := by
  set G : ℕ → ℝ := fun k => (List.ofFn x).getD k 0
  have hx : ∀ i : Fin (n + 1), x i = G i := by
    intro i; simp only [G]; rw [getD_ofFn, dif_pos i.2]
  have e1 : ∑ i : Fin (n + 1), rc j i * x i = ∑ k ∈ Finset.range (n + 1), rc j k * G k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => rc j k * G k)]
    apply Finset.sum_congr rfl; intro i _; rw [hx]
  have e2 : ∀ k, rc j k * G k = (if k < 2 * j - 1 then G k else 0) + (if k = 2 * j - 1 then 3 * G k else 0) := by
    intro k; unfold rc; split_ifs <;> first | omega | ring
  rw [e1, Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_add_distrib,
    sum_range_ite_lt G (n + 1) (2 * j - 1) (by omega), Finset.sum_ite_eq' (Finset.range (n + 1)),
    if_pos (Finset.mem_range.2 (by omega))]
  rfl

theorem RosX_ofFn_iff {n : ℕ} (x : Fin (n + 1) → ℝ) :
    RosX false 1 (List.ofFn x) ↔ ∀ j ∈ Finset.Icc 1 ((n + 1) / 2), ∑ i : Fin (n + 1), rc j i * x i ≤ 1 := by
  rw [RosX_false_iff]
  simp only [List.length_ofFn, Finset.mem_Icc]
  constructor
  · intro h j hj
    have h2 : 2 * j ≤ n + 1 := by omega
    rw [← rosser_lin x j hj.1 h2]; exact h j hj.1 h2
  · intro h j hj h2
    rw [rosser_lin x j hj h2]; exact h j ⟨hj, by omega⟩

end Palprimes.MT
