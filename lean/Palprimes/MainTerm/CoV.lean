import Palprimes.MainTerm.AeCont
import Palprimes.MainTerm.PrimeRiemann

/-! # Change of variables `x = e^σ` on the boxes `(log a, 0]^r`

`box_cov`: `∫_{(log a, 0]^r} f = ∫_{(a, 1]^r} f(log x) / Π x_i`, and the integrability transfer. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Palprimes.MT

/-- Componentwise exponential. -/
noncomputable def expv {m : ℕ} (σ : Fin m → ℝ) : Fin m → ℝ := fun i => Real.exp (σ i)

noncomputable def dexpv {m : ℕ} (σ : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun i => Real.exp (σ i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)

theorem hasFDerivAt_expv {m : ℕ} (σ : Fin m → ℝ) : HasFDerivAt expv (dexpv σ) σ := by
  unfold expv dexpv
  rw [hasFDerivAt_pi]
  intro i
  exact (Real.hasDerivAt_exp (σ i)).comp_hasFDerivAt σ (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin m => ℝ) i σ)

theorem det_dexpv {m : ℕ} (σ : Fin m → ℝ) : (dexpv σ).det = ∏ i, Real.exp (σ i) := by
  have h : ((dexpv σ : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
      Matrix.toLin' (Matrix.diagonal (fun i => Real.exp (σ i))) := by
    ext v i
    simp [dexpv, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [ContinuousLinearMap.det, h, LinearMap.det_toLin', Matrix.det_diagonal]

theorem expv_injective {m : ℕ} : Function.Injective (expv (m := m)) := by
  intro σ τ h; funext i; exact Real.exp_injective (congr_fun h i)

theorem logv_expv {m : ℕ} (σ : Fin m → ℝ) : logv (expv σ) = σ := by
  funext i; simp [logv, expv]

theorem expv_logv {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 < x i) : expv (logv x) = x := by
  funext i; simp [logv, expv, Real.exp_log (hx i)]

theorem expv_image_box (r : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    expv '' (boxA r a ha0 ha1 : Set (Fin r → ℝ)) = Set.pi Set.univ (fun _ => Set.Ioc a 1) := by
  rw [Box.coe_eq_pi]
  ext x
  simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc]
  constructor
  · rintro ⟨σ, hσ, rfl⟩ i
    obtain ⟨h1, h2⟩ := hσ i
    have h1' : Real.log a < σ i := h1
    have h2' : σ i ≤ 0 := h2
    constructor
    · calc a = Real.exp (Real.log a) := (Real.exp_log ha0).symm
        _ < Real.exp (σ i) := Real.exp_lt_exp.2 h1'
    · calc Real.exp (σ i) ≤ Real.exp 0 := Real.exp_le_exp.2 h2'
        _ = 1 := Real.exp_zero
  · intro hx
    have hpos : ∀ i, 0 < x i := fun i => lt_trans ha0 (hx i).1
    refine ⟨logv x, fun i => ⟨?_, ?_⟩, expv_logv x hpos⟩
    · show Real.log a < Real.log (x i)
      exact Real.log_lt_log ha0 (hx i).1
    · show Real.log (x i) ≤ 0
      exact Real.log_nonpos (hpos i).le (hx i).2

theorem box_cov (r : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (f : (Fin r → ℝ) → ℝ) :
    ∫ σ in (boxA r a ha0 ha1 : Set (Fin r → ℝ)), f σ =
      ∫ x in Set.pi Set.univ (fun _ => Set.Ioc a 1), f (logv x) / ∏ i, x i := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume (boxA r a ha0 ha1).measurableSet_coe
    (fun σ _ => (hasFDerivAt_expv σ).hasFDerivWithinAt) expv_injective.injOn
    (fun x => f (logv x) / ∏ i, x i)
  rw [expv_image_box] at h
  rw [h]
  apply setIntegral_congr_fun (boxA r a ha0 ha1).measurableSet_coe
  intro σ _
  have hP : 0 < ∏ i, Real.exp (σ i) := Finset.prod_pos (fun i _ => Real.exp_pos _)
  simp only [det_dexpv, logv_expv, smul_eq_mul, abs_of_pos hP]
  unfold expv
  field_simp

theorem box_cov_integrable (r : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (f : (Fin r → ℝ) → ℝ)
    (hf : IntegrableOn f (boxA r a ha0 ha1 : Set (Fin r → ℝ))) :
    IntegrableOn (fun x => f (logv x) / ∏ i, x i) (Set.pi Set.univ (fun _ => Set.Ioc a 1)) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (boxA r a ha0 ha1).measurableSet_coe
    (fun σ _ => (hasFDerivAt_expv σ).hasFDerivWithinAt) expv_injective.injOn
    (fun x => f (logv x) / ∏ i, x i)
  rw [expv_image_box] at h
  rw [h]
  refine hf.congr_fun (fun σ _ => ?_) (boxA r a ha0 ha1).measurableSet_coe
  have hP : 0 < ∏ i, Real.exp (σ i) := Finset.prod_pos (fun i _ => Real.exp_pos _)
  simp only [det_dexpv, logv_expv, smul_eq_mul, abs_of_pos hP]
  unfold expv
  field_simp

end Palprimes.MT
