import Palprimes.ExpSum.ColBound
import Palprimes.ExpSum.Farey

/-! # Block majorants (dossier §2.7)

* `Dfun b t = b⁻¹ Σ_{j<b} e(jt)`, `‖Dfun b t‖ = √ψ(t)`;
* `Gam b l x y = Π_{i<l} Dfun b (b^i x + b^{l-1-i} y)`, the `l`-digit block function;
* `block_eq`: `Π_{i<l} √ψ(c_{s+i} α) = ‖Gam b l (b^s α) (b^{2N-s-l+1} α)‖` for `s + l ≤ N`;
* `BlockMaj`: a symmetric trigonometric polynomial `T ≥ ‖Gam‖^p` with frequencies `|u|,|v| < b^l`;
* `W_ne_zero`: the frequency `Σ_r (u_r b^{1+lr} + v_r b^{2N-l(r+1)})` of a nonzero
  frequency vector is nonzero (dossier Lemma 2.7′). -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- `D_b(t) = b⁻¹ Σ_{j<b} e(jt)`. -/
noncomputable def Dfun (b : ℕ) (t : ℝ) : ℂ := ((b : ℂ))⁻¹ * ∑ j ∈ range b, ee (j * t)

theorem norm_Dfun (b : ℕ) (hb : 1 ≤ b) (t : ℝ) : ‖Dfun b t‖ = Real.sqrt (psiB b t) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  unfold Dfun psiB phiB
  rw [norm_mul, norm_inv, Complex.norm_natCast, Real.sqrt_sq (by positivity)]
  rw [inv_mul_eq_div]

theorem norm_Dfun_le_one (b : ℕ) (hb : 1 ≤ b) (t : ℝ) : ‖Dfun b t‖ ≤ 1 := by
  rw [norm_Dfun b hb, Real.sqrt_le_one]
  exact psiB_le_one b hb t

/-- The `l`-digit block function `Γ(x, y) = Π_{i<l} D_b(b^i x + b^{l-1-i} y)`. -/
noncomputable def Gam (b l : ℕ) (x y : ℝ) : ℂ :=
  ∏ i ∈ range l, Dfun b ((b : ℝ) ^ i * x + (b : ℝ) ^ (l - 1 - i) * y)

theorem norm_Gam_le_one (b l : ℕ) (hb : 1 ≤ b) (x y : ℝ) : ‖Gam b l x y‖ ≤ 1 := by
  unfold Gam
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => norm_Dfun_le_one b hb _)

/-- **Block identity**: `l` consecutive positions `s, …, s+l-1 < N` give one block factor. -/
theorem block_eq (b N l s : ℕ) (hb : 1 ≤ b) (hsl : s + l ≤ N) (α : ℝ) :
    ∏ i ∈ range l, Real.sqrt (psiB b (cK b N (s + i) * α)) =
      ‖Gam b l ((b : ℝ) ^ s * α) ((b : ℝ) ^ (2 * N - s - l + 1) * α)‖ := by
  unfold Gam
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [norm_Dfun b hb]
  congr 2
  have hk : s + i < N := by omega
  unfold cK
  rw [if_pos hk]
  push_cast
  have e1 : (b : ℝ) ^ (2 * N - (s + i)) = (b : ℝ) ^ (l - 1 - i) * (b : ℝ) ^ (2 * N - s - l + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e1, pow_add]
  ring

/-! ## Majorants -/

/-- The real trigonometric polynomial `T(x,y) = Σ_{w∈S} τ_w cos 2π(w₁x + w₂y)`. -/
noncomputable def Tval (S : Finset (ℤ × ℤ)) (τ : ℤ × ℤ → ℝ) (x y : ℝ) : ℝ :=
  ∑ w ∈ S, τ w * Real.cos (2 * π * ((w.1 : ℝ) * x + (w.2 : ℝ) * y))

/-- Its complex form `Σ_{w∈S} τ_w e(w₁x + w₂y)`. -/
noncomputable def Tc (S : Finset (ℤ × ℤ)) (τ : ℤ × ℤ → ℝ) (x y : ℝ) : ℂ :=
  ∑ w ∈ S, (τ w : ℂ) * ee ((w.1 : ℝ) * x + (w.2 : ℝ) * y)

/-- A block majorant of `‖Γ_l‖^p`: symmetric coefficients, frequencies below `b^l`. -/
structure BlockMaj (b l : ℕ) where
  S : Finset (ℤ × ℤ)
  τ : ℤ × ℤ → ℝ
  p : ℝ
  hp0 : 0 < p
  hp1 : p ≤ 1
  h00 : ((0 : ℤ), (0 : ℤ)) ∈ S
  hS : ∀ w ∈ S, |w.1| < (b : ℤ) ^ l ∧ |w.2| < (b : ℤ) ^ l
  hneg : ∀ w ∈ S, -w ∈ S
  hsym : ∀ w ∈ S, τ (-w) = τ w
  hmaj : ∀ x y : ℝ, ‖Gam b l x y‖ ^ p ≤ Tval S τ x y

/-- `T(0,0)`-coefficient and the `ℓ¹` norm of the coefficients. -/
def BlockMaj.t00 {b l : ℕ} (M : BlockMaj b l) : ℝ := M.τ (0, 0)
def BlockMaj.A {b l : ℕ} (M : BlockMaj b l) : ℝ := ∑ w ∈ M.S, |M.τ w|

theorem Tc_eq_Tval (S : Finset (ℤ × ℤ)) (τ : ℤ × ℤ → ℝ)
    (hneg : ∀ w ∈ S, -w ∈ S) (hsym : ∀ w ∈ S, τ (-w) = τ w) (x y : ℝ) :
    Tc S τ x y = (Tval S τ x y : ℂ) := by
  have hconj : starRingEnd ℂ (Tc S τ x y) = Tc S τ x y := by
    unfold Tc
    rw [map_sum]
    have h1 : ∑ w ∈ S, starRingEnd ℂ ((τ w : ℂ) * ee ((w.1 : ℝ) * x + (w.2 : ℝ) * y)) =
        ∑ w ∈ S, (τ w : ℂ) * ee (((-w).1 : ℝ) * x + ((-w).2 : ℝ) * y) := by
      apply Finset.sum_congr rfl; intro w _
      rw [map_mul, Complex.conj_ofReal, conj_ee]
      congr 2; push_cast [Prod.fst_neg, Prod.snd_neg]; ring
    rw [h1]
    -- now reindex by negation
    apply Finset.sum_nbij' (fun w => -w) (fun w => -w)
    · intro w hw; exact hneg w hw
    · intro w hw; exact hneg w hw
    · intro w _; exact neg_neg w
    · intro w _; exact neg_neg w
    · intro w hw
      rw [hsym w hw]
  have hreal : (Tc S τ x y).im = 0 := by
    have := congrArg Complex.im hconj
    rw [Complex.conj_im] at this
    linarith
  apply Complex.ext
  · rw [Complex.ofReal_re]
    unfold Tc Tval
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro w _
    rw [Complex.re_ofReal_mul, re_ee]
  · rw [Complex.ofReal_im, hreal]

/-! ## Nonvanishing of the frequency -/

/-- Lower and upper exponents of block `r`. -/
def sB (l r : ℕ) : ℕ := 1 + l * r
def eB (N l r : ℕ) : ℕ := 2 * N - l * (r + 1)

/-- The frequency `W_f = Σ_r (u_r b^{s_r} + v_r b^{e_r})`. -/
def Wf (b N l R : ℕ) (f : Fin R → ℤ × ℤ) : ℤ :=
  ∑ r : Fin R, ((f r).1 * (b : ℤ) ^ sB l r + (f r).2 * (b : ℤ) ^ eB N l r)

theorem not_dvd_small (b k : ℕ) (hb : 2 ≤ b) (u : ℤ) (hu0 : u ≠ 0) (hu : |u| < (b : ℤ) ^ k) (s : ℕ) :
    ¬ (b : ℤ) ^ (s + k) ∣ u * (b : ℤ) ^ s := by
  intro h
  rw [pow_add, mul_comm ((b : ℤ) ^ s)] at h
  have hbs : (b : ℤ) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : b ≠ 0))
  have h' : (b : ℤ) ^ k ∣ u := (mul_dvd_mul_iff_right hbs).1 h
  have := Int.le_of_dvd (abs_pos.2 hu0) ((dvd_abs _ _).2 h')
  linarith

/-- **Lemma 2.7′**: a nonzero frequency vector has nonzero frequency. -/
theorem W_ne_zero (b N l R : ℕ) (hb : 2 ≤ b) (hl : 1 ≤ l) (hR : l * R + 1 ≤ N)
    (f : Fin R → ℤ × ℤ) (hf : ∀ r, |(f r).1| < (b : ℤ) ^ l ∧ |(f r).2| < (b : ℤ) ^ l)
    (hne : f ≠ 0) : Wf b N l R f ≠ 0 := by
  classical
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  by_cases hu : ∃ r, (f r).1 ≠ 0
  · -- least `r0` with `u_{r0} ≠ 0`
    set U : Finset (Fin R) := univ.filter (fun r => (f r).1 ≠ 0) with hU
    have hUne : U.Nonempty := by
      obtain ⟨r, hr⟩ := hu; exact ⟨r, by simp [hU, hr]⟩
    set r0 := U.min' hUne with hr0
    have hr0U : r0 ∈ U := Finset.min'_mem U hUne
    have hu0 : (f r0).1 ≠ 0 := by simpa [hU] using hr0U
    set k := sB l r0 + l
    have hdiv : (b : ℤ) ^ k ∣ Wf b N l R f - (f r0).1 * (b : ℤ) ^ sB l r0 := by
      unfold Wf
      rw [← Finset.add_sum_erase _ _ (mem_univ r0)]
      have : ((f r0).1 * (b : ℤ) ^ sB l r0 + (f r0).2 * (b : ℤ) ^ eB N l r0 +
          ∑ r ∈ univ.erase r0, ((f r).1 * (b : ℤ) ^ sB l r + (f r).2 * (b : ℤ) ^ eB N l r)) -
          (f r0).1 * (b : ℤ) ^ sB l r0 =
          (f r0).2 * (b : ℤ) ^ eB N l r0 +
          ∑ r ∈ univ.erase r0, ((f r).1 * (b : ℤ) ^ sB l r + (f r).2 * (b : ℤ) ^ eB N l r) := by ring
      rw [this]
      have hr0R : (r0 : ℕ) < R := r0.2
      have hkN : k ≤ N := by
        simp only [k, sB]
        have : l * (r0 : ℕ) + l ≤ l * R := by nlinarith
        omega
      have hE : ∀ r : Fin R, k ≤ eB N l r := by
        intro r
        simp only [eB]
        have : l * ((r : ℕ) + 1) ≤ l * R := Nat.mul_le_mul_left _ r.2
        omega
      apply dvd_add
      · exact Dvd.dvd.mul_left (pow_dvd_pow _ (hE r0)) _
      · apply Finset.dvd_sum; intro r hr
        apply dvd_add
        · by_cases hzero : (f r).1 = 0
          · rw [hzero, zero_mul]; exact dvd_zero _
          · have hrU : r ∈ U := by simp [hU, hzero]
            have hle : r0 ≤ r := Finset.min'_le U r hrU
            have hne' : r ≠ r0 := Finset.ne_of_mem_erase hr
            have hlt : (r0 : ℕ) < r := lt_of_le_of_ne hle (fun h => hne' (Fin.ext h).symm)
            apply Dvd.dvd.mul_left
            apply pow_dvd_pow
            simp only [k, sB]
            have : l * ((r0 : ℕ) + 1) ≤ l * r := Nat.mul_le_mul_left _ hlt
            nlinarith
        · exact Dvd.dvd.mul_left (pow_dvd_pow _ (hE r)) _
    intro hW
    rw [hW, zero_sub, dvd_neg] at hdiv
    exact not_dvd_small b l hb _ hu0 (hf r0).1 _ hdiv
  · -- all `u_r = 0`: largest `r1` with `v_{r1} ≠ 0`
    push Not at hu
    have hv : ∃ r, (f r).2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      funext r
      exact Prod.ext (hu r) (h r)
    set V : Finset (Fin R) := univ.filter (fun r => (f r).2 ≠ 0) with hV
    have hVne : V.Nonempty := by
      obtain ⟨r, hr⟩ := hv; exact ⟨r, by simp [hV, hr]⟩
    set r1 := V.max' hVne with hr1
    have hr1V : r1 ∈ V := Finset.max'_mem V hVne
    have hv1 : (f r1).2 ≠ 0 := by simpa [hV] using hr1V
    set e := eB N l r1
    have hdiv : (b : ℤ) ^ (e + l) ∣ Wf b N l R f - (f r1).2 * (b : ℤ) ^ e := by
      unfold Wf
      rw [← Finset.add_sum_erase _ _ (mem_univ r1)]
      rw [hu r1, zero_mul, zero_add, add_sub_cancel_left]
      apply Finset.dvd_sum; intro r hr
      rw [hu r, zero_mul, zero_add]
      by_cases hzero : (f r).2 = 0
      · rw [hzero, zero_mul]; exact dvd_zero _
      · have hrV : r ∈ V := by simp [hV, hzero]
        have hle : r ≤ r1 := Finset.le_max' V r hrV
        have hne' : r ≠ r1 := Finset.ne_of_mem_erase hr
        have hlt : (r : ℕ) < r1 := lt_of_le_of_ne hle (fun h => hne' (Fin.ext h))
        apply Dvd.dvd.mul_left
        apply pow_dvd_pow
        simp only [e, eB]
        have h1 : l * ((r : ℕ) + 1) + l ≤ l * ((r1 : ℕ) + 1) := by nlinarith
        have h2 : l * ((r1 : ℕ) + 1) ≤ l * R := Nat.mul_le_mul_left _ r1.2
        omega
    intro hW
    rw [hW, zero_sub, dvd_neg] at hdiv
    exact not_dvd_small b l hb _ hv1 (hf r1).2 _ hdiv

end Palprimes
