import Palprimes.TL1.Majorant

/-! # Orthogonality for products of block majorants (dossier Lemmas 2.7, 2.7′, 2.8)

`Σ_{q∈Qs} Σ_{h<q} Π_{r<R} T(b^{s_r}α, b^{e_r}α) ≤ (Σ q) T₀₀^R + 2R₀·T_div·A^R` at `α = h/q + β`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

variable {b l : ℕ}

theorem prod_Tc_expand (M : BlockMaj b l) (N R : ℕ) (α : ℝ) :
    ∏ r : Fin R, Tc M.S M.τ ((b : ℝ) ^ sB l r * α) ((b : ℝ) ^ eB N l r * α) =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin R => M.S),
        (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * α) := by
  unfold Tc
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib, ← ee_sum]
  congr 2
  unfold Wf
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro r _
  ring

theorem sum_h_prod_Tc (M : BlockMaj b l) (N R q : ℕ) (hq : 0 < q) (β : ℝ) :
    ∑ h ∈ range q, ∏ r : Fin R,
        Tc M.S M.τ ((b : ℝ) ^ sB l r * ((h : ℝ) / q + β)) ((b : ℝ) ^ eB N l r * ((h : ℝ) / q + β)) =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin R => M.S),
        (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
          (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0) := by
  simp_rw [prod_Tc_expand M N R]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← sum_ee_root q hq (Wf b N l R f), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [mul_assoc, ← ee_add]
  congr 2
  field_simp
  ring

theorem abs_Wf_le (N R : ℕ) (hb : 1 ≤ b) (hR : l * R + 1 ≤ N)
    (f : Fin R → ℤ × ℤ) (hf : ∀ r, |(f r).1| < (b : ℤ) ^ l ∧ |(f r).2| < (b : ℤ) ^ l) :
    |Wf b N l R f| ≤ (R : ℤ) * (2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N))) := by
  unfold Wf
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
  calc |∑ r : Fin R, ((f r).1 * (b : ℤ) ^ sB l r + (f r).2 * (b : ℤ) ^ eB N l r)|
      ≤ ∑ r : Fin R, |((f r).1 * (b : ℤ) ^ sB l r + (f r).2 * (b : ℤ) ^ eB N l r)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin R, 2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N)) := by
        apply Finset.sum_le_sum; intro r _
        have hs : sB l r ≤ 2 * N := by
          have : l * (r : ℕ) ≤ l * R := Nat.mul_le_mul_left _ r.2.le
          simp only [sB]; omega
        have he : eB N l r ≤ 2 * N := by simp only [eB]; omega
        have h1 : |(f r).1 * (b : ℤ) ^ sB l r| ≤ (b : ℤ) ^ l * (b : ℤ) ^ (2 * N) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (b : ℤ) ^ sB l r)]
          exact mul_le_mul (hf r).1.le (pow_le_pow_right₀ hb1 hs) (by positivity) (by positivity)
        have h2 : |(f r).2 * (b : ℤ) ^ eB N l r| ≤ (b : ℤ) ^ l * (b : ℤ) ^ (2 * N) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (b : ℤ) ^ eB N l r)]
          exact mul_le_mul (hf r).2.le (pow_le_pow_right₀ hb1 he) (by positivity) (by positivity)
        calc _ ≤ |(f r).1 * (b : ℤ) ^ sB l r| + |(f r).2 * (b : ℤ) ^ eB N l r| := abs_add_le _ _
          _ ≤ _ := by linarith
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem Wf_zero (N R : ℕ) : Wf b N l R 0 = 0 := by simp [Wf]

/-- **Averaged majorant moment** (dossier Lemma 2.8). -/
theorem majorant_sum_le (M : BlockMaj b l) (hb : 2 ≤ b) (hl : 1 ≤ l) (N R : ℕ) (hR : l * R + 1 ≤ N)
    (Qs : Finset ℕ) (R0 : ℝ) (hR0 : 0 ≤ R0) (hQ : ∀ q ∈ Qs, 0 < q ∧ (q : ℝ) ≤ 2 * R0)
    (Tdiv : ℝ) (hT0 : 0 ≤ Tdiv)
    (hT : ∀ w : ℤ, w ≠ 0 → |w| ≤ (R : ℤ) * (2 * ((b : ℤ) ^ l * (b : ℤ) ^ (2 * N))) →
      (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ w)) : ℝ) ≤ Tdiv) (β : ℝ) :
    ∑ q ∈ Qs, ∑ h ∈ range q, ∏ r : Fin R,
        Tval M.S M.τ ((b : ℝ) ^ sB l r * ((h : ℝ) / q + β)) ((b : ℝ) ^ eB N l r * ((h : ℝ) / q + β)) ≤
      (∑ q ∈ Qs, (q : ℝ)) * M.t00 ^ R + 2 * R0 * Tdiv * M.A ^ R := by
  classical
  set P := Fintype.piFinset (fun _ : Fin R => M.S) with hP
  have hfS : ∀ f ∈ P, ∀ r, f r ∈ M.S := fun f hf r => Fintype.mem_piFinset.1 hf r
  have h0P : (0 : Fin R → ℤ × ℤ) ∈ P := Fintype.mem_piFinset.2 (fun _ => M.h00)
  -- complex form of the left side
  set G : ℕ → ℂ := fun q => ∑ f ∈ P, (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
          (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0) with hG
  have hL : ∀ q ∈ Qs, ((∑ h ∈ range q, ∏ r : Fin R,
        Tval M.S M.τ ((b : ℝ) ^ sB l r * ((h : ℝ) / q + β)) ((b : ℝ) ^ eB N l r * ((h : ℝ) / q + β)) : ℝ) : ℂ)
        = G q := by
    intro q hq
    simp only [hG, hP]
    rw [← sum_h_prod_Tc M N R q (hQ q hq).1 β]
    push_cast
    apply Finset.sum_congr rfl; intro h _
    apply Finset.prod_congr rfl; intro r _
    rw [Tc_eq_Tval M.S M.τ M.hneg M.hsym]
  -- split off `f = 0`
  have hsplit : ∀ q ∈ Qs, G q = (q : ℂ) * (M.t00 : ℂ) ^ R + ∑ f ∈ P.erase 0,
      (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
        (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0) := by
    intro q _
    simp only [hG]
    rw [← Finset.add_sum_erase _ _ h0P, Wf_zero]
    simp [BlockMaj.t00, ee_zero, mul_comm, Prod.mk_zero_zero]
  have hbound : ∀ f ∈ P.erase 0,
      ‖∑ q ∈ Qs, (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
        (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0)‖ ≤
        (∏ r, |M.τ (f r)|) * (2 * R0 * Tdiv) := by
    intro f hf
    have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
    have hfP := Finset.mem_of_mem_erase hf
    have hW : Wf b N l R f ≠ 0 := W_ne_zero b N l R hb hl hR f (fun r => M.hS _ (hfS f hfP r)) hfne
    have hWle := abs_Wf_le N R (by omega : 1 ≤ b) hR f (fun r => M.hS _ (hfS f hfP r))
    rw [← Finset.mul_sum]
    rw [norm_mul, norm_mul, norm_ee, mul_one, norm_prod]
    simp_rw [Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖∑ q ∈ Qs, (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0)‖
        ≤ ∑ q ∈ Qs, ‖(if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Qs.filter (fun q : ℕ => (q : ℤ) ∣ Wf b N l R f), 2 * R0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum; intro q hq
          split_ifs
          · rw [Complex.norm_natCast]; exact (hQ q hq).2
          · simp
      _ = (#(Qs.filter (fun q : ℕ => (q : ℤ) ∣ Wf b N l R f)) : ℝ) * (2 * R0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Tdiv * (2 * R0) :=
          mul_le_mul_of_nonneg_right (hT _ hW hWle) (by linarith)
      _ = _ := by ring
  -- assemble
  have hLre : ∑ q ∈ Qs, ∑ h ∈ range q, ∏ r : Fin R,
        Tval M.S M.τ ((b : ℝ) ^ sB l r * ((h : ℝ) / q + β)) ((b : ℝ) ^ eB N l r * ((h : ℝ) / q + β)) =
      (∑ q ∈ Qs, G q).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro q hq
    rw [← hL q hq, Complex.ofReal_re]
  rw [hLre, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Complex.add_re]
  have hfirst : (∑ q ∈ Qs, (q : ℂ) * (M.t00 : ℂ) ^ R).re = (∑ q ∈ Qs, (q : ℝ)) * M.t00 ^ R := by
    have e : (∑ q ∈ Qs, (q : ℂ) * (M.t00 : ℂ) ^ R) = (((∑ q ∈ Qs, (q : ℝ)) * M.t00 ^ R : ℝ) : ℂ) := by
      push_cast; rw [Finset.sum_mul]
    rw [e, Complex.ofReal_re]
  rw [hfirst]
  have hA : (∑ f ∈ P, ∏ r, |M.τ (f r)|) = M.A ^ R := by
    rw [hP, ← Finset.prod_univ_sum (fun _ : Fin R => M.S) (fun _ w => |M.τ w|)]
    simp [BlockMaj.A]
  have hrest : (∑ q ∈ Qs, ∑ f ∈ P.erase 0, (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
        (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0)).re ≤ 2 * R0 * Tdiv * M.A ^ R := by
    rw [Finset.sum_comm]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ f ∈ P.erase 0, ‖∑ q ∈ Qs, (∏ r, (M.τ (f r) : ℂ)) * ee ((Wf b N l R f : ℝ) * β) *
          (if (q : ℤ) ∣ Wf b N l R f then (q : ℂ) else 0)‖
        ≤ ∑ f ∈ P.erase 0, (∏ r, |M.τ (f r)|) * (2 * R0 * Tdiv) := Finset.sum_le_sum hbound
      _ ≤ ∑ f ∈ P, (∏ r, |M.τ (f r)|) * (2 * R0 * Tdiv) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => mul_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
              (by have := hT0; positivity))
      _ = 2 * R0 * Tdiv * M.A ^ R := by rw [← Finset.sum_mul, hA]; ring
  linarith

end Palprimes
