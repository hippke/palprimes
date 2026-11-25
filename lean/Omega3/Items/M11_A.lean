import Omega3.Statements
import Palprimes.MainTerm.Identify
import Palprimes.MainTerm.Approx3
import Palprimes.MainTerm.Tuples
import Palprimes.Sieve.SelbergSum
import Palprimes.E1.Main

/-! # M11 helper (merged to keep the lake trace depth small): sections from the former files
M11_Gen, M11_Reg, M11_Int, M11_Tup, M11_Chain, M11_Snoc, M11_S3b, M11_Pieces, M11_Sig. -/

section

/-!
# M11 helper: functions cut out by finitely many linear conditions in the coordinates `x = e^σ`

`CndR Rl Rg x`: `Σ c_i x_i < d` for `(c, d) ∈ Rl` and `d ≤ Σ c_i x_i` for `(c, d) ∈ Rg`.
`fR Rl Rg G σ = [CndR (e^σ)] G(e^σ)`: a.e. continuous (Palprimes `ae_continuousAt_of_bad`) and measurable.
Also: `W` is continuous (`Wf = max 0 (min (min (k²t²) (t − m)) W(1))`).
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real MeasureTheory Filter Topology

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

/-- A linear form. -/
noncomputable def LF {m : ℕ} (c x : Fin m → ℝ) : ℝ := ∑ i, c i * x i

theorem LF_continuous {m : ℕ} (c : Fin m → ℝ) : Continuous (fun x : Fin m → ℝ => LF c x) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem LF_expv_continuous {m : ℕ} (c : Fin m → ℝ) : Continuous (fun σ : Fin m → ℝ => LF c (expv σ)) :=
  (LF_continuous c).comp (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i))

/-- The conditions. -/
def CndR {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (x : Fin m → ℝ) : Prop :=
  (∀ p ∈ Rl, LF p.1 x < p.2) ∧ (∀ p ∈ Rg, p.2 ≤ LF p.1 x)

/-- The cut-out function in log-log coordinates. -/
noncomputable def fR {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (G : (Fin m → ℝ) → ℝ) (σ : Fin m → ℝ) : ℝ :=
  open Classical in if CndR Rl Rg (expv σ) then G (expv σ) else 0

theorem cnd_eventually {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (σ0 : Fin m → ℝ)
    (hoff : ∀ p ∈ Rl ∪ Rg, LF p.1 (expv σ0) ≠ p.2) :
    ∀ᶠ σ in 𝓝 σ0, (CndR Rl Rg (expv σ) ↔ CndR Rl Rg (expv σ0)) := by
  have hl : ∀ p ∈ Rl, ∀ᶠ σ in 𝓝 σ0, (LF p.1 (expv σ) < p.2 ↔ LF p.1 (expv σ0) < p.2) := by
    intro p hp
    have hc := (LF_expv_continuous p.1).continuousAt (x := σ0)
    have hne := hoff p (mem_union_left _ hp)
    rcases lt_or_gt_of_ne hne with h | h
    · filter_upwards [hc.eventually (gt_mem_nhds h)] with σ hσ
      exact ⟨fun _ => h, fun _ => hσ⟩
    · filter_upwards [hc.eventually (lt_mem_nhds h)] with σ hσ
      exact ⟨fun h' => absurd h' (not_lt.2 hσ.le), fun h' => absurd h' (not_lt.2 h.le)⟩
  have hg : ∀ p ∈ Rg, ∀ᶠ σ in 𝓝 σ0, (p.2 ≤ LF p.1 (expv σ) ↔ p.2 ≤ LF p.1 (expv σ0)) := by
    intro p hp
    have hc := (LF_expv_continuous p.1).continuousAt (x := σ0)
    have hne := hoff p (mem_union_right _ hp)
    rcases lt_or_gt_of_ne hne with h | h
    · filter_upwards [hc.eventually (gt_mem_nhds h)] with σ hσ
      exact ⟨fun h' => absurd h' (not_le.2 hσ), fun h' => absurd h' (not_le.2 h)⟩
    · filter_upwards [hc.eventually (lt_mem_nhds h)] with σ hσ
      exact ⟨fun _ => h.le, fun _ => hσ.le⟩
  filter_upwards [(Filter.eventually_all_finset Rl).2 hl, (Filter.eventually_all_finset Rg).2 hg] with σ h1 h2
  unfold CndR
  constructor
  · rintro ⟨a, b⟩
    exact ⟨fun p hp => (h1 p hp).1 (a p hp), fun p hp => (h2 p hp).1 (b p hp)⟩
  · rintro ⟨a, b⟩
    exact ⟨fun p hp => (h1 p hp).2 (a p hp), fun p hp => (h2 p hp).2 (b p hp)⟩

theorem fR_continuousAt {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (G : (Fin m → ℝ) → ℝ) (σ0 : Fin m → ℝ)
    (hoff : ∀ p ∈ Rl ∪ Rg, LF p.1 (expv σ0) ≠ p.2)
    (hG : CndR Rl Rg (expv σ0) → ContinuousAt G (expv σ0)) :
    ContinuousAt (fR Rl Rg G) σ0 := by
  classical
  have hev := cnd_eventually Rl Rg σ0 hoff
  have hexp : ContinuousAt (expv (m := m)) σ0 :=
    (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i)).continuousAt
  by_cases h0 : CndR Rl Rg (expv σ0)
  · have hc : ContinuousAt (fun σ => G (expv σ)) σ0 := ContinuousAt.comp (hG h0) hexp
    apply hc.congr_of_eventuallyEq
    filter_upwards [hev] with σ hσ
    unfold fR; rw [if_pos (hσ.2 h0)]
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hev] with σ hσ
    unfold fR; rw [if_neg (fun h => h0 (hσ.1 h))]

theorem fR_ae_continuous {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (G : (Fin m → ℝ) → ℝ)
    (hne : ∀ p ∈ Rl ∪ Rg, p.1 ≠ 0)
    (hG : ∀ x : Fin m → ℝ, CndR Rl Rg x → ContinuousAt G x) :
    ∀ᵐ σ ∂(volume : Measure (Fin m → ℝ)), ContinuousAt (fR Rl Rg G) σ :=
  ae_continuousAt_of_bad _ (Rl ∪ Rg) hne (fun σ h => fR_continuousAt Rl Rg G σ (fun p hp => by
    have := h p hp; unfold LF expv; exact this) (hG _))

theorem cnd_measurableSet {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) :
    MeasurableSet {σ : Fin m → ℝ | CndR Rl Rg (expv σ)} := by
  have h1 : {σ : Fin m → ℝ | CndR Rl Rg (expv σ)} =
      (⋂ p ∈ Rl, {σ : Fin m → ℝ | LF p.1 (expv σ) < p.2}) ∩ (⋂ p ∈ Rg, {σ : Fin m → ℝ | p.2 ≤ LF p.1 (expv σ)}) := by
    ext σ; simp [CndR]
  rw [h1]
  apply MeasurableSet.inter
  · exact MeasurableSet.biInter Rl.countable_toSet (fun p _ =>
      measurableSet_lt (LF_expv_continuous p.1).measurable measurable_const)
  · exact MeasurableSet.biInter Rg.countable_toSet (fun p _ =>
      measurableSet_le measurable_const (LF_expv_continuous p.1).measurable)

theorem fR_measurable {m : ℕ} (Rl Rg : Finset ((Fin m → ℝ) × ℝ)) (G : (Fin m → ℝ) → ℝ) (hG : Measurable G) :
    Measurable (fR Rl Rg G) := by
  classical
  unfold fR
  exact Measurable.ite (cnd_measurableSet Rl Rg)
    (hG.comp (continuous_pi fun i => Real.continuous_exp.comp (continuous_apply i)).measurable) measurable_const

/-! ## The weight `W` -/

theorem Wf_eq (t : ℝ) : Wf t = max 0 (min (min (kSq * t ^ 2) (t - mm)) W1) := by
  unfold Wf
  have hm : mm = 1 / 85 := rfl
  have hk : kSq = 9999 / 1000 := rfl
  have hU : UU = 83 / 85 := rfl
  have hW : W1 = 82 / 85 := rfl
  split_ifs with h1 h2 h3
  · symm; apply max_eq_left
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (by linarith))
  · push Not at h1
    have hpos : 0 ≤ min (kSq * t ^ 2) (t - mm) := le_min (by positivity) (by linarith)
    have hle : min (kSq * t ^ 2) (t - mm) ≤ W1 := le_trans (min_le_right _ _) (by linarith)
    rw [min_eq_left hle, max_eq_right hpos]
  · push Not at h1 h2
    have h4 : t - mm ≤ kSq * t ^ 2 := by nlinarith
    rw [min_eq_right h4, min_eq_left (by linarith), max_eq_right (by linarith)]
  · push Not at h1 h2 h3
    have h4 : W1 ≤ kSq * t ^ 2 := by nlinarith
    have h5 : W1 ≤ t - mm := by linarith
    rw [min_eq_right (le_min h4 h5), max_eq_right (by rw [hW]; norm_num)]

theorem Wf_continuous : Continuous Wf := by
  have : Wf = fun t => max 0 (min (min (kSq * t ^ 2) (t - mm)) W1) := funext Wf_eq
  rw [this]
  fun_prop

theorem Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by rw [Wf_eq]; exact le_max_left _ _

theorem Wf_le (t : ℝ) : Wf t ≤ W1 := by
  rw [Wf_eq]; apply max_le (by unfold W1; norm_num) (min_le_right _ _)

theorem Wf_zero_of_le {t : ℝ} (h : t ≤ mm) : Wf t = 0 := by unfold Wf; rw [if_pos h]

theorem Wf_W1_of_ge {t : ℝ} (h : UU ≤ t) : Wf t = W1 := by
  rw [Wf_eq]
  have hm : mm = 1 / 85 := rfl
  have hk : kSq = 9999 / 1000 := rfl
  have hU : UU = 83 / 85 := rfl
  have hW : W1 = 82 / 85 := rfl
  have h4 : W1 ≤ kSq * t ^ 2 := by nlinarith
  have h5 : W1 ≤ t - mm := by linarith
  rw [min_eq_right (le_min h4 h5), max_eq_right (by rw [hW]; norm_num)]

end Omega3.M11

end

section

/-!
# M11 helper: the chain integrand of `E11` (chains of length `n`) and its integral

Coordinates `x : Fin (n+1) → ℝ`, `x (last n) = t = log p/log y`, `Fin.init x = v` the chain (decreasing).
`fA n σ = [CndA (e^σ)] W(t)·2e^γ/u`, `u = 1 − t − Σ v`. The conditions are the arithmetic ones (strict prefix
conditions, non-strict final one); off the hyperplanes `PF v j = 1` they are `t < 1/2 ∧ HRegion86 n t v`.
`∫_{box} fA n = ∫ Kk n`, `Kk n t = [a < t < 1/2] W(t)·2e^γ/t · h86 n t`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

/-- The lower end `a = 1/170` of the boxes. -/
noncomputable def aa : ℝ := 1 / 170

theorem aa_pos : 0 < aa := by unfold aa; norm_num
theorem aa_lt_one : aa < 1 := by unfold aa; norm_num
theorem aa_lt_mm : aa < mm := by unfold aa mm; norm_num

/-- Unit vector. -/
noncomputable def eV {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → ℝ := fun k => if k = i then 1 else 0

theorem LF_eV {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) : LF (eV i) x = x i := by
  unfold LF eV; simp

theorem LF_sub {m : ℕ} (c c' x : Fin m → ℝ) : LF (c - c') x = LF c x - LF c' x := by
  unfold LF; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [Pi.sub_apply]; ring

/-- Prefix sum `PF v j = 3 v_{j−1} + Σ_{l < j−1} v_l` (as in `HRegion86`). -/
noncomputable def PF {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ := 3 * chainV v (j - 1) + ∑ l ∈ range (j - 1), chainV v l

noncomputable def prefC (j l : ℕ) : ℝ := if l = j - 1 then 3 else if l < j - 1 then 1 else 0

noncomputable def prefRow (n j : ℕ) : Fin (n + 1) → ℝ := fun i => if i.val < n then prefC j i.val else 0

noncomputable def lastRow (n : ℕ) : Fin (n + 1) → ℝ := fun i => if i = Fin.last n then 1 else if i.val = n - 1 then 2 else 1

theorem init_eq_chainV {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : v i = chainV v i.val := by
  unfold chainV; rw [dif_pos i.isLt]

theorem sum_range_prefC {n : ℕ} (v : Fin n → ℝ) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    ∑ l ∈ range n, prefC j l * chainV v l = PF v j := by
  unfold PF prefC
  have e : ∀ l, (if l = j - 1 then (3 : ℝ) else if l < j - 1 then 1 else 0) * chainV v l =
      (if l = j - 1 then 3 * chainV v l else 0) + (if l < j - 1 then chainV v l else 0) := by
    intro l
    by_cases h1 : l = j - 1
    · rw [if_pos h1, if_pos h1, if_neg (by omega)]; ring
    · rw [if_neg h1, if_neg h1]; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_add_distrib, Finset.sum_ite_eq' (range n) (j - 1),
    if_pos (by rw [mem_range]; omega), ← Finset.sum_filter]
  congr 2
  ext l; simp only [mem_filter, mem_range]; omega

theorem LF_prefRow {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) (x : Fin (n + 1) → ℝ) :
    LF (prefRow n j) x = PF (Fin.init x) j := by
  unfold LF prefRow
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_irrefl, ite_false, zero_mul, add_zero]
  rw [← sum_range_prefC (Fin.init x) hj hjn]
  rw [← Fin.sum_univ_eq_sum_range (fun l => prefC j l * chainV (Fin.init x) l) n]
  apply Finset.sum_congr rfl; intro i _
  rw [← init_eq_chainV]; rfl

theorem LF_lastRow {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) :
    LF (lastRow n) x = x (Fin.last n) + ∑ j, Fin.init x j + chainV (Fin.init x) (n - 1) := by
  have hne : ∀ i : Fin n, Fin.castSucc i ≠ Fin.last n := fun i => Fin.castSucc_ne_last i
  have e : ∀ i : Fin n, lastRow n (Fin.castSucc i) * x (Fin.castSucc i) =
      Fin.init x i + (if i = ⟨n - 1, by omega⟩ then Fin.init x i else 0) := by
    intro i
    unfold lastRow
    rw [if_neg (hne i)]
    simp only [Fin.coe_castSucc]
    by_cases h : i.val = n - 1
    · rw [if_pos h, if_pos (Fin.ext h)]; unfold Fin.init; ring
    · rw [if_neg h, if_neg (fun h' => h (by rw [h'])) ]; unfold Fin.init; ring
  have hl : lastRow n (Fin.last n) = 1 := by unfold lastRow; rw [if_pos rfl]
  unfold LF
  rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl (fun i _ => e i), hl, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ, if_pos (mem_univ _)]
  unfold chainV; rw [dif_pos (by omega)]; ring

/-- The arithmetic chain conditions as rows. -/
noncomputable def RlA (n : ℕ) : Finset ((Fin (n + 1) → ℝ) × ℝ) :=
  {(eV (Fin.last n), 1 / 2)} ∪ (univ.image (fun j : Fin n => (eV (Fin.last n) - eV j.castSucc, (0 : ℝ)))) ∪
    (univ.image (fun j : Fin n => (eV j.castSucc, (1 : ℝ)))) ∪
    ((univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).image
      (fun ij => (eV ij.2.castSucc - eV ij.1.castSucc, (0 : ℝ)))) ∪
    ((Ico 1 n).image (fun j => (prefRow n j, (1 : ℝ)))) ∪ {(lastRow n, 1)}

noncomputable def RgA (n : ℕ) : Finset ((Fin (n + 1) → ℝ) × ℝ) := {(prefRow n n, 1)}

/-- The arithmetic chain conditions, explicit form. -/
def ExplA (n : ℕ) (x : Fin (n + 1) → ℝ) : Prop :=
  x (Fin.last n) < 1 / 2 ∧ (∀ j, x (Fin.last n) < Fin.init x j) ∧ (∀ j, Fin.init x j < 1) ∧
    StrictAnti (Fin.init x) ∧ (∀ j : ℕ, 1 ≤ j → j < n → PF (Fin.init x) j < 1) ∧
    x (Fin.last n) + ∑ j, Fin.init x j + chainV (Fin.init x) (n - 1) < 1 ∧ 1 ≤ PF (Fin.init x) n

theorem cndA_iff {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) : CndR (RlA n) (RgA n) x ↔ ExplA n x := by
  unfold CndR ExplA
  constructor
  · rintro ⟨Hl, Hg⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := Hl (eV (Fin.last n), 1 / 2) (by simp [RlA]); rwa [LF_eV] at this
    · intro j
      have := Hl (eV (Fin.last n) - eV j.castSucc, 0) (by simp only [RlA, mem_union, mem_image, mem_univ, true_and]; left; left; left; left; right; exact ⟨j, rfl⟩)
      rw [LF_sub, LF_eV, LF_eV] at this; unfold Fin.init; linarith
    · intro j
      have := Hl (eV j.castSucc, 1) (by simp only [RlA, mem_union, mem_image, mem_univ, true_and]; left; left; left; right; exact ⟨j, rfl⟩)
      rw [LF_eV] at this; exact this
    · intro i j hij
      have := Hl (eV j.castSucc - eV i.castSucc, 0) (by
        simp only [RlA, mem_union, mem_image, mem_filter, mem_univ, true_and]; left; left; right; exact ⟨(i, j), hij, rfl⟩)
      rw [LF_sub, LF_eV, LF_eV] at this; unfold Fin.init; linarith
    · intro j hj1 hjn
      have := Hl (prefRow n j, 1) (by
        simp only [RlA, mem_union, mem_image, mem_Ico]; left; right; exact ⟨j, ⟨hj1, hjn⟩, rfl⟩)
      rwa [LF_prefRow hj1 hjn.le] at this
    · have := Hl (lastRow n, 1) (by simp [RlA])
      rwa [LF_lastRow hn] at this
    · have := Hg (prefRow n n, 1) (by simp [RgA])
      rwa [LF_prefRow hn le_rfl] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · simp only [RlA, mem_union, mem_singleton, mem_image, mem_univ, true_and, mem_filter, mem_Ico] at hp
      rcases hp with (((((rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨⟨i, j⟩, hij, rfl⟩) | ⟨j, ⟨hj1, hjn⟩, rfl⟩) | rfl)
      · rw [LF_eV]; exact h1
      · rw [LF_sub, LF_eV, LF_eV]; have := h2 j; unfold Fin.init at this; simp only; linarith
      · rw [LF_eV]; exact h3 j
      · rw [LF_sub, LF_eV, LF_eV]; have := h4 hij; unfold Fin.init at this; simp only; linarith
      · rw [LF_prefRow hj1 hjn.le]; exact h5 j hj1 hjn
      · rw [LF_lastRow hn]; exact h6
    · simp only [RgA, mem_singleton] at hp
      subst hp
      rw [LF_prefRow hn le_rfl]; exact h7

theorem RA_ne {n : ℕ} (hn : 1 ≤ n) : ∀ p ∈ RlA n ∪ RgA n, p.1 ≠ 0 := by
  have heV : ∀ i : Fin (n + 1), eV i ≠ 0 := by
    intro i h; have := congrFun h i; simp [eV] at this
  have hsub : ∀ i j : Fin (n + 1), i ≠ j → eV i - eV j ≠ 0 := by
    intro i j hij h; have := congrFun h i; simp [eV, hij] at this
  have hpref : ∀ j, 1 ≤ j → j ≤ n → prefRow n j ≠ 0 := by
    intro j hj1 hjn h
    have := congrFun h ⟨j - 1, by omega⟩
    simp [prefRow, prefC] at this
    omega
  have hlast : lastRow n ≠ 0 := by
    intro h; have := congrFun h (Fin.last n); simp [lastRow] at this
  intro p hp
  simp only [RlA, RgA, mem_union, mem_singleton, mem_image, mem_univ, true_and, mem_filter, mem_Ico] at hp
  rcases hp with ((((((rfl | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨⟨i, j⟩, hij, rfl⟩) | ⟨j, ⟨hj1, hjn⟩, rfl⟩) | rfl) | rfl)
  · exact heV _
  · exact hsub _ _ (Fin.castSucc_ne_last j).symm
  · exact heV _
  · exact hsub _ _ (fun h => absurd (Fin.castSucc_injective _ h) (ne_of_lt hij).symm)
  · exact hpref j hj1 hjn.le
  · exact hlast
  · exact hpref n hn le_rfl

/-- The weight function. -/
noncomputable def GA (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  Wf (x (Fin.last n)) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - x (Fin.last n) - ∑ j, Fin.init x j)

noncomputable def fA (n : ℕ) : (Fin (n + 1) → ℝ) → ℝ := fR (RlA n) (RgA n) (GA n)

/-- On the conditions: `u > v_{n−1} > t`. -/
theorem explA_u {n : ℕ} (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (h : ExplA n x) :
    x (Fin.last n) < 1 - x (Fin.last n) - ∑ j, Fin.init x j := by
  obtain ⟨-, h2, -, -, -, h6, -⟩ := h
  have := h2 ⟨n - 1, by omega⟩
  have e : chainV (Fin.init x) (n - 1) = Fin.init x ⟨n - 1, by omega⟩ := by unfold chainV; rw [dif_pos (by omega)]
  rw [e] at h6
  linarith

theorem GA_continuousAt {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) (hpos : 0 < x (Fin.last n))
    (h : ExplA n x) : ContinuousAt (GA n) x := by
  have hu := explA_u hn h
  unfold GA
  have hden : Continuous (fun x : Fin (n + 1) → ℝ => 1 - x (Fin.last n) - ∑ j, Fin.init x j) := by
    unfold Fin.init; fun_prop
  apply ContinuousAt.div
  · exact ((Wf_continuous.comp (continuous_apply _)).mul continuous_const).continuousAt
  · exact hden.continuousAt
  · have h0 : 0 < 1 - x (Fin.last n) - ∑ j, Fin.init x j := by linarith
    exact ne_of_gt h0

theorem GA_measurable (n : ℕ) : Measurable (GA n) := by
  unfold GA
  have hden : Continuous (fun x : Fin (n + 1) → ℝ => 1 - x (Fin.last n) - ∑ j, Fin.init x j) := by
    unfold Fin.init; fun_prop
  apply Measurable.div
  · exact ((Wf_continuous.comp (continuous_apply _)).mul continuous_const).measurable
  · exact hden.measurable

theorem fA_ae {n : ℕ} (hn : 1 ≤ n) : ∀ᵐ σ ∂(volume : Measure (Fin (n + 1) → ℝ)), ContinuousAt (fA n) σ := by
  unfold fA
  apply ae_continuousAt_of_bad _ (RlA n ∪ RgA n) (RA_ne hn)
  intro σ hσ
  apply fR_continuousAt _ _ _ σ (fun p hp => by have := hσ p hp; unfold LF expv; exact this)
  intro hc
  exact GA_continuousAt hn _ (Real.exp_pos _) ((cndA_iff hn _).1 hc)

theorem fA_measurable (n : ℕ) : Measurable (fA n) := fR_measurable _ _ _ (GA_measurable n)

theorem fA_bound {n : ℕ} (hn : 1 ≤ n) (σ : Fin (n + 1) → ℝ) :
    ‖fA n σ‖ ≤ 2 * Real.exp Real.eulerMascheroniConstant * W1 * 85 := by
  classical
  unfold fA fR
  have hE : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have hW1 : (0 : ℝ) < W1 := by unfold W1; norm_num
  split_ifs with hc
  · have h := (cndA_iff hn _).1 hc
    have hu := explA_u hn h
    set x := expv σ
    have ht : 0 < x (Fin.last n) := Real.exp_pos _
    unfold GA
    rw [Real.norm_eq_abs]
    by_cases hm : x (Fin.last n) ≤ mm
    · rw [Wf_zero_of_le hm]; simp; positivity
    · push Not at hm
      have hu0 : 0 < 1 - x (Fin.last n) - ∑ j, Fin.init x j := by linarith
      have hW := Wf_le (x (Fin.last n))
      have hW0 := Wf_nonneg (x (Fin.last n))
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hu0]
      have hm' : (1 : ℝ) / 85 < 1 - x (Fin.last n) - ∑ j, Fin.init x j := by
        have : mm = 1 / 85 := rfl; linarith
      have h1 : Wf (x (Fin.last n)) * (2 * Real.exp Real.eulerMascheroniConstant) ≤
          W1 * (2 * Real.exp Real.eulerMascheroniConstant) := mul_le_mul_of_nonneg_right hW (by positivity)
      have h2 : W1 * (2 * Real.exp Real.eulerMascheroniConstant) ≤
          2 * Real.exp Real.eulerMascheroniConstant * W1 * 85 * (1 - x (Fin.last n) - ∑ j, Fin.init x j) := by
        have : 2 * Real.exp Real.eulerMascheroniConstant * W1 * 85 * (1 / 85) = W1 * (2 * Real.exp Real.eulerMascheroniConstant) := by ring
        rw [← this]
        exact mul_le_mul_of_nonneg_left hm'.le (by positivity)
      linarith
  · simp; positivity

/-! ## Off the hyperplanes: the region of `h86` -/

theorem explA_iff_region {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) (hoff : ∀ j ∈ Icc 1 n, PF (Fin.init x) j ≠ 1) :
    ExplA n x ↔ x (Fin.last n) < 1 / 2 ∧ HRegion86 n (x (Fin.last n)) (Fin.init x) := by
  unfold ExplA HRegion86
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h4, h2, h3, fun j hj1 hjn => (h5 j hj1 hjn).le, ?_, by linarith⟩
    exact lt_of_le_of_ne h7 (fun h => hoff n (by simp; omega) h.symm)
  · rintro ⟨h1, h4, h2, h3, h5, h7, h6⟩
    refine ⟨h1, h2, h3, h4, fun j hj1 hjn => lt_of_le_of_ne (h5 j hj1 hjn) (hoff j (by simp; omega)), by linarith, h7.le⟩

/-! ## `x`-coordinates and the integral -/

noncomputable def FA (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  (Set.pi Set.univ (fun _ => Set.Ioc aa 1)).indicator (fun x => fA n (logv x) / ∏ i, x i) x

noncomputable def KA (n : ℕ) (t : ℝ) : ℝ :=
  open Classical in if aa < t ∧ t < 1 / 2 then Wf t * (2 * Real.exp Real.eulerMascheroniConstant) / t * h86 n t else 0

theorem IA_eq (n : ℕ) :
    ∫ σ in (boxA (n + 1) aa aa_pos aa_lt_one : Set (Fin (n + 1) → ℝ)), fA n σ = ∫ x, FA n x := by
  unfold FA
  rw [box_cov, integral_indicator (measurableSet_boxx _ _)]

theorem fA_integrableOn {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (fA n) (boxA (n + 1) aa aa_pos aa_lt_one : Set (Fin (n + 1) → ℝ)) :=
  integrableOn_box _ _ _ _ (fA_measurable n) _ (fun σ _ => fA_bound hn σ)

theorem FA_integrable {n : ℕ} (hn : 1 ≤ n) : Integrable (FA n) := by
  unfold FA
  rw [integrable_indicator_iff (measurableSet_boxx _ _)]
  exact box_cov_integrable _ _ _ _ _ (fA_integrableOn hn)

theorem FA_snoc {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ) (hoff : ∀ j ∈ Icc 1 n, PF v j ≠ 1) :
    FA n (Fin.snoc v t) = open Classical in if aa < t ∧ t < 1 / 2 then
      Wf t * (2 * Real.exp Real.eulerMascheroniConstant) / t *
        (if HRegion86 n t v then 1 / ((∏ j, v j) * (1 - t - ∑ j, v j)) else 0) else 0 := by
  classical
  have ha := aa_pos
  unfold FA
  by_cases hmem : (Fin.snoc v t : Fin (n + 1) → ℝ) ∈ Set.pi Set.univ (fun _ => Set.Ioc aa 1)
  · have hpos : ∀ i, 0 < (Fin.snoc v t : Fin (n + 1) → ℝ) i := fun i => lt_trans ha (hmem i (Set.mem_univ _)).1
    have ht := hmem (Fin.last n) (Set.mem_univ _)
    rw [Fin.snoc_last] at ht
    rw [Set.indicator_of_mem hmem]
    unfold fA fR
    rw [expv_logv _ hpos]
    have hoff' : ∀ j ∈ Icc 1 n, PF (Fin.init (Fin.snoc v t : Fin (n + 1) → ℝ)) j ≠ 1 := by
      rw [Fin.init_snoc]; exact hoff
    by_cases hc : CndR (RlA n) (RgA n) (Fin.snoc v t)
    · rw [if_pos hc]
      have hE := (cndA_iff hn _).1 hc
      have hR := (explA_iff_region hn _ hoff').1 hE
      rw [Fin.snoc_last, Fin.init_snoc] at hR
      have hu := explA_u hn hE
      rw [Fin.snoc_last, Fin.init_snoc] at hu
      rw [if_pos ⟨ht.1, hR.1⟩, if_pos hR.2]
      unfold GA
      rw [Fin.snoc_last, Fin.init_snoc, prod_snoc]
      have hPv : 0 < ∏ j, v j := Finset.prod_pos (fun j _ => lt_trans (lt_trans ha ht.1) (hR.2.2.1 j))
      have ht0 : 0 < t := lt_trans ha ht.1
      have hu0 : 0 < 1 - t - ∑ j, v j := by linarith
      field_simp
    · rw [if_neg hc]
      have hnot : ¬ (t < 1 / 2 ∧ HRegion86 n t v) := by
        intro h
        apply hc
        rw [cndA_iff hn, explA_iff_region hn _ hoff', Fin.snoc_last, Fin.init_snoc]; exact h
      by_cases h1 : aa < t ∧ t < 1 / 2
      · rw [if_pos h1, if_neg (fun h => hnot ⟨h1.2, h⟩), mul_zero, zero_div]
      · rw [if_neg h1, zero_div]
  · rw [Set.indicator_of_notMem hmem]
    by_cases h1 : aa < t ∧ t < 1 / 2
    · rw [if_pos h1]
      by_cases hR : HRegion86 n t v
      · exfalso; apply hmem
        intro i _
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · simp only [Fin.snoc_castSucc]; exact ⟨lt_trans h1.1 (hR.2.1 i'), (hR.2.2.1 i').le⟩
        · simp only [Fin.snoc_last]; exact ⟨h1.1, by linarith [h1.2]⟩
      · rw [if_neg hR, mul_zero]
    · rw [if_neg h1]

theorem inner_FA {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ∫ v : Fin n → ℝ, FA n (Fin.snoc v t) = KA n t := by
  classical
  have hae : ∀ᵐ v : Fin n → ℝ ∂volume, ∀ j ∈ Icc 1 n, PF v j ≠ 1 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [mem_Icc] at hj
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin n, prefC j i.val • LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
    have hLw : ∀ w, L w = PF w j := by
      intro w
      have h0 : L w = ∑ i : Fin n, prefC j i.val * w i := by simp [L]
      rw [h0, ← sum_range_prefC w hj.1 hj.2, ← Fin.sum_univ_eq_sum_range (fun l => prefC j l * chainV w l) n]
      apply Finset.sum_congr rfl; intro i _; rw [← init_eq_chainV]
    have hL : L ≠ 0 := by
      intro h
      have := LinearMap.congr_fun h (Pi.single ⟨j - 1, by omega⟩ 1)
      rw [hLw] at this
      unfold PF chainV at this
      simp only [LinearMap.zero_apply] at this
      rw [dif_pos (by omega)] at this
      have hs : ∑ l ∈ range (j - 1), (if h : l < n then (Pi.single (⟨j - 1, by omega⟩ : Fin n) (1 : ℝ) : Fin n → ℝ) ⟨l, h⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero; intro l hl
        rw [mem_range] at hl
        rw [dif_pos (by omega)]
        rw [Pi.single_apply, if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega)]
      rw [hs] at this; simp at this
    have hnull := volume_linear_level_null L hL 1
    rw [ae_iff]
    apply measure_mono_null _ hnull
    intro w hw
    simp only [Set.mem_setOf_eq, not_not] at hw ⊢
    rw [hLw]; exact hw
  rw [integral_congr_ae (hae.mono (fun v hv => FA_snoc hn v t hv))]
  unfold KA
  by_cases h1 : aa < t ∧ t < 1 / 2
  · simp only [if_pos h1]
    rw [integral_const_mul]
    unfold h86
    congr 1
  · simp only [if_neg h1, MeasureTheory.integral_zero]

theorem IA_eq_KA {n : ℕ} (hn : 1 ≤ n) :
    ∫ σ in (boxA (n + 1) aa aa_pos aa_lt_one : Set (Fin (n + 1) → ℝ)), fA n σ = ∫ t, KA n t ∧ Integrable (KA n) := by
  have hF := FA_integrable hn
  have e : (fun t : ℝ => ∫ v : Fin n → ℝ, FA n (Fin.snoc v t)) = KA n := funext (inner_FA hn)
  refine ⟨?_, ?_⟩
  · rw [IA_eq, integral_split_last _ hF, e]
  · rw [← e]; exact integrable_inner_last _ hF

end Omega3.M11

end

section

/-!
# M11 helper: the one-dimensional pieces and the identification with `𝓜(W)`

`f2 = [1/2 ≤ t](W(1) − W(t))·2e^γ/(1 − t)`, `f3 = [t < 1/2] W(t)·2e^γ/(1 − t)` in log-log coordinates on `Fin 1`.
`∫_{box} f2 = 2e^γ I2`, `∫_{box} f3 = 2e^γ I3`, `Σ_{k ≤ 42} ∫ KA (2k) = 2e^γ I4`, `mvalW = −I2 + I3 − I4`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real MeasureTheory Filter Topology BoxIntegral

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

noncomputable def e1 : Fin 1 → ℝ := fun _ => 1

theorem LF_e1 (x : Fin 1 → ℝ) : LF e1 x = x 0 := by unfold LF e1; simp

noncomputable def EG : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

theorem EG_pos : 0 < EG := by unfold EG; positivity

noncomputable def G2 (x : Fin 1 → ℝ) : ℝ := (W1 - Wf (x 0)) * EG / (1 - x 0)
noncomputable def G3 (x : Fin 1 → ℝ) : ℝ := Wf (x 0) * EG / (1 - x 0)

noncomputable def f2 : (Fin 1 → ℝ) → ℝ := fR ∅ {(e1, 1 / 2)} G2
noncomputable def f3 : (Fin 1 → ℝ) → ℝ := fR {(e1, 1 / 2)} ∅ G3

noncomputable def g2 (t : ℝ) : ℝ := (W1 - Wf t) / ((1 - t) * t)
noncomputable def g3 (t : ℝ) : ℝ := Wf t / ((1 - t) * t)
noncomputable def g4 (t : ℝ) : ℝ := Wf t * hS t / t

theorem cnd2_iff (x : Fin 1 → ℝ) : CndR ∅ {(e1, 1 / 2)} x ↔ 1 / 2 ≤ x 0 := by
  unfold CndR; simp [LF_e1]

theorem cnd3_iff (x : Fin 1 → ℝ) : CndR {(e1, 1 / 2)} ∅ x ↔ x 0 < 1 / 2 := by
  unfold CndR; simp [LF_e1]

theorem e1_ne : e1 ≠ 0 := by intro h; have := congrFun h 0; simp [e1] at this

theorem W1_sub_Wf_zero {t : ℝ} (h : UU ≤ t) : W1 - Wf t = 0 := by rw [Wf_W1_of_ge h]; ring

theorem G2_continuousAt (x : Fin 1 → ℝ) : ContinuousAt G2 x := by
  by_cases h : x 0 < 1
  · unfold G2
    apply ContinuousAt.div
    · exact ((continuous_const.sub (Wf_continuous.comp (continuous_apply 0))).mul continuous_const).continuousAt
    · exact (continuous_const.sub (continuous_apply 0)).continuousAt
    · have h0 : 0 < 1 - x 0 := by linarith
      exact ne_of_gt h0
  · push Not at h
    have hU : UU < x 0 := lt_of_lt_of_le (by unfold UU; norm_num) h
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    have hev : ∀ᶠ z in 𝓝 x, UU < z 0 := (continuous_apply 0).continuousAt.eventually (lt_mem_nhds hU)
    filter_upwards [hev] with z hz
    unfold G2; rw [W1_sub_Wf_zero hz.le]; simp

theorem G3_continuousAt (x : Fin 1 → ℝ) (h : x 0 < 1 / 2) : ContinuousAt G3 x := by
  unfold G3
  apply ContinuousAt.div
  · exact ((Wf_continuous.comp (continuous_apply 0)).mul continuous_const).continuousAt
  · exact (continuous_const.sub (continuous_apply 0)).continuousAt
  · have h0 : 0 < 1 - x 0 := by linarith
    exact ne_of_gt h0

theorem G2_measurable : Measurable G2 := by
  unfold G2
  exact (((continuous_const.sub (Wf_continuous.comp (continuous_apply 0))).mul continuous_const).measurable).div
    (continuous_const.sub (continuous_apply 0)).measurable

theorem G3_measurable : Measurable G3 := by
  unfold G3
  exact (((Wf_continuous.comp (continuous_apply 0)).mul continuous_const).measurable).div
    (continuous_const.sub (continuous_apply 0)).measurable

theorem f2_ae : ∀ᵐ σ ∂(volume : Measure (Fin 1 → ℝ)), ContinuousAt f2 σ := by
  apply fR_ae_continuous
  · intro p hp; simp at hp; rw [hp]; exact e1_ne
  · intro x _; exact G2_continuousAt x

theorem f3_ae : ∀ᵐ σ ∂(volume : Measure (Fin 1 → ℝ)), ContinuousAt f3 σ := by
  apply fR_ae_continuous
  · intro p hp; simp at hp; rw [hp]; exact e1_ne
  · intro x hx; exact G3_continuousAt x ((cnd3_iff x).1 hx)

theorem f2_bound (σ : Fin 1 → ℝ) : ‖f2 σ‖ ≤ EG * W1 * 85 := by
  classical
  have hE := EG_pos
  have hW : (0 : ℝ) < W1 := by unfold W1; norm_num
  unfold f2 fR
  split_ifs with hc
  · obtain ⟨t, ht⟩ : ∃ t, expv σ 0 = t := ⟨_, rfl⟩
    unfold G2
    rw [Real.norm_eq_abs, ht]
    by_cases hU : UU ≤ t
    · rw [W1_sub_Wf_zero hU]; simp; positivity
    · push Not at hU
      have h1 : 2 / 85 < 1 - t := by have : UU = 83 / 85 := rfl; linarith
      have hW0 := Wf_nonneg t
      have hWl := Wf_le t
      rw [abs_div, abs_mul, abs_of_nonneg (by linarith : 0 ≤ W1 - Wf t), abs_of_pos hE, abs_of_pos (by linarith),
        div_le_iff₀ (by linarith)]
      have : (W1 - Wf t) * EG ≤ W1 * EG := mul_le_mul_of_nonneg_right (by linarith) hE.le
      have h3 : W1 * EG ≤ EG * W1 * 85 * (1 - t) := by
        have : (2 : ℝ) ≤ 85 * (1 - t) := by linarith
        have h4 : 0 ≤ EG * W1 := by positivity
        nlinarith
      linarith
  · simp; positivity

theorem f3_bound (σ : Fin 1 → ℝ) : ‖f3 σ‖ ≤ EG * W1 * 85 := by
  classical
  have hE := EG_pos
  have hW : (0 : ℝ) < W1 := by unfold W1; norm_num
  unfold f3 fR
  split_ifs with hc
  · have ht := (cnd3_iff _).1 hc
    obtain ⟨t, htt⟩ : ∃ t, expv σ 0 = t := ⟨_, rfl⟩
    rw [htt] at ht
    unfold G3
    rw [Real.norm_eq_abs, htt]
    have hW0 := Wf_nonneg t
    have hWl := Wf_le t
    rw [abs_div, abs_mul, abs_of_nonneg hW0, abs_of_pos hE, abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
    have : Wf t * EG ≤ W1 * EG := mul_le_mul_of_nonneg_right hWl hE.le
    have h3 : W1 * EG ≤ EG * W1 * 85 * (1 - t) := by
      have : (2 : ℝ) ≤ 85 * (1 - t) := by linarith
      have h4 : 0 ≤ EG * W1 := by positivity
      nlinarith
    linarith
  · simp; positivity

theorem f2_measurable : Measurable f2 := fR_measurable _ _ _ G2_measurable
theorem f3_measurable : Measurable f3 := fR_measurable _ _ _ G3_measurable

/-! ## Box integrals in `t` -/

theorem integral_fin1 (F : (Fin 1 → ℝ) → ℝ) : ∫ x, F x = ∫ t : ℝ, F (fun _ => t) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have := h.integral_comp (MeasurableEquiv.measurableEmbedding _) F
  exact this.symm

theorem integrable_fin1 (F : (Fin 1 → ℝ) → ℝ) (hF : Integrable F) : Integrable (fun t : ℝ => F (fun _ => t)) := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have := (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := F)).2 hF
  exact this

theorem box1_eval (f : (Fin 1 → ℝ) → ℝ) (t : ℝ) :
    (Set.pi Set.univ (fun _ => Set.Ioc aa 1)).indicator (fun x => f (logv x) / ∏ i, x i) (fun _ : Fin 1 => t) =
      (Set.Ioc aa 1).indicator (fun t => f (fun _ => Real.log t) / t) t := by
  by_cases h : t ∈ Set.Ioc aa 1
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by intro i _; exact h)]
    simp only [Fin.prod_univ_one]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by intro hm; exact h (hm 0 (Set.mem_univ _)))]

theorem box_int_fin1 (f : (Fin 1 → ℝ) → ℝ) (hf : IntegrableOn f (boxA 1 aa aa_pos aa_lt_one : Set (Fin 1 → ℝ))) :
    ∫ σ in (boxA 1 aa aa_pos aa_lt_one : Set (Fin 1 → ℝ)), f σ = ∫ t, (Set.Ioc aa 1).indicator (fun t => f (fun _ => Real.log t) / t) t ∧
      Integrable (fun t => (Set.Ioc aa 1).indicator (fun t => f (fun _ => Real.log t) / t) t) := by
  have hF : Integrable ((Set.pi Set.univ (fun _ => Set.Ioc aa 1)).indicator (fun x => f (logv x) / ∏ i, x i)) := by
    rw [integrable_indicator_iff (measurableSet_boxx _ _)]
    exact box_cov_integrable _ _ _ _ _ hf
  constructor
  · rw [box_cov, ← integral_indicator (measurableSet_boxx _ _), integral_fin1]
    congr 1; funext t; exact box1_eval f t
  · have := integrable_fin1 _ hF
    simp only [box1_eval] at this
    exact this

theorem f2_log (t : ℝ) (ht : 0 < t) :
    f2 (fun _ => Real.log t) / t = EG * (open Classical in if 1 / 2 ≤ t then g2 t else 0) := by
  classical
  unfold f2 fR
  have hx : expv (fun _ : Fin 1 => Real.log t) = fun _ => t := by funext i; unfold expv; exact Real.exp_log ht
  rw [hx]
  by_cases h : 1 / 2 ≤ t
  · rw [if_pos ((cnd2_iff _).2 h), if_pos h]; unfold G2 g2; field_simp
  · rw [if_neg (fun h' => h ((cnd2_iff _).1 h')), if_neg h]; simp

theorem f3_log (t : ℝ) (ht : 0 < t) :
    f3 (fun _ => Real.log t) / t = EG * (open Classical in if t < 1 / 2 then g3 t else 0) := by
  classical
  unfold f3 fR
  have hx : expv (fun _ : Fin 1 => Real.log t) = fun _ => t := by funext i; unfold expv; exact Real.exp_log ht
  rw [hx]
  by_cases h : t < 1 / 2
  · rw [if_pos ((cnd3_iff _).2 h), if_pos h]; unfold G3 g3; field_simp
  · rw [if_neg (fun h' => h ((cnd3_iff _).1 h')), if_neg h]; simp

theorem ind2_eq (t : ℝ) : (Set.Ioc aa 1).indicator (fun t => f2 (fun _ => Real.log t) / t) t =
    EG * (Set.Icc (1 / 2) 1).indicator g2 t := by
  classical
  have ha : aa < 1 / 2 := by unfold aa; norm_num
  by_cases h : t ∈ Set.Ioc aa 1
  · rw [Set.indicator_of_mem h, f2_log t (lt_trans aa_pos h.1)]
    by_cases h2 : 1 / 2 ≤ t
    · rw [if_pos h2, Set.indicator_of_mem (show t ∈ Set.Icc (1 / 2 : ℝ) 1 from ⟨h2, h.2⟩)]
    · rw [if_neg h2, Set.indicator_of_notMem (fun hm : t ∈ Set.Icc (1 / 2 : ℝ) 1 => h2 hm.1)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm : t ∈ Set.Icc (1 / 2 : ℝ) 1 =>
      h ⟨by linarith [hm.1], hm.2⟩), mul_zero]

theorem ind3_eq (t : ℝ) : (Set.Ioc aa 1).indicator (fun t => f3 (fun _ => Real.log t) / t) t =
    EG * (Set.Ioo aa (1 / 2)).indicator g3 t := by
  classical
  by_cases h : t ∈ Set.Ioc aa 1
  · rw [Set.indicator_of_mem h, f3_log t (lt_trans aa_pos h.1)]
    by_cases h2 : t < 1 / 2
    · rw [if_pos h2, Set.indicator_of_mem (show t ∈ Set.Ioo aa (1 / 2) from ⟨h.1, h2⟩)]
    · rw [if_neg h2, Set.indicator_of_notMem (fun hm : t ∈ Set.Ioo aa (1 / 2) => h2 hm.2)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm : t ∈ Set.Ioo aa (1 / 2) =>
      h ⟨hm.1, by linarith [hm.2]⟩), mul_zero]

noncomputable def I2 : ℝ := ∫ t, (Set.Icc (1 / 2) 1).indicator g2 t
noncomputable def I3 : ℝ := ∫ t, (Set.Ioo aa (1 / 2)).indicator g3 t
noncomputable def I4 : ℝ := ∫ t, (Set.Ioo aa (1 / 2)).indicator g4 t

theorem f2_box : ∫ σ in (boxA 1 aa aa_pos aa_lt_one : Set (Fin 1 → ℝ)), f2 σ = EG * I2 ∧
    Integrable ((Set.Icc (1 / 2) 1).indicator g2) := by
  obtain ⟨h1, h2⟩ := box_int_fin1 f2 (integrableOn_box _ _ _ _ f2_measurable _ (fun σ _ => f2_bound σ))
  simp only [ind2_eq] at h1 h2
  refine ⟨by rw [h1, integral_const_mul]; rfl, ?_⟩
  have := h2.const_mul (EG⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ EG_pos.ne', one_mul] at this
  exact this

theorem f3_box : ∫ σ in (boxA 1 aa aa_pos aa_lt_one : Set (Fin 1 → ℝ)), f3 σ = EG * I3 ∧
    Integrable ((Set.Ioo aa (1 / 2)).indicator g3) := by
  obtain ⟨h1, h2⟩ := box_int_fin1 f3 (integrableOn_box _ _ _ _ f3_measurable _ (fun σ _ => f3_bound σ))
  simp only [ind3_eq] at h1 h2
  refine ⟨by rw [h1, integral_const_mul]; rfl, ?_⟩
  have := h2.const_mul (EG⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ EG_pos.ne', one_mul] at this
  exact this

/-! ## The chain pieces summed: `h(t, 1)` -/

theorem h86_zero {i : ℕ} {x : ℝ} (hx : 0 ≤ x) (h : 1 ≤ i * x) : h86 i x = 0 := by
  classical
  unfold h86
  have : (fun v : Fin i → ℝ => if HRegion86 i x v then 1 / ((∏ j, v j) * (1 - x - ∑ j, v j)) else 0) = fun _ => 0 := by
    funext v
    rw [if_neg]
    rintro ⟨-, h2, -, -, -, h6⟩
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; simp at h; linarith
      · exact h0
    have hs : (i : ℝ) * x < ∑ j, v j := by
      have : ∑ _j : Fin i, x < ∑ j, v j := Finset.sum_lt_sum_of_nonempty ⟨⟨0, hi⟩, mem_univ _⟩ (fun j _ => h2 j)
      simpa using this
    have hc : x < chainV v (i - 1) := by unfold chainV; rw [dif_pos (by omega)]; exact h2 _
    linarith
  rw [this, MeasureTheory.integral_zero]

theorem sum_h86_eq_hS {t : ℝ} (ht : mm < t) :
    ∑ k ∈ Icc 1 42, h86 (2 * k) t = hS t := by
  have hm : mm = 1 / 85 := rfl
  have ht0 : 0 < t := by linarith
  unfold hS
  have hfl : ⌊1 / t⌋₊ + 1 ≤ 100 := by
    have : 1 / t < 85 := by rw [div_lt_iff₀ ht0]; linarith
    have := Nat.floor_lt' (by norm_num : (85 : ℕ) ≠ 0) |>.2 (by exact_mod_cast this)
    omega
  have hz : ∀ k, 43 ≤ k → h86 (2 * k) t = 0 := by
    intro k hk
    apply h86_zero ht0.le
    have : (86 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 86 ≤ 2 * k)
    nlinarith
  have hz2 : ∀ k, ⌊1 / t⌋₊ + 1 < k → h86 (2 * k) t = 0 := by
    intro k hk
    apply h86_zero ht0.le
    have h1 : 1 / t < (⌊1 / t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (⌊1 / t⌋₊ : ℝ) + 1 < k := by exact_mod_cast hk
    have h3 : 1 < k * t := by
      have := lt_trans h1 h2
      rw [div_lt_iff₀ ht0] at this; linarith
    have : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [this]; nlinarith
  rw [Finset.sum_subset (s₁ := Icc 1 42) (s₂ := Icc 1 100) (Icc_subset_Icc le_rfl (by norm_num))
      (fun k hk hk' => by simp at hk hk'; exact hz k (by omega)),
    Finset.sum_subset (s₁ := Icc 1 (⌊1 / t⌋₊ + 1)) (s₂ := Icc 1 100) (Icc_subset_Icc le_rfl hfl)
      (fun k hk hk' => by simp only [mem_Icc, not_and, not_le] at hk hk'; exact hz2 k (by omega))]

theorem sum_KA (t : ℝ) : ∑ k ∈ Icc 1 42, KA (2 * k) t = EG * (Set.Ioo aa (1 / 2)).indicator g4 t := by
  classical
  unfold KA
  by_cases h : aa < t ∧ t < 1 / 2
  · simp only [if_pos h]
    rw [Set.indicator_of_mem h, ← Finset.mul_sum]
    unfold g4 EG
    by_cases hm : t ≤ mm
    · rw [Wf_zero_of_le hm]; simp
    · push Not at hm
      rw [sum_h86_eq_hS hm]; ring
  · simp only [if_neg h, Finset.sum_const_zero]
    rw [Set.indicator_of_notMem h, mul_zero]

theorem chain_box : ∑ k ∈ Icc 1 42, ∫ σ in (boxA (2 * k + 1) aa aa_pos aa_lt_one : Set (Fin (2 * k + 1) → ℝ)), fA (2 * k) σ =
    EG * I4 ∧ Integrable ((Set.Ioo aa (1 / 2)).indicator g4) := by
  have hK : ∀ k ∈ Icc 1 42, ∫ σ in (boxA (2 * k + 1) aa aa_pos aa_lt_one : Set (Fin (2 * k + 1) → ℝ)), fA (2 * k) σ =
      ∫ t, KA (2 * k) t ∧ Integrable (KA (2 * k)) := by
    intro k hk; rw [mem_Icc] at hk; exact IA_eq_KA (by omega)
  have hint : Integrable (fun t => ∑ k ∈ Icc 1 42, KA (2 * k) t) :=
    integrable_finsetSum _ (fun k hk => (hK k hk).2)
  have e : (fun t => ∑ k ∈ Icc 1 42, KA (2 * k) t) = fun t => EG * (Set.Ioo aa (1 / 2)).indicator g4 t := funext sum_KA
  constructor
  · rw [Finset.sum_congr rfl (fun k hk => (hK k hk).1), ← integral_finsetSum _ (fun k hk => (hK k hk).2)]
    rw [e, integral_const_mul]; rfl
  · rw [e] at hint
    have := hint.const_mul (EG⁻¹)
    simp only [← mul_assoc, inv_mul_cancel₀ EG_pos.ne', one_mul] at this
    exact this

/-! ## `𝓜(W) = −I2 + I3 − I4` -/

theorem ind_ae_eq (g : ℝ → ℝ) (hg : ∀ t, 0 < t → t ≤ aa → g t = 0) :
    (Set.Ioc 0 (1 / 2)).indicator g =ᵐ[volume] (Set.Ioo aa (1 / 2)).indicator g := by
  have hs : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({1 / 2} : Set ℝ) := (Set.countable_singleton _).ae_notMem _
  filter_upwards [hs] with t ht
  have ht' : t ≠ 1 / 2 := ht
  by_cases h1 : t ∈ Set.Ioo aa (1 / 2)
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) (1 / 2) from ⟨lt_trans aa_pos h1.1, h1.2.le⟩)]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : t ∈ Set.Ioc 0 (1 / 2)
    · rw [Set.indicator_of_mem h2]
      apply hg t h2.1
      by_contra hc; push Not at hc
      exact h1 ⟨hc, lt_of_le_of_ne h2.2 ht'⟩
    · rw [Set.indicator_of_notMem h2]

theorem g3_zero (t : ℝ) (ht : 0 < t) (h : t ≤ aa) : g3 t = 0 := by
  unfold g3; rw [Wf_zero_of_le (le_trans h aa_lt_mm.le)]; simp

theorem g4_zero (t : ℝ) (ht : 0 < t) (h : t ≤ aa) : g4 t = 0 := by
  unfold g4; rw [Wf_zero_of_le (le_trans h aa_lt_mm.le)]; simp

theorem interval_eq (g : ℝ → ℝ) (hg : ∀ t, 0 < t → t ≤ aa → g t = 0) :
    ∫ t in (0 : ℝ)..(1 / 2), g t = ∫ t, (Set.Ioo aa (1 / 2)).indicator g t := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_indicator measurableSet_Ioc]
  exact integral_congr_ae (ind_ae_eq g hg)

theorem interval_integrable (g : ℝ → ℝ) (hg : ∀ t, 0 < t → t ≤ aa → g t = 0)
    (hI : Integrable ((Set.Ioo aa (1 / 2)).indicator g)) : IntervalIntegrable g volume 0 (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), ← integrable_indicator_iff measurableSet_Ioc]
  exact hI.congr (ind_ae_eq g hg).symm

theorem mvalW_eq : mvalW = -I2 + I3 - I4 := by
  obtain ⟨-, hI3⟩ := f3_box
  obtain ⟨-, hI4⟩ := chain_box
  unfold mvalW
  have e2 : ∫ t in (1 / 2 : ℝ)..1, (W1 - Wf t) / ((1 - t) * t) = I2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    unfold I2
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc]
    rfl
  have e3 : ∫ t in (0 : ℝ)..(1 / 2), Wf t * (1 / (1 - t) - hS t) / t =
      (∫ t in (0 : ℝ)..(1 / 2), g3 t) - ∫ t in (0 : ℝ)..(1 / 2), g4 t := by
    rw [← intervalIntegral.integral_sub (interval_integrable g3 g3_zero hI3) (interval_integrable g4 g4_zero hI4)]
    congr 1; funext t
    unfold g3 g4
    rw [mul_sub, sub_div, mul_one_div, div_div]
  rw [e2, e3, interval_eq g3 g3_zero, interval_eq g4 g4_zero]
  unfold I3 I4
  ring

end Omega3.M11

end

section

/-!
# M11 helper: copy of M07_Chi (set-form Jurkat–Richert conditions), plus chain prefix form and tuple sums

`ChiG C Y D`: every nonempty `E ⊆ D` with `C |E|` has `Π E · p(Π E)² < Y`. Peeling the largest prime
(`chiG_insert`, generalising M08's `chi_insert`), unions with a lower block (`chiG_union`), and the
translation of `chiProp`, `chiMinusProp`, `chiStarProp`, `chiPlusProp` (see `M07_PLAN.md` §0, §1).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

theorem prod_pos_of_primes {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : 0 < ∏ p ∈ E, p :=
  prod_pos fun p hp => (hE p hp).pos

theorem omega_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : ω (∏ p ∈ E, p) = E.card := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_prod hE]

theorem minFac_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (hne : E.Nonempty) :
    (∏ p ∈ E, p).minFac ∈ E ∧ ∀ q ∈ E, (∏ p ∈ E, p).minFac ≤ q := by
  have h1 : (∏ p ∈ E, p) ≠ 1 := by
    obtain ⟨q, hq⟩ := hne
    intro h
    have := Finset.dvd_prod_of_mem (fun p => p) hq
    rw [h] at this
    exact (hE q hq).ne_one (Nat.dvd_one.1 this)
  have hmem : (∏ p ∈ E, p).minFac ∈ (∏ p ∈ E, p).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime h1, Nat.minFac_dvd _, (prod_pos_of_primes hE).ne'⟩
  rw [Nat.primeFactors_prod hE] at hmem
  refine ⟨hmem, fun q hq => Nat.minFac_le_of_dvd (hE q hq).two_le (Finset.dvd_prod_of_mem _ hq)⟩

theorem minFac_prod_insert {E : Finset ℕ} {M : ℕ} (hE : ∀ p ∈ E, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ E, q < M) (hne : E.Nonempty) :
    (∏ p ∈ insert M E, p).minFac = (∏ p ∈ E, p).minFac := by
  have hE' : ∀ p ∈ insert M E, p.Prime := by
    intro p hp; rcases mem_insert.1 hp with rfl | hp
    · exact hM
    · exact hE p hp
  obtain ⟨h1, h2⟩ := minFac_prod hE' (insert_nonempty M E)
  obtain ⟨h3, h4⟩ := minFac_prod hE hne
  apply le_antisymm
  · exact h2 _ (mem_insert_of_mem h3)
  · rcases mem_insert.1 h1 with h | h
    · exfalso
      have := h4 _ h3
      have := hlt _ h3
      have := h2 _ (mem_insert_of_mem h3)
      omega
    · exact h4 _ h

/-- The generalised Jurkat–Richert condition in set form. -/
def ChiG (C : ℕ → Prop) (Y : ℝ) (D : Finset ℕ) : Prop :=
  ∀ E ⊆ D, E.Nonempty → C E.card →
    ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2 < Y

theorem chiG_empty (C : ℕ → Prop) (Y : ℝ) : ChiG C Y ∅ := fun E hE hne _ => by
  rw [subset_empty] at hE; subst hE; exact absurd hne (by simp)

theorem chiG_mono {C : ℕ → Prop} {Y : ℝ} {D D' : Finset ℕ} (h : D' ⊆ D) (H : ChiG C Y D) : ChiG C Y D' :=
  fun E hE hne hc => H E (hE.trans h) hne hc

theorem chiG_mono_class {C C' : ℕ → Prop} {Y : ℝ} {D : Finset ℕ} (h : ∀ j, C' j → C j) (H : ChiG C Y D) :
    ChiG C' Y D := fun E hE hne hc => H E hE hne (h _ hc)

theorem chiG_congr_class {C C' : ℕ → Prop} {Y : ℝ} {D : Finset ℕ} (h : ∀ j, C' j ↔ C j) :
    ChiG C' Y D ↔ ChiG C Y D :=
  ⟨chiG_mono_class (fun j hj => (h j).2 hj), chiG_mono_class (fun j hj => (h j).1 hj)⟩

/-- Divisor form ↔ set form. -/
theorem chiG_iff (C : ℕ → Prop) (Y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    (∀ h ∈ (∏ p ∈ D, p).divisors, h ≠ 1 → C (ω h) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < Y) ↔ ChiG C Y D := by
  have hD0 : (∏ p ∈ D, p) ≠ 0 := (prod_pos_of_primes hD).ne'
  have hsq : Squarefree (∏ p ∈ D, p) := SelbergPort.prod_primes_squarefree D hD
  constructor
  · intro H E hED hne hpar
    have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
    apply H
    · rw [Nat.mem_divisors]; exact ⟨prod_dvd_prod_of_subset _ _ _ hED, hD0⟩
    · obtain ⟨q, hq⟩ := hne
      intro h
      have := Finset.dvd_prod_of_mem (fun p => p) hq
      rw [h] at this
      exact (hEp q hq).ne_one (Nat.dvd_one.1 this)
    · rwa [omega_prod hEp]
  · intro H h hh h1 hpar
    rw [Nat.mem_divisors] at hh
    have hsub : h.primeFactors ⊆ D := by
      have := Nat.primeFactors_mono hh.1 hD0
      rwa [Nat.primeFactors_prod hD] at this
    have hprod : ∏ p ∈ h.primeFactors, p = h := Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hh.1)
    have hne : h.primeFactors.Nonempty := by
      rw [Nat.nonempty_primeFactors]
      have : h ≠ 0 := fun h0 => hD0 (by rw [h0] at hh; exact Nat.eq_zero_of_zero_dvd hh.1)
      omega
    have := H _ hsub hne (by
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hpar; exact hpar)
    rwa [hprod] at this

/-- Class of `χ`: `ν` even or `ν ≤ 1/m`. -/
def Cchi (j : ℕ) : Prop := Even j ∨ (j : ℝ) ≤ 1 / mm
/-- Class of `χ*`: `ν` odd and `ν ≤ 1/m`. -/
def Cst (j : ℕ) : Prop := Odd j ∧ (j : ℝ) ≤ 1 / mm

theorem chi_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiProp y mm (∏ p ∈ D, p) ↔ ChiG Cchi y D := by
  rw [← chiG_iff Cchi y hD]; rfl

theorem chiMinus_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiMinusProp y (∏ p ∈ D, p) ↔ ChiG Even y D := by
  rw [← chiG_iff Even y hD]; rfl

theorem chiPlus_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiPlusProp y (∏ p ∈ D, p) ↔ ChiG Odd y D := by
  rw [← chiG_iff Odd y hD]; rfl

theorem chiStar_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiStarProp y mm (∏ p ∈ D, p) ↔ ChiG Cst y D := by
  rw [← chiG_iff Cst y hD]
  unfold chiStarProp Cst
  constructor
  · intro H h hh h1 hc; exact H h hh h1 hc.1 hc.2
  · intro H h hh h1 hc1 hc2; exact H h hh h1 ⟨hc1, hc2⟩

/-- `χ = χ⁻ ∧ χ*`. -/
theorem chiG_chi_iff (Y : ℝ) (D : Finset ℕ) : ChiG Cchi Y D ↔ ChiG Even Y D ∧ ChiG Cst Y D := by
  constructor
  · intro H
    exact ⟨chiG_mono_class (fun j hj => Or.inl hj) H, chiG_mono_class (fun j hj => Or.inr hj.2) H⟩
  · rintro ⟨H1, H2⟩ E hE hne hc
    rcases hc with hc | hc
    · exact H1 E hE hne hc
    · rcases Nat.even_or_odd E.card with he | ho
      · exact H1 E hE hne he
      · exact H2 E hE hne ⟨ho, hc⟩

/-- Peeling the largest prime. -/
theorem chiG_insert (C : ℕ → Prop) (Y : ℝ) {D : Finset ℕ} {M : ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) :
    ChiG C Y (insert M D) ↔ ((C 1 → (M : ℝ) ^ 3 < Y) ∧ ChiG (fun j => C (j + 1)) (Y / M) D) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hMD : M ∉ D := fun h => lt_irrefl M (hlt M h)
  have conv : ∀ E' ⊆ D, E'.Nonempty →
      ((((∏ p ∈ insert M E', p : ℕ) : ℝ) * (((∏ p ∈ insert M E', p).minFac : ℕ) : ℝ) ^ 2 < Y) ↔
        (((∏ p ∈ E', p : ℕ) : ℝ) * (((∏ p ∈ E', p).minFac : ℕ) : ℝ) ^ 2 < Y / M)) := by
    intro E' hE' hne
    have hE'p : ∀ p ∈ E', p.Prime := fun p hp => hD p (hE' hp)
    have hME' : M ∉ E' := fun h => hMD (hE' h)
    rw [minFac_prod_insert hE'p hM (fun q hq => hlt q (hE' hq)) hne, prod_insert hME', lt_div_iff₀ hM0]
    push_cast
    constructor <;> intro h <;> linarith
  have single : (((∏ p ∈ ({M} : Finset ℕ), p : ℕ) : ℝ) * (((∏ p ∈ ({M} : Finset ℕ), p).minFac : ℕ) : ℝ) ^ 2) =
      (M : ℝ) ^ 3 := by
    rw [prod_singleton, hM.minFac_eq]; ring
  constructor
  · intro H
    refine ⟨fun hσ => ?_, fun E' hE' hne hpar => ?_⟩
    · have := H {M} (by simp) (singleton_nonempty M) (by simpa using hσ)
      rwa [single] at this
    · have hME' : M ∉ E' := fun h => hMD (hE' h)
      have := H (insert M E') (insert_subset_insert M hE') (insert_nonempty M E') (by
        rw [card_insert_of_notMem hME']; exact hpar)
      exact (conv E' hE' hne).1 this
  · rintro ⟨hc, H⟩
    have A : ∀ E' ⊆ D, C (E'.card + 1) →
        ((∏ p ∈ insert M E', p : ℕ) : ℝ) * (((∏ p ∈ insert M E', p).minFac : ℕ) : ℝ) ^ 2 < Y := by
      intro E' hE' hpar
      rcases E'.eq_empty_or_nonempty with rfl | hne
      · rw [insert_empty, single]; exact hc (by simpa using hpar)
      · exact (conv E' hE' hne).2 (H E' hE' hne hpar)
    intro E hE hne hpar
    by_cases hME : M ∈ E
    · have hEe : E = insert M (E.erase M) := (insert_erase hME).symm
      have hsub : E.erase M ⊆ D := by
        intro x hx
        rcases mem_insert.1 (hE (mem_of_mem_erase hx)) with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have hcard : E.card = (E.erase M).card + 1 := (card_erase_add_one hME).symm
      rw [hcard] at hpar
      rw [hEe]; exact A _ hsub hpar
    · have hED : E ⊆ D := by
        intro x hx
        rcases mem_insert.1 (hE hx) with h | h
        · exact absurd (h ▸ hx) hME
        · exact h
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
      set q := E.max' hne with hq
      have hqE : q ∈ E := max'_mem E hne
      have hcard : E.card = (E.erase q).card + 1 := (card_erase_add_one hqE).symm
      rw [hcard] at hpar
      have hsub : E.erase q ⊆ D := fun x hx => hED (mem_of_mem_erase hx)
      have hA := A _ hsub hpar
      have hMer : M ∉ E.erase q := fun h => hMD (hsub h)
      have hIp : ∀ p ∈ insert M (E.erase q), p.Prime := by
        intro p hp; rcases mem_insert.1 hp with rfl | hp
        · exact hM
        · exact hEp p (mem_of_mem_erase hp)
      have hprod : (∏ p ∈ E, p) ≤ ∏ p ∈ insert M (E.erase q), p := by
        rw [(mul_prod_erase E (fun p => p) hqE).symm, prod_insert hMer]
        exact Nat.mul_le_mul_right _ (hlt q (hED hqE)).le
      have hmf : (∏ p ∈ E, p).minFac ≤ (∏ p ∈ insert M (E.erase q), p).minFac := by
        obtain ⟨h1, _⟩ := minFac_prod hIp (insert_nonempty M _)
        obtain ⟨_, h4⟩ := minFac_prod hEp hne
        rcases mem_insert.1 h1 with h | h
        · rw [h]; exact le_trans (h4 q hqE) (hlt q (hED hqE)).le
        · exact h4 _ (mem_of_mem_erase h)
      have hmf' : (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ≤ (((∏ p ∈ insert M (E.erase q), p).minFac : ℕ) : ℝ) := by
        exact_mod_cast hmf
      have hprod' : ((∏ p ∈ E, p : ℕ) : ℝ) ≤ ((∏ p ∈ insert M (E.erase q), p : ℕ) : ℝ) := by
        exact_mod_cast hprod
      calc ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2
          ≤ ((∏ p ∈ insert M (E.erase q), p : ℕ) : ℝ) *
              (((∏ p ∈ insert M (E.erase q), p).minFac : ℕ) : ℝ) ^ 2 := by
            apply mul_le_mul hprod' (pow_le_pow_left₀ (by positivity) hmf' 2) (by positivity) (by positivity)
        _ < Y := hA


/-! ## Chains: prefix form of `ChiG` on a decreasing tuple -/

/-- Prefix product `Π_{l ≤ j} v_l`. -/
def preP {m : ℕ} (v : Fin m → ℕ) (j : Fin m) : ℕ := ∏ l : Fin m, if l ≤ j then v l else 1

theorem image_succ_eq {m : ℕ} (v : Fin (m + 1) → ℕ) :
    Finset.univ.image v = insert (v 0) (Finset.univ.image (Fin.tail v)) := by
  ext a; simp only [mem_image, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · left; rfl
    · right; exact ⟨j, rfl⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, rfl⟩

theorem chiG_chain : ∀ (m : ℕ) (C : ℕ → Prop) (Y : ℝ) (v : Fin m → ℕ), StrictAnti v → (∀ i, (v i).Prime) →
    (ChiG C Y (Finset.univ.image v) ↔
      ∀ j : Fin m, C (j.val + 1) → ((preP v j : ℕ) : ℝ) * ((v j : ℕ) : ℝ) ^ 2 < Y) := by
  intro m
  induction m with
  | zero =>
    intro C Y v _ _
    have : Finset.univ.image v = ∅ := by simp
    rw [this]; exact ⟨fun _ j => j.elim0, fun _ => chiG_empty _ _⟩
  | succ m ih =>
    intro C Y v hv hp
    have htail : StrictAnti (Fin.tail v) := fun a b hab => hv (Fin.succ_lt_succ_iff.2 hab)
    have hpt : ∀ i, (Fin.tail v i).Prime := fun i => hp _
    have hlt : ∀ q ∈ Finset.univ.image (Fin.tail v), q < v 0 := by
      intro q hq; rw [mem_image] at hq; obtain ⟨j, _, rfl⟩ := hq
      exact hv (Fin.succ_pos j)
    have hDp : ∀ q ∈ Finset.univ.image (Fin.tail v), q.Prime := by
      intro q hq; rw [mem_image] at hq; obtain ⟨j, _, rfl⟩ := hq; exact hpt j
    rw [image_succ_eq, chiG_insert C Y hDp (hp 0) hlt, ih (fun j => C (j + 1)) (Y / v 0) _ htail hpt,
      Fin.forall_fin_succ]
    have hv0 : (0 : ℝ) < v 0 := by exact_mod_cast (hp 0).pos
    have hP0 : preP v 0 = v 0 := by
      unfold preP; rw [Fin.prod_univ_succ]
      simp only [le_refl, ite_true]
      rw [Finset.prod_eq_one (fun l _ => if_neg (not_le.2 (Fin.succ_pos l))), mul_one]
    have hPs : ∀ j : Fin m, preP v j.succ = v 0 * preP (Fin.tail v) j := by
      intro j; unfold preP; rw [Fin.prod_univ_succ]
      simp only [Fin.zero_le, ite_true, Fin.succ_le_succ_iff]; rfl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hc => ?_, fun j hc => ?_⟩
      · rw [hP0]; have := h1 hc; simp only [Fin.val_zero] at *; nlinarith [this]
      · have := h2 j hc
        rw [hPs j]; push_cast
        rw [lt_div_iff₀ hv0] at this
        have e : (Fin.tail v j : ℝ) = (v j.succ : ℝ) := rfl
        rw [e] at this; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun hc => ?_, fun j hc => ?_⟩
      · have := h1 hc; rw [hP0] at this; simp only [Fin.val_zero] at *; nlinarith [this]
      · have := h2 j hc
        rw [hPs j] at this; push_cast at this
        rw [lt_div_iff₀ hv0]
        have e : (Fin.tail v j : ℝ) = (v j.succ : ℝ) := rfl
        rw [e]; linarith

/-! ## Tuple sums -/

theorem sum_powersetCard_tuples' (S : Finset ℕ) (m : ℕ) (H : Finset ℕ → ℝ) :
    ∑ U ∈ S.powersetCard m, H U =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin m => S), (if StrictAnti q then H (Finset.univ.image q) else 0) := by
  classical
  cases m with
  | zero =>
    simp only [Finset.powersetCard_zero, Finset.sum_singleton]
    have : Fintype.piFinset (fun _ : Fin 0 => S) = {Fin.elim0} := by
      ext q; simp only [Fintype.mem_piFinset, mem_singleton]
      exact ⟨fun _ => funext (fun i => i.elim0), fun _ i => i.elim0⟩
    have hsa : StrictAnti (Fin.elim0 : Fin 0 → ℕ) := fun a => a.elim0
    rw [this, Finset.sum_singleton, if_pos hsa]
    rfl
  | succ n =>
    have h := Palprimes.MT.sum_powersetCard_tuples S n (fun l => H l.toFinset)
    have e1 : ∀ U ∈ S.powersetCard (n + 1), H U = H (toDec U).toFinset := by
      intro U _; unfold toDec; rw [Finset.sort_toFinset]
    rw [Finset.sum_congr rfl e1, h]
    apply Finset.sum_congr rfl; intro q _
    split_ifs
    · rw [Palprimes.MT.image_eq_toFinset]
    · rfl

theorem sum_piFinset_snoc {n : ℕ} (A : Finset ℕ) (F : (Fin (n + 1) → ℕ) → ℝ) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => A), F q =
      ∑ p ∈ A, ∑ v ∈ Fintype.piFinset (fun _ : Fin n => A), F (Fin.snoc v p) := by
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun q => (q (Fin.last n), Fin.init q)) (fun x => Fin.snoc x.2 x.1)
  · intro q hq
    rw [Fintype.mem_piFinset] at hq
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨hq _, fun i => hq _⟩
  · intro x hx
    rw [mem_product, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact hx.2 i'
    · rw [Fin.snoc_last]; exact hx.1
  · intro q _; exact Fin.snoc_init_self q
  · intro x _; simp
  · intro q _; rw [Fin.snoc_init_self]

theorem sum_piFinset_one (A : Finset ℕ) (F : (Fin 1 → ℕ) → ℝ) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => A), F q = ∑ p ∈ A, F (fun _ => p) := by
  apply Finset.sum_nbij' (fun q => q 0) (fun p => fun _ => p)
  · intro q hq; rw [Fintype.mem_piFinset] at hq; exact hq 0
  · intro p hp; rw [Fintype.mem_piFinset]; intro _; exact hp
  · intro q _; funext i; rw [Fin.fin_one_eq_zero i]
  · intro p _; rfl
  · intro q _; congr 1; funext i; rw [Fin.fin_one_eq_zero i]

end Omega3.M11

end

section

/-!
# M11 helper: the chain conditions of `E11` on decreasing tuples of primes, in log coordinates

For a strictly decreasing tuple `v` of `m'+1 ≤ 85` primes and a prime `p`, the conditions of the `n`-sum of `E11`
(`n = Π v`, `p < p(n)`, `n p(n) < y/p`, `χ̄_y(n) = 1`, `n ∣ P(y)`) and `p < y^{1/2}` are `ExplA (m'+1)` of
`x = (log v_j/log y, log p/log y)`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

/-- Log coordinates of a tuple. -/
noncomputable def xq {r : ℕ} (y : ℝ) (q : Fin r → ℕ) : Fin r → ℝ := fun i => Real.log (q i) / Real.log y

theorem primes_image {m : ℕ} (v : Fin m → ℕ) (hp : ∀ i, (v i).Prime) : ∀ p ∈ Finset.univ.image v, p.Prime := by
  intro p hp'; rw [mem_image] at hp'; obtain ⟨i, _, rfl⟩ := hp'; exact hp i

theorem prod_image_sa {m : ℕ} (v : Fin m → ℕ) (hv : StrictAnti v) : ∏ p ∈ Finset.univ.image v, p = ∏ i, v i :=
  prod_image (fun a _ b _ h => hv.injective h)

theorem chi_tuple {m : ℕ} (hm : m ≤ 85) (y : ℝ) (v : Fin m → ℕ) (hv : StrictAnti v) (hp : ∀ i, (v i).Prime) :
    chiProp y mm (∏ i, v i) ↔ ∀ j : Fin m, ((preP v j : ℕ) : ℝ) * ((v j : ℕ) : ℝ) ^ 2 < y := by
  rw [← prod_image_sa v hv, chi_iff' y (primes_image v hp), chiG_chain m Cchi y v hv hp]
  constructor
  · intro h j; exact h j (Or.inr (by rw [show (1 : ℝ) / mm = 85 by norm_num [mm]]; push_cast; have := j.isLt; exact_mod_cast (by omega : j.val + 1 ≤ 85)))
  · intro h j _; exact h j

theorem minFac_tuple {m' : ℕ} (v : Fin (m' + 1) → ℕ) (hv : StrictAnti v) (hp : ∀ i, (v i).Prime) :
    (∏ i, v i).minFac = v (Fin.last m') := by
  rw [← prod_image_sa v hv]
  obtain ⟨h1, h2⟩ := minFac_prod (primes_image v hp) (by simp)
  apply le_antisymm (h2 _ (mem_image_of_mem _ (mem_univ _)))
  rw [mem_image] at h1
  obtain ⟨i, _, hi⟩ := h1
  rw [← hi]
  exact hv.antitone (Fin.le_last i)

theorem preP_init {m' : ℕ} (v : Fin (m' + 1) → ℕ) (j : Fin m') : preP (Fin.init v) j = preP v j.castSucc := by
  unfold preP
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_le_castSucc_iff]
  rw [if_neg (not_le.2 (Fin.castSucc_lt_last j)), mul_one]
  rfl

theorem chibar_tuple {m' : ℕ} (hm : m' + 1 ≤ 85) (y : ℝ) (v : Fin (m' + 1) → ℕ) (hv : StrictAnti v)
    (hp : ∀ i, (v i).Prime) :
    chibar y mm (∏ i, v i) = open Classical in
      if (∀ j : Fin m', ((preP v j.castSucc : ℕ) : ℝ) * ((v j.castSucc : ℕ) : ℝ) ^ 2 < y) ∧
        ¬ (((preP v (Fin.last m') : ℕ) : ℝ) * ((v (Fin.last m') : ℕ) : ℝ) ^ 2 < y) then 1 else 0 := by
  classical
  have hne : (∏ i, v i) ≠ 1 := by
    intro h
    have := Finset.dvd_prod_of_mem v (mem_univ (0 : Fin (m' + 1)))
    rw [h] at this; exact (hp 0).ne_one (Nat.dvd_one.1 this)
  have hinit : StrictAnti (Fin.init v) := fun a b hab => hv (Fin.castSucc_lt_castSucc_iff.2 hab)
  have hpi : ∀ i, (Fin.init v i).Prime := fun i => hp _
  have hdiv : (∏ i, v i) / (∏ i, v i).minFac = ∏ i, Fin.init v i := by
    rw [minFac_tuple v hv hp, Fin.prod_univ_castSucc, Nat.mul_div_cancel _ (hp _).pos]; rfl
  unfold chibar chi
  rw [if_neg hne, hdiv]
  have hA := chi_tuple (by omega) y (Fin.init v) hinit hpi
  have hB := chi_tuple hm y v hv hp
  simp only [preP_init] at hA
  rw [Fin.forall_fin_succ'] at hB
  have e : ∀ j : Fin m', Fin.init v j = v j.castSucc := fun j => rfl
  simp only [e] at hA
  have e2 : (∏ i, Fin.init v i) = ∏ i : Fin m', v i.castSucc := rfl
  rw [e2]
  by_cases h1 : ∀ j : Fin m', ((preP v j.castSucc : ℕ) : ℝ) * ((v j.castSucc : ℕ) : ℝ) ^ 2 < y
  · by_cases h2 : ((preP v (Fin.last m') : ℕ) : ℝ) * ((v (Fin.last m') : ℕ) : ℝ) ^ 2 < y
    · rw [if_pos (hA.2 h1), if_pos (hB.2 ⟨h1, h2⟩), if_neg (fun h => h.2 h2)]; ring
    · rw [if_pos (hA.2 h1), if_neg (fun h => h2 (hB.1 h).2), if_pos ⟨h1, h2⟩]; ring
  · rw [if_neg (fun h => h1 (hA.1 h)), if_neg (fun h => h1 (hB.1 h).1), if_neg (fun h => h1 h.1)]; ring

/-! ## Log coordinates -/

theorem log_div_lt_iff {y : ℝ} (hy : 1 < y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a / Real.log y < Real.log b / Real.log y ↔ a < b := by
  have hl := Real.log_pos hy
  rw [div_lt_div_iff_of_pos_right hl, Real.log_lt_log_iff ha hb]

theorem log_prod_ite {m : ℕ} (v : Fin m → ℕ) (hp : ∀ i, (v i).Prime) (P : Fin m → Prop) [DecidablePred P] :
    Real.log (((∏ l : Fin m, if P l then v l else 1 : ℕ) : ℕ) : ℝ) = ∑ l : Fin m, if P l then Real.log (v l) else 0 := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl; intro l _; split_ifs <;> simp
  · intro l _; split_ifs
    · exact_mod_cast (hp l).ne_zero
    · norm_num

theorem sum_range_chainV {m : ℕ} (x : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ∑ l ∈ range j, chainV x l = ∑ l : Fin m, if l.val < j then x l else 0 := by
  have h1 : ∑ l ∈ range j, chainV x l = ∑ l ∈ range m, if l < j then chainV x l else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext l; simp only [mem_filter, mem_range]; omega
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun l => if l < j then chainV x l else 0) m]
  apply Finset.sum_congr rfl; intro l _; rw [← init_eq_chainV]

theorem pref_iff {m : ℕ} {y : ℝ} (hy : 1 < y) (v : Fin m → ℕ) (hp : ∀ i, (v i).Prime) (j : Fin m) :
    ((preP v j : ℕ) : ℝ) * ((v j : ℕ) : ℝ) ^ 2 < y ↔ PF (xq y v) (j.val + 1) < 1 := by
  classical
  have hl := Real.log_pos hy
  have hv0 : (0 : ℝ) < v j := by exact_mod_cast (hp j).pos
  have hP0 : (0 : ℝ) < ((preP v j : ℕ) : ℝ) := by
    unfold preP; exact_mod_cast Finset.prod_pos (fun l _ => by split_ifs; exact (hp l).pos; norm_num)
  have hlog : Real.log (((preP v j : ℕ) : ℝ) * ((v j : ℕ) : ℝ) ^ 2) =
      (∑ l : Fin m, if l < j then Real.log (v l) else 0) + 3 * Real.log (v j) := by
    rw [Real.log_mul hP0.ne' (by positivity), Real.log_pow]
    unfold preP
    rw [log_prod_ite v hp (fun l => l ≤ j)]
    have : ∑ l : Fin m, (if l ≤ j then Real.log (v l) else 0) =
        (∑ l : Fin m, if l < j then Real.log (v l) else 0) + Real.log (v j) := by
      have hj : Real.log (v j) = ∑ l : Fin m, (if l = j then Real.log (v l) else 0) := by
        rw [Finset.sum_ite_eq']; simp
      rw [hj, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro l _
      rcases lt_trichotomy l j with h | h | h
      · rw [if_pos h.le, if_pos h, if_neg (ne_of_lt h)]; ring
      · subst h; rw [if_pos le_rfl, if_neg (lt_irrefl _), if_pos rfl]; ring
      · rw [if_neg (not_le.2 h), if_neg (not_lt.2 h.le), if_neg (ne_of_gt h)]; ring
    rw [this]; push_cast; ring
  have hPF : PF (xq y v) (j.val + 1) = ((∑ l : Fin m, if l < j then Real.log (v l) else 0) + 3 * Real.log (v j)) / Real.log y := by
    unfold PF
    simp only [Nat.add_sub_cancel]
    rw [sum_range_chainV _ _ j.isLt.le, ← init_eq_chainV]
    unfold xq
    rw [add_div, Finset.sum_div]
    have : ∀ l : Fin m, (if l.val < j.val then Real.log (v l) / Real.log y else 0) =
        (if l < j then Real.log (v l) else 0) / Real.log y := by
      intro l; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1) | (exfalso; exact h1 h2) | simp
    rw [Finset.sum_congr rfl (fun l _ => this l)]; ring
  rw [hPF, div_lt_one hl, ← hlog, Real.log_lt_log_iff (by positivity) (by linarith)]

end Omega3.M11

end

section

/-!
# M11 helper: `ExplA` of a tuple `(v, p)` of primes is the condition set of the `n`-sum of `E11`
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

theorem xq_snoc_last {n : ℕ} (y : ℝ) (v : Fin n → ℕ) (p : ℕ) :
    xq y (Fin.snoc v p : Fin (n + 1) → ℕ) (Fin.last n) = Real.log p / Real.log y := by
  unfold xq; rw [Fin.snoc_last]

theorem xq_snoc_init {n : ℕ} (y : ℝ) (v : Fin n → ℕ) (p : ℕ) :
    Fin.init (xq y (Fin.snoc v p : Fin (n + 1) → ℕ)) = xq y v := by
  funext i; unfold Fin.init xq; rw [Fin.snoc_castSucc]

theorem strictAnti_xq_iff {m : ℕ} {y : ℝ} (hy : 1 < y) (v : Fin m → ℕ) (hp : ∀ i, (v i).Prime) :
    StrictAnti (xq y v) ↔ StrictAnti v := by
  constructor
  · intro h a b hab
    have := h hab
    unfold xq at this
    exact_mod_cast (log_div_lt_iff hy (by exact_mod_cast (hp b).pos) (by exact_mod_cast (hp a).pos)).1 this
  · intro h a b hab
    unfold xq
    exact (log_div_lt_iff hy (by exact_mod_cast (hp b).pos) (by exact_mod_cast (hp a).pos)).2 (by exact_mod_cast h hab)

theorem lt_one_iff_xq {y : ℝ} (hy : 1 < y) {a : ℕ} (ha : 0 < a) : Real.log a / Real.log y < 1 ↔ (a : ℝ) < y := by
  have hl := Real.log_pos hy
  rw [div_lt_one hl, Real.log_lt_log_iff (by exact_mod_cast ha) (by linarith)]

theorem lt_half_iff_xq {y : ℝ} (hy : 1 < y) {a : ℕ} (ha : 0 < a) :
    Real.log a / Real.log y < 1 / 2 ↔ (a : ℝ) < y ^ ((1 : ℝ) / 2) := by
  have hl := Real.log_pos hy
  rw [div_lt_iff₀ hl, ← Real.log_rpow (by linarith), Real.log_lt_log_iff (by exact_mod_cast ha) (by positivity)]

theorem explA_snoc {m' : ℕ} (hm : m' + 1 ≤ 85) {y : ℝ} (hy : 1 < y) (v : Fin (m' + 1) → ℕ) (p : ℕ)
    (hv : ∀ i, (v i).Prime) (hp : p.Prime) :
    ExplA (m' + 1) (xq y (Fin.snoc v p : Fin (m' + 2) → ℕ)) ↔
      ((p : ℝ) < y ^ ((1 : ℝ) / 2) ∧ StrictAnti v ∧ (∀ j, (v j : ℝ) < y) ∧ p < (∏ i, v i).minFac ∧
        ((∏ i, v i : ℕ) : ℝ) * ((∏ i, v i).minFac : ℝ) < y / p ∧ chibar y mm (∏ i, v i) = 1) := by
  classical
  have hl := Real.log_pos hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hv0 : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast (hv i).pos
  unfold ExplA
  rw [xq_snoc_last, xq_snoc_init]
  by_cases hsa : StrictAnti v
  · have hsx : StrictAnti (xq y v) := (strictAnti_xq_iff hy v hv).2 hsa
    have hmin := minFac_tuple v hsa hv
    have hcb := chibar_tuple hm y v hsa hv
    rw [hmin]
    -- the pieces
    have e1 := lt_half_iff_xq hy hp.pos
    have e2 : (∀ j, Real.log p / Real.log y < xq y v j) ↔ p < v (Fin.last m') := by
      constructor
      · intro h; have := h (Fin.last m'); unfold xq at this
        exact_mod_cast (log_div_lt_iff hy hp0 (hv0 _)).1 this
      · intro h j; unfold xq
        apply (log_div_lt_iff hy hp0 (hv0 _)).2
        have : v (Fin.last m') ≤ v j := hsa.antitone (Fin.le_last j)
        exact_mod_cast lt_of_lt_of_le h this
    have e3 : (∀ j, xq y v j < 1) ↔ ∀ j, (v j : ℝ) < y := by
      constructor
      · intro h j; exact (lt_one_iff_xq hy (hv j).pos).1 (h j)
      · intro h j; exact (lt_one_iff_xq hy (hv j).pos).2 (h j)
    have e5 : (∀ j : ℕ, 1 ≤ j → j < m' + 1 → PF (xq y v) j < 1) ↔
        ∀ j : Fin m', ((preP v j.castSucc : ℕ) : ℝ) * ((v j.castSucc : ℕ) : ℝ) ^ 2 < y := by
      constructor
      · intro h j; rw [pref_iff hy v hv]; exact h _ (by simp) (by simp)
      · intro h j hj1 hj2
        have := (pref_iff hy v hv ⟨j - 1, by omega⟩).1 (h ⟨j - 1, by omega⟩)
        simp only [Fin.castSucc_mk] at this
        rwa [show j - 1 + 1 = j by omega] at this
    have e7 : (1 ≤ PF (xq y v) (m' + 1)) ↔ ¬ (((preP v (Fin.last m') : ℕ) : ℝ) * ((v (Fin.last m') : ℕ) : ℝ) ^ 2 < y) := by
      rw [pref_iff hy v hv, Fin.val_last, not_lt]
    have e6 : (Real.log p / Real.log y + ∑ j, xq y v j + chainV (xq y v) (m' + 1 - 1) < 1) ↔
        ((∏ i, v i : ℕ) : ℝ) * (v (Fin.last m') : ℝ) < y / p := by
      have hc : chainV (xq y v) m' = xq y v (Fin.last m') := by unfold chainV; rw [dif_pos (by omega)]; rfl
      rw [Nat.add_sub_cancel, hc]
      unfold xq
      rw [← Finset.sum_div, ← add_div, ← add_div, div_lt_one hl]
      have hP : (0 : ℝ) < ((∏ i, v i : ℕ) : ℝ) := by exact_mod_cast Finset.prod_pos (fun i _ => (hv i).pos)
      have hlogP : Real.log ((∏ i, v i : ℕ) : ℝ) = ∑ i, Real.log (v i) := by
        rw [Nat.cast_prod, Real.log_prod]; intro i _; exact (hv0 i).ne'
      rw [← hlogP, ← Real.log_mul hp0.ne' hP.ne', ← Real.log_mul (mul_pos hp0 hP).ne' (hv0 _).ne',
        Real.log_lt_log_iff (mul_pos (mul_pos hp0 hP) (hv0 _)) (by linarith), lt_div_iff₀ hp0]
      constructor <;> intro h <;> nlinarith
    have hcb1 : chibar y mm (∏ i, v i) = 1 ↔
        (∀ j : Fin m', ((preP v j.castSucc : ℕ) : ℝ) * ((v j.castSucc : ℕ) : ℝ) ^ 2 < y) ∧
          ¬ (((preP v (Fin.last m') : ℕ) : ℝ) * ((v (Fin.last m') : ℕ) : ℝ) ^ 2 < y) := by
      rw [hcb]; split_ifs with h
      · exact ⟨fun _ => h, fun _ => rfl⟩
      · exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd h' h⟩
    rw [e1, e2, e3, e5, e6, e7, hcb1]
    constructor
    · rintro ⟨h1, h2, h3, -, h5, h6, h7⟩; exact ⟨h1, hsa, h3, h2, h6, h5, h7⟩
    · rintro ⟨h1, -, h3, h2, h6, h5, h7⟩; exact ⟨h1, h2, h3, hsx, h5, h6, h7⟩
  · constructor
    · rintro ⟨-, -, -, h4, -⟩; exact absurd ((strictAnti_xq_iff hy v hv).1 h4) hsa
    · rintro ⟨-, h, -⟩; exact absurd h hsa

end Omega3.M11

end

section

/-!
# M11 helper: the `n`-sum of `E11` as a sum over tuples of primes in `(y^a, y]`

For a prime `p < y^{1/2}` in `Pset y a` with `w(p) ≠ 0`:
`w(p)γ(p)/p Σ_{n} χ̄_y(n)γ(n)/n σ⁺(y/(pn)) = Σ_{k ≤ 42} Σ_{v ∈ Pset^{2k}} Φ(v, p)`.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT
open Classical

/-- The summand on tuples `q = (v, p)`. -/
noncomputable def Phi3 (b n : ℕ) (y : ℝ) (q : Fin (n + 1) → ℕ) : ℝ :=
  (∏ i, gB b (q i)) * (if ExplA n (xq y q) then Wf (xq y q (Fin.last n)) * sigmaP b (y / ((∏ i, q i : ℕ) : ℝ)) else 0)

theorem gB_prime (b p : ℕ) (hp : p.Prime) : gB b p = rhoB b p / p := by
  unfold gB rhoB
  by_cases h : Nat.Coprime p (bigB b)
  · rw [if_pos ⟨hp, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h, zero_div]

theorem rho_div_prod' (b : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) = ∏ p ∈ D, gB b p := by
  unfold rhoB gB
  by_cases h : Nat.Coprime (∏ p ∈ D, p) (bigB b)
  · rw [if_pos h]
    have h' : ∀ p ∈ D, Nat.Coprime p (bigB b) := fun p hp =>
      Nat.Coprime.coprime_dvd_left (dvd_prod_of_mem _ hp) h
    rw [prod_congr rfl (fun p hp => if_pos ⟨hD p hp, h' p hp⟩), Nat.cast_prod, one_div, ← prod_inv_distrib]
    simp [one_div]
  · rw [if_neg h, zero_div]
    rw [Nat.coprime_prod_left_iff] at h
    push Not at h
    obtain ⟨p, hp, hpc⟩ := h
    symm
    apply prod_eq_zero hp
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hpc h2

theorem primesBelow_prime' {w : ℝ} {p : ℕ} (hp : p ∈ primesBelow w) : p.Prime := ((mem_primesBelow w p).1 hp).1

theorem mem_Pset {y a : ℝ} {p : ℕ} : p ∈ Pset y a ↔ p.Prime ∧ ⌊y ^ a⌋₊ < p ∧ p ≤ ⌊y⌋₊ := by
  unfold Pset; rw [mem_filter, mem_Ioc]; tauto

theorem sum_pi_restrict {m : ℕ} (A B : Finset ℕ) (F : (Fin m → ℕ) → ℝ)
    (h : ∀ v ∈ Fintype.piFinset (fun _ : Fin m => A), F v ≠ 0 → ∀ j, v j ∈ B) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => A), F v = ∑ v ∈ Fintype.piFinset (fun _ : Fin m => A ∩ B), F v := by
  symm
  apply Finset.sum_subset
  · intro v hv; rw [Fintype.mem_piFinset] at hv ⊢; intro j; exact (mem_inter.1 (hv j)).1
  · intro v hvA hv
    by_contra hF
    apply hv
    rw [Fintype.mem_piFinset] at hvA ⊢
    intro j; exact mem_inter.2 ⟨hvA j, h v (Fintype.mem_piFinset.2 hvA) hF j⟩

/-- The tuple summand before multiplying by the `p`-factor. -/
noncomputable def Psi (b : ℕ) (y : ℝ) (p m : ℕ) (v : Fin m → ℕ) : ℝ :=
  if StrictAnti v ∧ (∀ j, (v j : ℝ) < y) ∧ ((∏ i, v i) ≠ 1 ∧ Even (ω (∏ i, v i)) ∧ p < (∏ i, v i).minFac ∧
      ((∏ i, v i : ℕ) : ℝ) * ((∏ i, v i).minFac : ℝ) < y / p) then
    chibar y mm (∏ i, v i) * (∏ j, gB b (v j)) * sigmaP b (y / ((p : ℝ) * ((∏ i, v i : ℕ) : ℝ)))
  else 0

/-- Lower bound for the chain primes: `p > y^m`, so every prime of a valid `n` lies in `Pset y a`. -/
theorem big_of_w {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : p.Prime) (hw : mm < Real.log p / Real.log y) :
    y ^ aa < p := by
  have hl := Real.log_pos hy
  have h1 : mm * Real.log y < Real.log p := by rwa [lt_div_iff₀ hl] at hw
  have h2 : Real.log (y ^ aa) < Real.log p := by
    rw [Real.log_rpow (by linarith)]; have := aa_lt_mm; nlinarith
  exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos (by linarith) _) (by exact_mod_cast hp.pos)).1 h2

theorem card_of_cond {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : p.Prime) (hw : mm < Real.log p / Real.log y)
    {U : Finset ℕ} (hU : ∀ q ∈ U, q.Prime)
    (hc : (∏ q ∈ U, q) ≠ 1 ∧ Even (ω (∏ q ∈ U, q)) ∧ p < (∏ q ∈ U, q).minFac ∧
      ((∏ q ∈ U, q : ℕ) : ℝ) * ((∏ q ∈ U, q).minFac : ℝ) < y / p) :
    ∃ k ∈ Icc 1 42, U.card = 2 * k := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [omega_prod hU] at h2
  obtain ⟨r, hr⟩ := h2
  have hne : U.Nonempty := by
    rw [nonempty_iff_ne_empty]; rintro rfl; exact h1 prod_empty
  have hcard : 1 ≤ U.card := hne.card_pos
  have hl := Real.log_pos hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨-, hmin⟩ := minFac_prod hU hne
  have hpq : ∀ q ∈ U, (p : ℝ) ≤ q := fun q hq => by exact_mod_cast (lt_of_lt_of_le h3 (hmin q hq)).le
  have hP : (p : ℝ) ^ U.card ≤ ((∏ q ∈ U, q : ℕ) : ℝ) := by
    rw [Nat.cast_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => hp0.le) hpq
  have hm : (p : ℝ) ≤ ((∏ q ∈ U, q).minFac : ℝ) := by exact_mod_cast h3.le
  have hpow : (p : ℝ) ^ (U.card + 2) < y := by
    rw [lt_div_iff₀ hp0] at h4
    calc (p : ℝ) ^ (U.card + 2) = (p : ℝ) ^ U.card * p * p := by ring
      _ ≤ ((∏ q ∈ U, q : ℕ) : ℝ) * ((∏ q ∈ U, q).minFac : ℝ) * p := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul hP hm hp0.le (by positivity)) hp0.le
      _ < y := h4
  have hlog : ((U.card + 2 : ℕ) : ℝ) * Real.log p < Real.log y := by
    rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) hpow
  have h1' : mm * Real.log y < Real.log p := by rwa [lt_div_iff₀ hl] at hw
  have h85 : ((U.card + 2 : ℕ) : ℝ) * mm < 1 := by
    have hc0 : (0 : ℝ) ≤ ((U.card + 2 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h1'.le hc0
    have h5 : ((U.card + 2 : ℕ) : ℝ) * (mm * Real.log y) < 1 * Real.log y := by linarith
    have h6 : ((U.card + 2 : ℕ) : ℝ) * mm * Real.log y < 1 * Real.log y := by linarith [h5]
    exact lt_of_mul_lt_mul_right h6 hl.le
  have hlt : U.card + 2 < 85 := by
    have : mm = 1 / 85 := rfl
    rw [this] at h85
    have : ((U.card + 2 : ℕ) : ℝ) < 85 := by linarith
    exact_mod_cast this
  refine ⟨r, ?_, by omega⟩
  rw [mem_Icc]; omega

/-- **Pointwise identity** for one prime `p`. -/
theorem inner_eq (b : ℕ) {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : p.Prime) (hpy : (p : ℝ) < y ^ ((1 : ℝ) / 2))
    (hpP : p ∈ Pset y aa) :
    wy y p * rhoB b p / p * ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧
        p < n.minFac ∧ (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) =
      ∑ k ∈ Icc 1 42, ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa), Phi3 b (2 * k) y (Fin.snoc v p) := by
  have hl := Real.log_pos hy
  have hwdef : wy y p = Wf (Real.log p / Real.log y) := rfl
  by_cases hw : Real.log p / Real.log y ≤ mm
  · -- `w(p) = 0`: both sides vanish
    rw [hwdef, Wf_zero_of_le hw, zero_mul, zero_div, zero_mul]
    symm; apply Finset.sum_eq_zero; intro k _; apply Finset.sum_eq_zero; intro v _
    unfold Phi3; rw [xq_snoc_last, Wf_zero_of_le hw]; simp
  push Not at hw
  set S := primesBelow y
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => primesBelow_prime' hq
  -- (a) divisors → subsets
  obtain ⟨cond, hcond⟩ : ∃ cond : ℕ → Prop, cond = fun n => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧ (n : ℝ) * n.minFac < y / p := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, F = fun n => chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Finset ℕ → ℝ, G = fun U => if cond (∏ q ∈ U, q) then F (∏ q ∈ U, q) else 0 := ⟨_, rfl⟩
  have ha : ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧
        p < n.minFac ∧ (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) =
      ∑ U ∈ S.powerset, G U := by
    rw [Finset.sum_filter]; unfold primorialLt; rw [sum_divisors_primes _ hSp]
    apply Finset.sum_congr rfl; intro U _; rw [hG, hcond, hF]; dsimp only; split_ifs <;> rfl
  -- (b) split by cardinality
  have hb : ∑ U ∈ S.powerset, G U = ∑ k ∈ Icc 1 42, ∑ U ∈ S.powersetCard (2 * k), G U := by
    have hpt : ∀ U ∈ S.powerset, G U = ∑ k ∈ Icc 1 42, if U.card = 2 * k then G U else 0 := by
      intro U hU
      have hUp : ∀ q ∈ U, q.Prime := fun q hq => hSp q (mem_powerset.1 hU hq)
      by_cases hc : cond (∏ q ∈ U, q)
      · obtain ⟨k0, hk0, hk0c⟩ := card_of_cond hy hp hw hUp (by rw [hcond] at hc; exact hc)
        rw [Finset.sum_eq_single k0 (fun k _ hk => if_neg (by omega)) (fun h => absurd hk0 h), if_pos hk0c]
      · have : G U = 0 := by rw [hG]; simp only [if_neg hc]
        rw [this]; simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_filter, Finset.powersetCard_eq_filter]
  -- (c) subsets of size `2k` → tuples; (e) `S` → `Pset`
  have hc : ∀ k ∈ Icc 1 42, ∑ U ∈ S.powersetCard (2 * k), G U =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa), Psi b y p (2 * k) v := by
    intro k _
    rw [sum_powersetCard_tuples']
    have h1 : ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => S), (if StrictAnti v then G (Finset.univ.image v) else 0) =
        ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => S), Psi b y p (2 * k) v := by
      apply Finset.sum_congr rfl; intro v hv
      rw [Fintype.mem_piFinset] at hv
      have hvp : ∀ j, (v j).Prime := fun j => hSp _ (hv j)
      have hvy : ∀ j, (v j : ℝ) < y := fun j => ((mem_primesBelow _ _).1 (hv j)).2
      unfold Psi
      by_cases hsa : StrictAnti v
      · rw [if_pos hsa, hG]
        simp only []
        rw [prod_image_sa v hsa]
        by_cases hcv : cond (∏ i, v i)
        · rw [if_pos hcv, if_pos ⟨hsa, hvy, by rw [hcond] at hcv; exact hcv⟩, hF]
          simp only []
          have hr := rho_div_prod' b (primes_image v hvp)
          rw [prod_image_sa v hsa, prod_image (fun a _ b' _ h => hsa.injective h)] at hr
          rw [mul_div_assoc, hr]
          try (push_cast; ring_nf)
        · rw [if_neg hcv, if_neg (fun h => hcv (by rw [hcond]; exact h.2.2))]
      · rw [if_neg hsa, if_neg (fun h => hsa h.1)]
    rw [h1, sum_pi_restrict S (Pset y aa), Finset.inter_comm, ← sum_pi_restrict (Pset y aa) S]
    · -- nonzero `Psi` on `Pset`-tuples has all coordinates in `S`
      intro v hv hne j
      rw [Fintype.mem_piFinset] at hv
      unfold Psi at hne
      split_ifs at hne with h
      · exact (mem_primesBelow _ _).2 ⟨(mem_Pset.1 (hv j)).1, h.2.1 j⟩
      · exact absurd rfl hne
    · intro v hv hne j
      rw [Fintype.mem_piFinset] at hv
      unfold Psi at hne
      split_ifs at hne with h
      · obtain ⟨hsa, hvy, -, -, hpm, -⟩ := h
        have hvp : ∀ j, (v j).Prime := fun j => hSp _ (hv j)
        rcases (2 * k).eq_zero_or_pos with h0 | h0
        · exact absurd j.isLt (by omega)
        obtain ⟨m', hm'⟩ : ∃ m', 2 * k = m' + 1 := ⟨2 * k - 1, by omega⟩
        refine mem_Pset.2 ⟨hvp j, ?_, Nat.le_floor (hvy j).le⟩
        have hbig := big_of_w hy hp hw
        have hvj : p < v j := by
          have := lt_of_lt_of_le hpm (Nat.minFac_le_of_dvd (hvp j).two_le (Finset.dvd_prod_of_mem v (mem_univ j)))
          exact this
        have h1 : (⌊y ^ aa⌋₊ : ℝ) ≤ y ^ aa := Nat.floor_le (by positivity)
        have h2 : (p : ℝ) < v j := by exact_mod_cast hvj
        exact_mod_cast (lt_of_le_of_lt h1 (lt_trans hbig h2))
      · exact absurd rfl hne
  -- assemble
  have hcp : ∀ k ∈ Icc 1 42, ∀ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa),
      wy y p * rhoB b p / p * Psi b y p (2 * k) v = Phi3 b (2 * k) y (Fin.snoc v p) := by
    intro k hk v hv
    rw [mem_Icc] at hk
    rw [Fintype.mem_piFinset] at hv
    have hvp : ∀ j, (v j).Prime := fun j => (mem_Pset.1 (hv j)).1
    obtain ⟨m', hm'⟩ : ∃ m', 2 * k = m' + 1 := ⟨2 * k - 1, by omega⟩
    have key : ∀ (n : ℕ) (hn : n = m' + 1) (v : Fin n → ℕ), (∀ j, (v j).Prime) →
        wy y p * rhoB b p / p * Psi b y p n v = Phi3 b n y (Fin.snoc v p) := by
      intro n hn v hvp
      subst hn
      unfold Psi Phi3
      have hE := explA_snoc (by omega) hy v p hvp hp
      rw [xq_snoc_last, ← hwdef]
      have hprod : (∏ i, gB b ((Fin.snoc v p : Fin (m' + 2) → ℕ) i)) = (∏ j, gB b (v j)) * (rhoB b p / p) := by
        rw [Fin.prod_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [gB_prime b p hp]
      have hprodN : (∏ i, (Fin.snoc v p : Fin (m' + 2) → ℕ) i) = (∏ j, v j) * p := by
        rw [Fin.prod_univ_castSucc]; simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hprod, hprodN]
      by_cases hsa : StrictAnti v
      · have hcb := chibar_tuple (by omega) y v hsa hvp
        have hne1 : (∏ i, v i) ≠ 1 := by
          intro h
          have := Finset.dvd_prod_of_mem v (mem_univ (0 : Fin (m' + 1)))
          rw [h] at this; exact (hvp 0).ne_one (Nat.dvd_one.1 this)
        have hev : Even (ω (∏ i, v i)) := by
          rw [← prod_image_sa v hsa, omega_prod (primes_image v hvp), card_image_of_injective _ hsa.injective,
            card_univ, Fintype.card_fin, ← hm']; exact even_two_mul k
        by_cases hrest : (∀ j, (v j : ℝ) < y) ∧ p < (∏ i, v i).minFac ∧
            ((∏ i, v i : ℕ) : ℝ) * ((∏ i, v i).minFac : ℝ) < y / p
        · rw [if_pos ⟨hsa, hrest.1, hne1, hev, hrest.2.1, hrest.2.2⟩]
          by_cases hc1 : chibar y mm (∏ i, v i) = 1
          · rw [if_pos (hE.2 ⟨hpy, hsa, hrest.1, hrest.2.1, hrest.2.2, hc1⟩), hc1]
            push_cast; ring_nf
          · have hc0 : chibar y mm (∏ i, v i) = 0 := by
              rw [hcb] at hc1 ⊢; split_ifs at hc1 ⊢ with h
              · exact absurd rfl hc1
              · rfl
            rw [if_neg (fun h => hc1 (hE.1 h).2.2.2.2.2), hc0]; ring
        · rw [if_neg (fun h => hrest ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩),
            if_neg (fun h => hrest ⟨(hE.1 h).2.2.1, (hE.1 h).2.2.2.1, (hE.1 h).2.2.2.2.1⟩)]
          ring
      · rw [if_neg (fun h => hsa h.1), if_neg (fun h => hsa (hE.1 h).2.1)]; ring
    exact key (2 * k) hm' v hvp
  rw [ha, hb, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  rw [hc k hk, Finset.mul_sum]
  exact Finset.sum_congr rfl (hcp k hk)

end Omega3.M11

end

section

/-!
# M11 helper: `E11 = W(1)T⁻ − S2 + S3a − S3b`, each piece as a sum over primes / tuples in `Pset y a`
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT
open Classical

noncomputable def tp (y : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log y

theorem wy_eq (y : ℝ) (p : ℕ) : wy y p = Wf (tp y p) := rfl

theorem floor_aa_lt {y : ℝ} (hy : 1 < y) {p : ℕ} (h : y ^ aa < p) : ⌊y ^ aa⌋₊ < p := by
  have h1 : (⌊y ^ aa⌋₊ : ℝ) ≤ y ^ aa := Nat.floor_le (by positivity)
  exact_mod_cast lt_of_le_of_lt h1 h

theorem rpow_aa_lt_half {y : ℝ} (hy : 1 < y) : y ^ aa < y ^ ((1 : ℝ) / 2) :=
  Real.rpow_lt_rpow_of_exponent_lt hy (by unfold aa; norm_num)

theorem rpow_le_self' {y : ℝ} (hy : 1 < y) {c : ℝ} (hc : c ≤ 1) : y ^ c ≤ y := by
  have := Real.rpow_le_rpow_of_exponent_le hy.le hc; simpa using this

theorem tp_le_aa {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : p.Prime) (h : ¬ ⌊y ^ aa⌋₊ < p) : tp y p ≤ aa := by
  have hl := Real.log_pos hy
  push Not at h
  have h1 : (p : ℝ) ≤ y ^ aa := by
    have : (p : ℝ) ≤ (⌊y ^ aa⌋₊ : ℝ) := by exact_mod_cast h
    exact this.trans (Nat.floor_le (by positivity))
  unfold tp
  rw [div_le_iff₀ hl, ← Real.log_rpow (by linarith)]
  exact Real.log_le_log (by exact_mod_cast hp.pos) h1

theorem w_zero_of_small {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : p.Prime) (h : ¬ ⌊y ^ aa⌋₊ < p) : wy y p = 0 := by
  rw [wy_eq]; exact Wf_zero_of_le ((tp_le_aa hy hp h).trans aa_lt_mm.le)

theorem tp_lt_half_iff {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : 0 < p) : tp y p < 1 / 2 ↔ (p : ℝ) < y ^ ((1 : ℝ) / 2) :=
  lt_half_iff_xq hy hp

/-! ## `S3a` -/

theorem S3a_eq (b : ℕ) {y : ℝ} (hy : 1 < y) :
    ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p * sigmaP b (y / p) =
      ∑ p ∈ Pset y aa, gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p)) := by
  have hI : ∀ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)) ∩ Pset y aa,
      wy y p * rhoB b p / p * sigmaP b (y / p) = gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p)) := by
    intro p hp
    rw [mem_inter] at hp
    have hpp := primesBelow_prime' hp.1
    have hlt := ((mem_primesBelow _ _).1 hp.1).2
    rw [if_pos ((tp_lt_half_iff hy hpp.pos).2 hlt), gB_prime b p hpp, wy_eq]; ring
  have e1 : ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p * sigmaP b (y / p) =
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)) ∩ Pset y aa, wy y p * rhoB b p / p * sigmaP b (y / p) := by
    symm
    apply Finset.sum_subset inter_subset_left
    intro p hp hpn
    have hpp := primesBelow_prime' hp
    have hnP : p ∉ Pset y aa := fun h => hpn (mem_inter.2 ⟨hp, h⟩)
    have : ¬ ⌊y ^ aa⌋₊ < p := fun h => hnP (mem_Pset.2 ⟨hpp, h, by
      have h2 := ((mem_primesBelow _ _).1 hp).2
      exact Nat.le_floor (le_trans h2.le (rpow_le_self' hy (by norm_num)))⟩)
    rw [w_zero_of_small hy hpp this]; ring
  have e2 : ∑ p ∈ Pset y aa, gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p)) =
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)) ∩ Pset y aa,
        gB b p * ((if tp y p < 1 / 2 then Wf (tp y p) else 0) * sigmaP b (y / p)) := by
    symm
    apply Finset.sum_subset inter_subset_right
    intro p hp hpn
    have hpp := (mem_Pset.1 hp).1
    have hnB : p ∉ primesBelow (y ^ ((1 : ℝ) / 2)) := fun h => hpn (mem_inter.2 ⟨h, hp⟩)
    have : ¬ tp y p < 1 / 2 := fun h => hnB ((mem_primesBelow _ _).2 ⟨hpp, (tp_lt_half_iff hy hpp.pos).1 h⟩)
    rw [if_neg this]; ring
  rw [e1, e2]
  exact Finset.sum_congr rfl hI

/-! ## `S2` -/

theorem S2_eq (b : ℕ) {y : ℝ} (hy : 1 < y) :
    ∑ p ∈ (primesBelow (y ^ UU + 1)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ^ UU),
        (W1 - wy y p) * rhoB b p / p * sigmaP b (y / p) =
      ∑ p ∈ Pset y aa, gB b p * ((if 1 / 2 ≤ tp y p then W1 - Wf (tp y p) else 0) * sigmaP b (y / p)) := by
  have hl := Real.log_pos hy
  set L := (primesBelow (y ^ UU + 1)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ^ UU)
  have hLP : L ⊆ Pset y aa := by
    intro p hp
    rw [mem_filter] at hp
    have hpp := primesBelow_prime' hp.1
    refine mem_Pset.2 ⟨hpp, floor_aa_lt hy (lt_of_lt_of_le (rpow_aa_lt_half hy) hp.2.1), Nat.le_floor ?_⟩
    exact le_trans hp.2.2 (rpow_le_self' hy (by unfold UU; norm_num))
  rw [← Finset.sum_subset hLP (fun p hp hpn => by
    have hpp := (mem_Pset.1 hp).1
    by_cases h1 : 1 / 2 ≤ tp y p
    · rw [if_pos h1]
      have h2 : ¬ (p : ℝ) ≤ y ^ UU := by
        intro h2; apply hpn; rw [mem_filter]
        refine ⟨(mem_primesBelow _ _).2 ⟨hpp, by linarith⟩, ?_, h2⟩
        by_contra h3; push Not at h3; exact (not_lt.2 h1) ((tp_lt_half_iff hy hpp.pos).2 h3)
      push Not at h2
      have hU : UU ≤ tp y p := by
        unfold tp; rw [le_div_iff₀ hl, ← Real.log_rpow (by linarith)]
        exact Real.log_le_log (by positivity) h2.le
      rw [Wf_W1_of_ge hU]; ring
    · rw [if_neg h1]; ring)]
  apply Finset.sum_congr rfl; intro p hp
  rw [mem_filter] at hp
  have hpp := primesBelow_prime' hp.1
  have h1 : 1 / 2 ≤ tp y p := by
    by_contra h; push Not at h; exact (not_lt.2 hp.2.1) ((tp_lt_half_iff hy hpp.pos).1 h)
  rw [if_pos h1, gB_prime b p hpp, wy_eq]; ring

/-! ## `S3b` -/

theorem S3b_eq (b : ℕ) {y : ℝ} (hy : 1 < y) :
    ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p *
        ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧
            (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) =
      ∑ k ∈ Icc 1 42, ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q := by
  have hR : ∀ k ∈ Icc 1 42, ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * k + 1) => Pset y aa), Phi3 b (2 * k) y q =
      ∑ p ∈ Pset y aa, ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa), Phi3 b (2 * k) y (Fin.snoc v p) :=
    fun k _ => sum_piFinset_snoc _ _
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  have hzero : ∀ p ∈ Pset y aa, ¬ (p : ℝ) < y ^ ((1 : ℝ) / 2) →
      ∑ k ∈ Icc 1 42, ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa), Phi3 b (2 * k) y (Fin.snoc v p) = 0 := by
    intro p hp hnot
    apply Finset.sum_eq_zero; intro k _; apply Finset.sum_eq_zero; intro v _
    unfold Phi3
    rw [if_neg, mul_zero]
    intro h
    have := h.1
    rw [xq_snoc_last] at this
    exact hnot ((lt_half_iff_xq hy (mem_Pset.1 hp).1.pos).1 this)
  have e1 : ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p *
        ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧
            (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) =
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)) ∩ Pset y aa, wy y p * rhoB b p / p *
        ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧
            (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) := by
    symm
    apply Finset.sum_subset inter_subset_left
    intro p hp hpn
    have hpp := primesBelow_prime' hp
    have hnP : p ∉ Pset y aa := fun h => hpn (mem_inter.2 ⟨hp, h⟩)
    have : ¬ ⌊y ^ aa⌋₊ < p := fun h => hnP (mem_Pset.2 ⟨hpp, h, by
      have h2 := ((mem_primesBelow _ _).1 hp).2
      exact Nat.le_floor (le_trans h2.le (rpow_le_self' hy (by norm_num)))⟩)
    rw [w_zero_of_small hy hpp this]; ring
  have e2 : ∑ p ∈ Pset y aa, ∑ k ∈ Icc 1 42, ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa),
        Phi3 b (2 * k) y (Fin.snoc v p) =
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)) ∩ Pset y aa, ∑ k ∈ Icc 1 42,
        ∑ v ∈ Fintype.piFinset (fun _ : Fin (2 * k) => Pset y aa), Phi3 b (2 * k) y (Fin.snoc v p) := by
    symm
    apply Finset.sum_subset inter_subset_right
    intro p hp hpn
    have hpp := (mem_Pset.1 hp).1
    apply hzero p hp
    intro h; exact hpn (mem_inter.2 ⟨(mem_primesBelow _ _).2 ⟨hpp, h⟩, hp⟩)
  rw [e1, e2]
  apply Finset.sum_congr rfl; intro p hp
  rw [mem_inter] at hp
  exact inner_eq b hy (primesBelow_prime' hp.1) ((mem_primesBelow _ _).1 hp.1).2 hp.2

/-! ## `E11` -/

theorem E11_split' (b : ℕ) (y : ℝ) :
    E11 b y = W1 * Tpm b false y (y ^ ((1 : ℝ) / 2)) -
      ∑ p ∈ (primesBelow (y ^ UU + 1)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ^ UU),
        (W1 - wy y p) * rhoB b p / p * sigmaP b (y / p) +
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p * sigmaP b (y / p) -
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * rhoB b p / p *
        ∑ n ∈ (primorialLt y).divisors.filter (fun n : ℕ => n ≠ 1 ∧ Even (ω n) ∧ p < n.minFac ∧
            (n : ℝ) * n.minFac < y / p), chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) := by
  unfold E11
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro p _; ring

end Omega3.M11

end

section

/-!
# M11 helper: `σ⁺(Y)/V(y) = 2e^γ log y/log Y + o(1)` uniformly for `y^c ≤ Y ≤ y`

From Lemma 7 at `s = 3` and Palprimes' `VB_ratio` (Mertens).
-/

set_option linter.style.longLine false

open Finset Real Filter

namespace Omega3.M11

open Palprimes Palprimes.Greaves Palprimes.MT

theorem sigma_approx (b : ℕ) (hb : 2 ≤ b) (h7 : Lemma7Stmt b) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, ∀ Y : ℝ, y ^ c ≤ Y → Y ≤ y →
      |sigmaP b Y / VB b y - 2 * Real.exp Real.eulerMascheroniConstant * (Real.log y / Real.log Y)| ≤ ε := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set δ := ε / (2 * (E + 2 / c + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε₁ := ε / (2 * (2 / c + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨y7, hy7⟩ := h7 ε₁ hε₁0
  obtain ⟨y1, hy1, hratio⟩ := VB_ratio b hb (c / 2) (by positivity) (by linarith) (min δ 1) (by positivity)
  filter_upwards [eventually_ge_atTop y1, eventually_ge_atTop (2 : ℝ), ev_rpow_ge c hc y7] with y hyy1 hy2 hyc
  intro Y hYc hYy
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hy0 _) hYc
  have hY7 : y7 ≤ Y := le_trans hyc hYc
  have h7Y := hy7 Y hY7 3 (by norm_num) (by norm_num)
  have hsig : sigmaP b Y = Tpm b true Y (Y ^ ((1 : ℝ) / 3)) := rfl
  -- `w = √Y` is in `[y^{c/2}, y]`
  set w := Real.sqrt Y with hw
  have hw1 : y ^ (c / 2) ≤ w := by
    rw [hw, show c / 2 = c * (1 / 2) by ring, Real.rpow_mul hy0.le, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hYc
  have hw2 : w ≤ y := by
    calc w ≤ Real.sqrt y := Real.sqrt_le_sqrt hYy
      _ ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = y := Real.sqrt_sq hy0.le
  have hR := hratio y hyy1 w hw1 hw2
  have hlw : Real.log w = Real.log Y / 2 := Real.log_sqrt hYpos.le
  have hlYc : c * Real.log y ≤ Real.log Y := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hy0 _) hYc
    rwa [Real.log_rpow hy0] at this
  have hlY : 0 < Real.log Y := lt_of_lt_of_le (mul_pos hc hly) hlYc
  have hratio2 : Real.log y / Real.log w = 2 * (Real.log y / Real.log Y) := by
    rw [hlw]; field_simp
  rw [hratio2] at hR
  have hq : Real.log y / Real.log Y ≤ 1 / c := by
    rw [div_le_div_iff₀ hlY hc]; linarith
  have hq0 : 0 ≤ Real.log y / Real.log Y := by positivity
  have hVy := VB_pos b y
  have hVw := VB_pos b w
  -- `V(w)/V(y) ≤ 2/c + 1`
  have hVr : VB b w / VB b y ≤ 2 / c + 1 := by
    have := (abs_le.1 hR).2
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    have h2 : 2 * (Real.log y / Real.log Y) ≤ 2 / c := by
      have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2); rwa [mul_one_div] at this
    linarith
  -- split
  have key : sigmaP b Y / VB b y - 2 * E * (Real.log y / Real.log Y) =
      (Tpm b true Y (Y ^ ((1 : ℝ) / 3)) - E * VB b w) / VB b y +
        E * (VB b w / VB b y - 2 * (Real.log y / Real.log Y)) := by
    rw [hsig]; field_simp; ring
  rw [key]
  have hA : |(Tpm b true Y (Y ^ ((1 : ℝ) / 3)) - E * VB b w) / VB b y| ≤ ε₁ * (2 / c + 1) := by
    rw [abs_div, abs_of_pos hVy, div_le_iff₀ hVy]
    have : ε₁ * VB b w ≤ ε₁ * ((2 / c + 1) * VB b y) := by
      apply mul_le_mul_of_nonneg_left _ hε₁0.le
      rw [div_le_iff₀ hVy] at hVr; exact hVr
    have h7' : |Tpm b true Y (Y ^ ((1 : ℝ) / 3)) - E * VB b w| ≤ ε₁ * VB b w := by
      rw [hw]; simpa [one_div] using h7Y
    nlinarith
  have hB : |E * (VB b w / VB b y - 2 * (Real.log y / Real.log Y))| ≤ E * δ := by
    rw [abs_mul, abs_of_pos hE0]
    exact mul_le_mul_of_nonneg_left (le_trans hR (min_le_left _ _)) hE0.le
  have hsum : ε₁ * (2 / c + 1) + E * δ ≤ ε := by
    have e1 : ε₁ * (2 / c + 1) = ε / 2 := by rw [hε₁]; field_simp
    have e2 : E * δ ≤ ε / 2 := by
      rw [hδ, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 < 2 / c := by positivity
      nlinarith
    linarith
  calc _ ≤ |(Tpm b true Y (Y ^ ((1 : ℝ) / 3)) - E * VB b w) / VB b y| +
        |E * (VB b w / VB b y - 2 * (Real.log y / Real.log Y))| := abs_add_le _ _
    _ ≤ ε := by linarith

end Omega3.M11

end
