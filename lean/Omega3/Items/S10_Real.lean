import Omega3.Statements
import Omega3.Items.S10_Mono

/-!
# S10 helpers, part 1: step functions, cell decomposition of the integrals in `gEta`, `cEta`
-/

set_option linter.style.longLine false

open Real MeasureTheory intervalIntegral Set

namespace Omega3
namespace S10

/-- One step of `StepFn.eval`. -/
noncomputable def stp (u : ℝ) (acc : ℝ) (pr : ℚ × ℚ) : ℝ := if (pr.1 : ℝ) ≤ u then (pr.2 : ℝ) else acc

lemma eval_eq (s : StepFn) (u : ℝ) : s.eval u = s.foldl (stp u) 0 := rfl

lemma foldl_stp_const (u : ℝ) : ∀ (l : List (ℚ × ℚ)) (acc : ℝ), (∀ p ∈ l, u < (p.1 : ℝ)) →
    l.foldl (stp u) acc = acc
  | [], _, _ => rfl
  | p :: rest, acc, h => by
    simp only [List.foldl_cons]
    have h1 : stp u acc p = acc := by
      simp only [stp]; rw [if_neg (not_le.mpr (h p (by simp)))]
    rw [h1]; exact foldl_stp_const u rest acc (fun q hq => h q (by simp [hq]))

/-- Sortedness of the left ends. -/
def Sorted (l : List (ℚ × ℚ)) : Prop := l.Pairwise (fun p q => p.1 < q.1)

/-- The cell sum: `Ψ(acc)∫_c^{min a s} F + …`. -/
noncomputable def cellInt (Ψ F : ℝ → ℝ) (s : ℝ) : ℝ → ℝ → List (ℚ × ℚ) → ℝ
  | acc, c, [] => Ψ acc * ∫ u in c..s, F u
  | acc, c, pr :: rest => Ψ acc * (∫ u in c..min (pr.1 : ℝ) s, F u) + cellInt Ψ F s (pr.2 : ℝ) (min (pr.1 : ℝ) s) rest

theorem cellInt_spec (Ψ F : ℝ → ℝ) (s : ℝ) : ∀ (l : List (ℚ × ℚ)) (acc c : ℝ), Sorted l →
    (∀ p ∈ l, c < (p.1 : ℝ)) → c ≤ s → IntervalIntegrable F volume c s →
    IntervalIntegrable (fun u => Ψ (l.foldl (stp u) acc) * F u) volume c s ∧
      ∫ u in c..s, Ψ (l.foldl (stp u) acc) * F u = cellInt Ψ F s acc c l
  | [], acc, c, _, _, _, hF => by
    simp only [List.foldl_nil, cellInt]
    exact ⟨hF.const_mul _, intervalIntegral.integral_const_mul _ _⟩
  | pr :: rest, acc, c, hs, hc, hcs, hF => by
    have hs' : Sorted rest := (List.pairwise_cons.mp hs).2
    have hlt : ∀ q ∈ rest, (pr.1 : ℝ) < (q.1 : ℝ) := fun q hq => by
      exact_mod_cast (List.pairwise_cons.mp hs).1 q hq
    set a : ℝ := (pr.1 : ℝ)
    set d : ℝ := min a s
    have hca : c < a := hc pr (by simp)
    have hcd : c ≤ d := le_min hca.le hcs
    have hds : d ≤ s := min_le_right _ _
    have hF1 : IntervalIntegrable F volume c d := hF.mono_set (by
      rw [uIcc_of_le hcd, uIcc_of_le hcs]; exact Icc_subset_Icc le_rfl hds)
    have hF2 : IntervalIntegrable F volume d s := hF.mono_set (by
      rw [uIcc_of_le hds, uIcc_of_le hcs]; exact Icc_subset_Icc hcd le_rfl)
    obtain ⟨ih1, ih2⟩ := cellInt_spec Ψ F s rest (pr.2 : ℝ) d hs'
      (fun q hq => lt_of_le_of_lt (min_le_left _ _) (hlt q hq)) hds hF2
    -- first piece
    have e1 : EqOn (fun u => Ψ ((pr :: rest).foldl (stp u) acc) * F u) (fun u => Ψ acc * F u) (Ioo c d) := by
      intro u hu
      have hua : u < a := lt_of_lt_of_le hu.2 (min_le_left _ _)
      simp only [List.foldl_cons]
      have : stp u acc pr = acc := by simp only [stp]; rw [if_neg (not_le.mpr hua)]
      rw [this, foldl_stp_const u rest acc (fun q hq => lt_trans hua (hlt q hq))]
    have e2 : EqOn (fun u => Ψ ((pr :: rest).foldl (stp u) acc) * F u)
        (fun u => Ψ (rest.foldl (stp u) (pr.2 : ℝ)) * F u) (Ioo d s) := by
      intro u hu
      have hau : a ≤ u := by
        have : d < s := lt_trans hu.1 hu.2
        have hd : d = a := by
          rcases min_choice a s with h | h
          · exact h
          · exfalso; simp only [d] at this; rw [h] at this; exact lt_irrefl _ this
        rw [← hd]; exact hu.1.le
      simp only [List.foldl_cons]
      have : stp u acc pr = (pr.2 : ℝ) := by simp only [stp]; rw [if_pos hau]
      rw [this]
    have i1 : IntervalIntegrable (fun u => Ψ ((pr :: rest).foldl (stp u) acc) * F u) volume c d :=
      (hF1.const_mul (Ψ acc)).congr_uIoo (by rw [uIoo_of_le hcd]; exact fun u hu => (e1 hu).symm)
    have i2 : IntervalIntegrable (fun u => Ψ ((pr :: rest).foldl (stp u) acc) * F u) volume d s :=
      ih1.congr_uIoo (by rw [uIoo_of_le hds]; exact fun u hu => (e2 hu).symm)
    refine ⟨i1.trans i2, ?_⟩
    rw [← integral_add_adjacent_intervals i1 i2, integral_congr_Ioo_of_le hcd e1,
      integral_congr_Ioo_of_le hds e2, ih2, intervalIntegral.integral_const_mul]
    rfl

/-- Top level: `∫_0^s Ψ(η̂(u)) F(u) du` for `η̂ = (a₀, v₀) :: rest`, `Ψ 0 = 0`. -/
theorem integral_eval (Ψ F : ℝ → ℝ) (hΨ : Ψ 0 = 0) (s : ℝ) (hs0 : 0 ≤ s) (pr : ℚ × ℚ) (rest : List (ℚ × ℚ))
    (hsort : Sorted (pr :: rest)) (ha0 : 0 < (pr.1 : ℝ))
    (hF : IntervalIntegrable F volume (min (pr.1 : ℝ) s) s) :
    IntervalIntegrable (fun u => Ψ (StepFn.eval (pr :: rest) u) * F u) volume 0 s ∧
    ∫ u in (0 : ℝ)..s, Ψ (StepFn.eval (pr :: rest) u) * F u = cellInt Ψ F s (pr.2 : ℝ) (min (pr.1 : ℝ) s) rest := by
  have hs' : Sorted rest := (List.pairwise_cons.mp hsort).2
  have hlt : ∀ q ∈ rest, (pr.1 : ℝ) < (q.1 : ℝ) := fun q hq => by
    exact_mod_cast (List.pairwise_cons.mp hsort).1 q hq
  set a : ℝ := (pr.1 : ℝ)
  set d : ℝ := min a s
  have h0d : 0 ≤ d := le_min ha0.le hs0
  have hds : d ≤ s := min_le_right _ _
  obtain ⟨ih1, ih2⟩ := cellInt_spec Ψ F s rest (pr.2 : ℝ) d hs'
      (fun q hq => lt_of_le_of_lt (min_le_left _ _) (hlt q hq)) hds hF
  have e1 : EqOn (fun u => Ψ (StepFn.eval (pr :: rest) u) * F u) (fun _ => (0 : ℝ)) (Ioo 0 d) := by
    intro u hu
    have hua : u < a := lt_of_lt_of_le hu.2 (min_le_left _ _)
    simp only [eval_eq, List.foldl_cons]
    have : stp u 0 pr = 0 := by simp only [stp]; rw [if_neg (not_le.mpr hua)]
    rw [this, foldl_stp_const u rest 0 (fun q hq => lt_trans hua (hlt q hq)), hΨ, zero_mul]
  have e2 : EqOn (fun u => Ψ (StepFn.eval (pr :: rest) u) * F u)
      (fun u => Ψ (rest.foldl (stp u) (pr.2 : ℝ)) * F u) (Ioo d s) := by
    intro u hu
    have hau : a ≤ u := by
      have : d < s := lt_trans hu.1 hu.2
      have hd : d = a := by
        rcases min_choice a s with h | h
        · exact h
        · exfalso; simp only [d] at this; rw [h] at this; exact lt_irrefl _ this
      rw [← hd]; exact hu.1.le
    simp only [eval_eq, List.foldl_cons]
    have : stp u 0 pr = (pr.2 : ℝ) := by simp only [stp]; rw [if_pos hau]
    rw [this]
  have i1 : IntervalIntegrable (fun u => Ψ (StepFn.eval (pr :: rest) u) * F u) volume 0 d :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo (by rw [uIoo_of_le h0d]; exact fun u hu => (e1 hu).symm)
  have i2 : IntervalIntegrable (fun u => Ψ (StepFn.eval (pr :: rest) u) * F u) volume d s :=
    ih1.congr_uIoo (by rw [uIoo_of_le hds]; exact fun u hu => (e2 hu).symm)
  refine ⟨i1.trans i2, ?_⟩
  rw [← integral_add_adjacent_intervals i1 i2, integral_congr_Ioo_of_le h0d e1,
    integral_congr_Ioo_of_le hds e2, ih2]
  simp


/-! ## Cells -/

/-- Cells `(a, b, v)` of a step function `(a, v) :: rest` (the last cell ends at `1`). -/
def cellsAux : ℚ → ℚ → List (ℚ × ℚ) → List (ℚ × ℚ × ℚ)
  | a, v, [] => [(a, 1, v)]
  | a, v, q :: rest => (a, q.1, v) :: cellsAux q.1 q.2 rest

theorem cellInt_eq_sum (Ψ F : ℝ → ℝ) (s : ℝ) (hs1 : s ≤ 1) : ∀ (rest : List (ℚ × ℚ)) (a v : ℚ),
    cellInt Ψ F s (v : ℝ) (min (a : ℝ) s) rest =
      ((cellsAux a v rest).map (fun c => Ψ (c.2.2 : ℝ) * ∫ u in min (c.1 : ℝ) s..min (c.2.1 : ℝ) s, F u)).sum
  | [], a, v => by
    simp only [cellInt, cellsAux, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Rat.cast_one, min_eq_right hs1]
  | q :: rest, a, v => by
    simp only [cellInt, cellsAux, List.map_cons, List.sum_cons]
    rw [cellInt_eq_sum Ψ F s hs1 rest q.1 q.2]

lemma ii_list_sum {ι : Type*} (L : List ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ c ∈ L, IntervalIntegrable (f c) volume a b) :
    IntervalIntegrable (fun u => (L.map (fun c => f c u)).sum) volume a b := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h c (by simp)).add (ih (fun c' hc' => h c' (by simp [hc'])))

lemma integral_list_sum {ι : Type*} (L : List ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (h : ∀ c ∈ L, IntervalIntegrable (f c) volume a b) :
    ∫ u in a..b, (L.map (fun c => f c u)).sum = (L.map (fun c => ∫ u in a..b, f c u)).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [intervalIntegral.integral_add (h c (by simp)) (ii_list_sum L f a b (fun c' hc' => h c' (by simp [hc'])))]
    rw [ih (fun c' hc' => h c' (by simp [hc']))]

/-! ## Closed forms -/

theorem integral_s_sub_div (s p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ∫ v in p..q, (s - v) / v = s * (Real.log q - Real.log p) - (q - p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have e : EqOn (fun v => (s - v) / v) (fun v => s * v⁻¹ - 1) (uIcc p q) := by
    intro v hv
    rw [uIcc_of_le hpq] at hv
    have : v ≠ 0 := (lt_of_lt_of_le hp hv.1).ne'
    simp only; field_simp
  rw [integral_congr e, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_inv_of_pos hp hq,
    Real.log_div hq.ne' hp.ne']
  · simp
  · exact (intervalIntegral.intervalIntegrable_inv (fun x hx => by
      rw [uIcc_of_le hpq] at hx; exact (lt_of_lt_of_le hp hx.1).ne') continuousOn_id).const_mul s
  · exact intervalIntegrable_const

lemma contOn_s_sub_div (s p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) :
    ContinuousOn (fun v => (s - v) / v) (uIcc p q) := by
  apply ContinuousOn.div (continuousOn_const.sub continuousOn_id) continuousOn_id
  intro v hv
  rw [uIcc_of_le hpq] at hv; exact (lt_of_lt_of_le hp hv.1).ne'


/-- Cell properties: `0 < a < b ≤ 1`. -/
theorem cells_props : ∀ (rest : List (ℚ × ℚ)) (a v : ℚ), Sorted ((a, v) :: rest) → 0 < a →
    (∀ p ∈ (a, v) :: rest, p.1 < 1) → ∀ c ∈ cellsAux a v rest, 0 < c.1 ∧ c.1 < c.2.1 ∧ c.2.1 ≤ 1
  | [], a, v, _, ha, h1, c, hc => by
    simp only [cellsAux, List.mem_singleton] at hc
    subst hc; exact ⟨ha, h1 (a, v) (by simp), le_rfl⟩
  | q :: rest, a, v, hs, ha, h1, c, hc => by
    have hq : a < q.1 := (List.pairwise_cons.mp hs).1 q (by simp)
    simp only [cellsAux, List.mem_cons] at hc
    rcases hc with hc | hc
    · subst hc; exact ⟨ha, hq, (h1 q (by simp)).le⟩
    · have hs2 : Sorted ((q.1, q.2) :: rest) := (List.pairwise_cons.mp hs).2
      exact cells_props rest q.1 q.2 hs2 (lt_trans ha hq) (fun p hp => by
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rw [hp]; exact h1 q (by simp)
        · exact h1 p (by simp [hp])) c hc

/-- The cells of the step function `(a, v) :: rest` as reals. -/
noncomputable def cellsR (a v : ℚ) (rest : List (ℚ × ℚ)) : List (ℝ × ℝ × ℝ) :=
  (cellsAux a v rest).map (fun c => ((c.1 : ℝ), (c.2.1 : ℝ), (c.2.2 : ℝ)))

/-- Hypotheses on a step function used below. -/
structure Good (a v : ℚ) (rest : List (ℚ × ℚ)) : Prop where
  sorted : Sorted ((a, v) :: rest)
  pos : 0 < a
  lt1 : ∀ p ∈ (a, v) :: rest, p.1 < 1

lemma Good.cells {a v : ℚ} {rest : List (ℚ × ℚ)} (h : Good a v rest) :
    ∀ c ∈ cellsR a v rest, 0 < c.1 ∧ c.1 < c.2.1 ∧ c.2.1 ≤ 1 := by
  intro c hc
  simp only [cellsR, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨h1, h2, h3⟩ := cells_props rest a v h.sorted h.pos h.lt1 c' hc'
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) < (c'.1 : ℝ); exact_mod_cast h1
  · show (c'.1 : ℝ) < (c'.2.1 : ℝ); exact_mod_cast h2
  · show (c'.2.1 : ℝ) ≤ 1; exact_mod_cast h3

theorem Ahat_eq {a v : ℚ} {rest : List (ℚ × ℚ)} (h : Good a v rest) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Ahat ((a, v) :: rest) s = ((cellsR a v rest).map (fun c => c.2.2 * phiC c.1 c.2.1 s)).sum := by
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast h.pos
  have hmin : 0 < min (a : ℝ) s := lt_min ha hs0
  have hF : IntervalIntegrable (fun v => (s - v) / v) volume (min ((a, v).1 : ℝ) s) s :=
    (contOn_s_sub_div s _ s hmin (min_le_right _ _)).intervalIntegrable
  obtain ⟨_, h2⟩ := integral_eval id (fun v => (s - v) / v) rfl s hs0.le (a, v) rest h.sorted ha hF
  unfold Ahat
  have e : (fun x => StepFn.eval ((a, v) :: rest) x * (s - x) / x) =
      (fun x => id (StepFn.eval ((a, v) :: rest) x) * ((s - x) / x)) := by
    funext x; simp [mul_div_assoc]
  rw [e, h2, cellInt_eq_sum id _ s hs1 rest a v, cellsR, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  obtain ⟨h1, h2, _⟩ := cells_props rest a v h.sorted h.pos h.lt1 c hc
  have h1' : (0 : ℝ) < c.1 := by exact_mod_cast h1
  have h2' : (c.1 : ℝ) ≤ c.2.1 := by exact_mod_cast h2.le
  simp only [Function.comp, id]
  rw [integral_s_sub_div s _ _ (lt_min h1' hs0) (min_le_min_right _ h2')]
  rfl

theorem I1_eq {a v : ℚ} {rest : List (ℚ × ℚ)} (h : Good a v rest) :
    ∫ u in (0 : ℝ)..1, StepFn.eval ((a, v) :: rest) u ^ 2 * (1 - u) / u =
      ((cellsR a v rest).map (fun c => c.2.2 ^ 2 * phiC c.1 c.2.1 1)).sum := by
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast h.pos
  have hmin : 0 < min (a : ℝ) 1 := lt_min ha one_pos
  have hF : IntervalIntegrable (fun v => (1 - v) / v) volume (min ((a, v).1 : ℝ) 1) 1 :=
    (contOn_s_sub_div 1 _ 1 hmin (min_le_right _ _)).intervalIntegrable
  obtain ⟨_, h2⟩ := integral_eval (fun x => x ^ 2) (fun v => (1 - v) / v) (by simp) 1 zero_le_one (a, v) rest
    h.sorted ha hF
  have e : (fun x => StepFn.eval ((a, v) :: rest) x ^ 2 * (1 - x) / x) =
      (fun x => (StepFn.eval ((a, v) :: rest) x) ^ 2 * ((1 - x) / x)) := by
    funext x; simp [mul_div_assoc]
  rw [e, h2, cellInt_eq_sum _ _ 1 le_rfl rest a v, cellsR, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  obtain ⟨h1, h2, _⟩ := cells_props rest a v h.sorted h.pos h.lt1 c hc
  have h1' : (0 : ℝ) < c.1 := by exact_mod_cast h1
  have h2' : (c.1 : ℝ) ≤ c.2.1 := by exact_mod_cast h2.le
  simp only [Function.comp]
  rw [integral_s_sub_div 1 _ _ (lt_min h1' one_pos) (min_le_min_right _ h2')]
  rfl


/-! ## The double integral of `cEta` -/

/-- The kernel `min(1, r(u₁) r(u₂))`. -/
noncomputable def kk (u₁ u₂ : ℝ) : ℝ := min 1 ((1 - u₁) / u₁ * ((1 - u₂) / u₂))

lemma kk_contOn (u₁ p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) : ContinuousOn (kk u₁) (uIcc p q) := by
  unfold kk
  apply ContinuousOn.inf' continuousOn_const
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.div (continuousOn_const.sub continuousOn_id) continuousOn_id
  intro v hv; rw [uIcc_of_le hpq] at hv; exact (lt_of_lt_of_le hp hv.1).ne'

lemma r_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : (1 - y) / y ≤ (1 - x) / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]; nlinarith

lemma r_nonneg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 0 ≤ (1 - x) / x := div_nonneg (by linarith) hx.le

lemma kk_anti1 {x y w : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hw : 0 < w) (hw1 : w ≤ 1) : kk y w ≤ kk x w := by
  unfold kk
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right (r_anti hx hxy) (r_nonneg hw hw1))

lemma kk_anti2 {x y w : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hw : 0 < w) (hw1 : w ≤ 1) : kk w y ≤ kk w x := by
  unfold kk
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_left (r_anti hx hxy) (r_nonneg hw hw1))

/-- `Φ_c(u₁) = ∫_{a}^{b} k(u₁, u₂) du₂`. -/
noncomputable def PhiK (a b u₁ : ℝ) : ℝ := ∫ u₂ in a..b, kk u₁ u₂

lemma PhiK_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) : AntitoneOn (PhiK a b) (Ioi 0) := by
  intro x hx y hy hxy
  unfold PhiK
  apply integral_mono_on hab ((kk_contOn y a b ha hab).intervalIntegrable)
    ((kk_contOn x a b ha hab).intervalIntegrable)
  intro w hw
  exact kk_anti1 hx hxy (lt_of_lt_of_le ha hw.1) (le_trans hw.2 hb)

lemma PhiK_ii {a b p q : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (PhiK a b) volume p q := by
  apply AntitoneOn.intervalIntegrable
  apply (PhiK_anti ha hab hb).mono
  intro x hx; rw [uIcc_of_le hpq] at hx; exact lt_of_lt_of_le hp hx.1

theorem I2_eq {a v : ℚ} {rest : List (ℚ × ℚ)} (h : Good a v rest) :
    (∫ u₁ in (0 : ℝ)..1, ∫ u₂ in (0 : ℝ)..1, StepFn.eval ((a, v) :: rest) u₁ * StepFn.eval ((a, v) :: rest) u₂ *
        min 1 ((1 - u₁) / u₁ * ((1 - u₂) / u₂))) =
      ((cellsR a v rest).map (fun c' => c'.2.2 *
        ((cellsR a v rest).map (fun c => c.2.2 * ∫ u in c'.1..c'.2.1, PhiK c.1 c.2.1 u)).sum)).sum := by
  set e : StepFn := (a, v) :: rest
  have ha : (0 : ℝ) < (a : ℝ) := by exact_mod_cast h.pos
  have hmin : min (a : ℝ) 1 = a := min_eq_left (by exact_mod_cast (h.lt1 (a, v) (by simp)).le)
  have hcell := h.cells
  set Ψ : ℝ → ℝ := fun u₁ => ((cellsR a v rest).map (fun c => c.2.2 * PhiK c.1 c.2.1 u₁)).sum
  -- inner integral
  have inner : ∀ u₁ : ℝ, (∫ u₂ in (0 : ℝ)..1, e.eval u₁ * e.eval u₂ * min 1 ((1 - u₁) / u₁ * ((1 - u₂) / u₂))) =
      e.eval u₁ * Ψ u₁ := by
    intro u₁
    have hF : IntervalIntegrable (kk u₁) volume (min ((a, v).1 : ℝ) 1) 1 := by
      show IntervalIntegrable (kk u₁) volume (min (a : ℝ) 1) 1
      rw [hmin]; exact (kk_contOn u₁ a 1 ha (by exact_mod_cast (h.lt1 (a, v) (by simp)).le)).intervalIntegrable
    obtain ⟨_, h2⟩ := integral_eval id (kk u₁) rfl 1 zero_le_one (a, v) rest h.sorted ha hF
    have e1 : (fun u₂ => e.eval u₁ * e.eval u₂ * min 1 ((1 - u₁) / u₁ * ((1 - u₂) / u₂))) =
        (fun u₂ => e.eval u₁ * (id (e.eval u₂) * kk u₁ u₂)) := by
      funext u₂; simp only [id, kk]; ring
    rw [e1, intervalIntegral.integral_const_mul, h2, cellInt_eq_sum id _ 1 le_rfl rest a v]
    congr 1
    simp only [Ψ, cellsR, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    obtain ⟨h1, h2, h3⟩ := cells_props rest a v h.sorted h.pos h.lt1 c hc
    have h2' : (c.1 : ℝ) < 1 := by exact_mod_cast lt_of_lt_of_le h2 h3
    have h3' : (c.2.1 : ℝ) ≤ 1 := by exact_mod_cast h3
    simp only [Function.comp, id, PhiK, min_eq_left h2'.le, min_eq_left h3']
  simp_rw [inner]
  -- outer integral
  have hΨ : ∀ p q : ℝ, 0 < p → p ≤ q → IntervalIntegrable Ψ volume p q := by
    intro p q hp hpq
    apply ii_list_sum
    intro c hc
    obtain ⟨h1, h2, h3⟩ := hcell c hc
    exact (PhiK_ii h1 h2.le h3 hp hpq).const_mul _
  have hF : IntervalIntegrable Ψ volume (min ((a, v).1 : ℝ) 1) 1 := by
    show IntervalIntegrable Ψ volume (min (a : ℝ) 1) 1
    rw [hmin]; exact hΨ a 1 ha (by exact_mod_cast (h.lt1 (a, v) (by simp)).le)
  obtain ⟨_, h2⟩ := integral_eval id Ψ rfl 1 zero_le_one (a, v) rest h.sorted ha hF
  have e2 : (fun u₁ => e.eval u₁ * Ψ u₁) = (fun u₁ => id (e.eval u₁) * Ψ u₁) := rfl
  rw [e2, h2, cellInt_eq_sum id _ 1 le_rfl rest a v]
  simp only [cellsR, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c' hc'
  obtain ⟨h1, h2, h3⟩ := cells_props rest a v h.sorted h.pos h.lt1 c' hc'
  have h1' : (0 : ℝ) < c'.1 := by exact_mod_cast h1
  have h2' : (c'.1 : ℝ) < 1 := by exact_mod_cast lt_of_lt_of_le h2 h3
  have h12 : (c'.1 : ℝ) ≤ c'.2.1 := by exact_mod_cast h2.le
  have h3' : (c'.2.1 : ℝ) ≤ 1 := by exact_mod_cast h3
  simp only [Function.comp, id, min_eq_left h2'.le, min_eq_left h3']
  congr 1
  simp only [Ψ, cellsR, List.map_map]
  rw [integral_list_sum]
  · congr 1
    apply List.map_congr_left
    intro c _
    simp only [Function.comp]
    rw [intervalIntegral.integral_const_mul]
  · intro c hc
    obtain ⟨k1, k2, k3⟩ := cells_props rest a v h.sorted h.pos h.lt1 c hc
    have k1' : (0 : ℝ) < c.1 := by exact_mod_cast k1
    have k2' : (c.1 : ℝ) ≤ c.2.1 := by exact_mod_cast k2.le
    have k3' : (c.2.1 : ℝ) ≤ 1 := by exact_mod_cast k3
    exact (PhiK_ii k1' k2' k3' h1' h12).const_mul _

theorem cEta_eq {a v : ℚ} {rest : List (ℚ × ℚ)} (h : Good a v rest) :
    cEta ((a, v) :: rest) = 1 + ((cellsR a v rest).map (fun c => c.2.2 ^ 2 * phiC c.1 c.2.1 1)).sum -
      ((cellsR a v rest).map (fun c' => c'.2.2 *
        ((cellsR a v rest).map (fun c => c.2.2 * ∫ u in c'.1..c'.2.1, PhiK c.1 c.2.1 u)).sum)).sum := by
  unfold cEta
  rw [I1_eq h, I2_eq h]

/-! ## Riemann sums for antitone functions -/

theorem anti_riemann {f : ℝ → ℝ} {lo hi : ℝ} {n : ℕ} (hn : 0 < n) (hlh : lo ≤ hi) (hf : AntitoneOn f (Icc lo hi)) :
    ∑ k ∈ Finset.range n, (hi - lo) / n * f (lo + (hi - lo) * (k + 1) / n) ≤ ∫ t in lo..hi, f t ∧
    ∫ t in lo..hi, f t ≤ ∑ k ∈ Finset.range n, (hi - lo) / n * f (lo + (hi - lo) * k / n) := by
  set g : ℕ → ℝ := fun k => lo + (hi - lo) * k / n with hg
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : g 0 = lo := by simp [hg]
  have hgn : g n = hi := by simp only [hg]; field_simp; ring
  have hmono : ∀ k, g k ≤ g (k + 1) := by
    intro k; simp only [hg]; push_cast
    have : (hi - lo) * k / n ≤ (hi - lo) * (k + 1) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hnr.le
    linarith
  have hsub : ∀ k < n, Icc (g k) (g (k + 1)) ⊆ Icc lo hi := by
    intro k hk
    apply Icc_subset_Icc
    · simp only [hg]
      have : 0 ≤ (hi - lo) * k / n := div_nonneg (mul_nonneg (by linarith) (by positivity)) hnr.le
      linarith
    · simp only [hg]
      have hk' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
      have : (hi - lo) * ((k + 1 : ℕ) : ℝ) / n ≤ hi - lo := by
        rw [div_le_iff₀ hnr]; push_cast; nlinarith
      linarith
  have hint : ∀ k < n, IntervalIntegrable f volume (g k) (g (k + 1)) := fun k hk =>
    AntitoneOn.intervalIntegrable (by rw [uIcc_of_le (hmono k)]; exact hf.mono (hsub k hk))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hg0, hgn] at hsum
  have hw : ∀ k, g (k + 1) - g k = (hi - lo) / n := by
    intro k; simp only [hg]; push_cast; field_simp; ring
  rw [← hsum]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hfk : ∀ t ∈ Icc (g k) (g (k + 1)), f (g (k + 1)) ≤ f t := fun t ht =>
      hf (hsub k hk' ht) (hsub k hk' ⟨hmono k, le_rfl⟩) ht.2
    calc (hi - lo) / n * f (lo + (hi - lo) * (k + 1) / n) = ∫ t in g k..g (k + 1), f (g (k + 1)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hw]; simp [hg]
      _ ≤ _ := integral_mono_on (hmono k) intervalIntegrable_const (hint k hk') hfk
  · apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hfk : ∀ t ∈ Icc (g k) (g (k + 1)), f t ≤ f (g k) := fun t ht =>
      hf (hsub k hk' ⟨le_rfl, hmono k⟩) (hsub k hk' ht) ht.1
    calc ∫ t in g k..g (k + 1), f t ≤ ∫ t in g k..g (k + 1), f (g k) :=
          integral_mono_on (hmono k) (hint k hk') intervalIntegrable_const hfk
      _ = (hi - lo) / n * f (lo + (hi - lo) * k / n) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hw]

end S10
end Omega3
