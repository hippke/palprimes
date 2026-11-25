import Omega3.Items.S10_Box

/-!
# S10 helpers, part 6: the box test and the band allowance
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

def boxG (a1 : ℤ) (cs : List Cell) (th tl : ℕ × ℕ × ℕ) : ℤ :=
  let c : ℤ := eminN 0 cs (Qn - th.1) (Qn - tl.1) * Qn * TP - a1
  (((Qn - th.1) * TP * En * Qn : ℕ) : ℤ) + (if 0 ≤ c then c * tl.1 else c * th.1) +
    ((Pn tl.1 tl.2.2 cs : ℤ) - Nn th.1 th.2.1 cs) * Qn

def SQ : ℕ := Qn * TP * En * Qn

def boxOK (xn xd : ℕ) (a1 : ℤ) (cs : List Cell) (th tl : ℕ × ℕ × ℕ) : Bool :=
  if (Qn - tl.1) * (xd - xn) * 85 ≤ 2 * Qn * xd then true else
  let G := boxG a1 cs th tl
  let t2n : ℕ := (Qn - tl.1) * (xd - xn)
  let t2d : ℕ := 2 * Qn * xd
  let L : ℤ := ((D0 - 1 : ℕ) : ℤ) * ((83 * xd : ℕ) - (85 * xn : ℕ) : ℤ) * (G * D0 - SQ) ^ 2
  let Ld : ℤ := ((D0 * 85 * xd * (SQ * D0) ^ 2 : ℕ) : ℤ)
  decide ((SQ : ℤ) < G * D0) &&
    (decide (((9999 * t2n ^ 2 : ℕ) : ℤ) * Ld ≤ L * 1000 * ((t2d ^ 2 : ℕ) : ℤ)) ||
     decide ((((85 * t2n : ℕ) : ℤ) - t2d) * Ld ≤ L * 85 * t2d))

lemma SQ_pos : (0 : ℝ) < SQ := by norm_num [SQ, Qn, TP, En]

/-- Lower bound of `g_η` on a box. -/
theorem gEta_box (A0 : ℕ) (cs : List Cell) (hcs : ∀ c ∈ cs, CellOK A0 c) (a v : ℚ) (rest : List (ℚ × ℚ))
    (he : stepOfCells cs = (a, v) :: rest) (hG : Good a v rest) (hcr : cellsR a v rest = cs.map rc)
    (th tl : ℕ × ℕ × ℕ) (hth : A0 ≤ th.1 → LogOK th) (htl : A0 ≤ tl.1 → LogOK tl) (hnh : th.1 ≤ Qn)
    (u : ℝ) (hu1 : 1 - (th.1 : ℝ) / Qn ≤ u) (hu2 : u ≤ 1 - (tl.1 : ℝ) / Qn) (hu : u < 1) :
    (boxG (A1hi cs) cs th tl : ℝ) / SQ ≤ gEta ((a, v) :: rest) u := by
  have hQ := Qn_pos
  have hT := TP_pos
  have hE := En_pos
  have hS : (0 : ℝ) < Qn * TP * En := by positivity
  have hAhat : ∀ s, 0 < s → s ≤ 1 → Ahat ((a, v) :: rest) s = AR cs s := by
    intro s h0 h1
    rw [Ahat_eq hG s h0 h1, hcr, List.map_map]; rfl
  have hs0 : 0 < 1 - u := by linarith
  have hu0 : 0 ≤ u := by
    have : (th.1 : ℝ) / Qn ≤ 1 := by rw [div_le_one hQ]; exact_mod_cast hnh
    linarith
  have hA1 := AR_one A0 cs hcs
  have hAb := AR_box A0 cs hcs tl.1 tl.2.1 tl.2.2 th.1 th.2.1 th.2.2 htl hth (1 - u) hs0 (by linarith) (by linarith)
  have hev : (eminN 0 cs (Qn - th.1) (Qn - tl.1) : ℝ) / En ≤ StepFn.eval ((a, v) :: rest) u := by
    rw [← eminN_eq, ← he, eval_eq]
    have hsub : ((Qn - th.1 : ℕ) : ℝ) = Qn - th.1 := Nat.cast_sub hnh
    have hsub2 : ((Qn - tl.1 : ℕ) : ℝ) / Qn ≥ u := by
      rcases le_total tl.1 Qn with h | h
      · rw [Nat.cast_sub h, ge_iff_le, le_div_iff₀ hQ]
        have : (1 - (tl.1 : ℝ) / Qn) * Qn = Qn - tl.1 := by field_simp
        nlinarith
      · rw [Nat.sub_eq_zero_of_le h]
        have : (Qn : ℝ) ≤ tl.1 := by exact_mod_cast h
        have : (1 : ℝ) ≤ tl.1 / Qn := by rw [le_div_iff₀ hQ]; linarith
        simp only [Nat.cast_zero, zero_div]; linarith
    have h0 : ((0 : ℤ) : ℝ) / En = 0 := by simp
    rw [h0]
    apply eval_ge_emin _ _ _ _ u
    · rw [he]; exact hG.sorted
    · rw [hsub, sub_div, div_self hQ.ne']; exact hu1
    · exact hsub2
  unfold gEta
  rw [hAhat 1 one_pos le_rfl, hAhat (1 - u) hs0 (by linarith)]
  -- algebra
  set em : ℤ := eminN 0 cs (Qn - th.1) (Qn - tl.1)
  set A1 : ℤ := A1hi cs
  set c : ℤ := em * Qn * TP - A1 with hcdef
  have hX : (c : ℝ) / (Qn * TP * En) ≤ StepFn.eval ((a, v) :: rest) u - AR cs 1 := by
    have : (c : ℝ) / (Qn * TP * En) = (em : ℝ) / En - (A1 : ℝ) / (Qn * TP * En) := by
      simp only [c]; push_cast; field_simp
    rw [this]; linarith
  have hct : ((if 0 ≤ c then c * tl.1 else c * th.1 : ℤ) : ℝ) / (Qn * TP * En * Qn) ≤
      (StepFn.eval ((a, v) :: rest) u - AR cs 1) * (1 - u) := by
    have hl : (tl.1 : ℝ) / Qn ≤ 1 - u := by linarith
    have hh : 1 - u ≤ (th.1 : ℝ) / Qn := by linarith
    split_ifs with hc
    · have hcR : (0 : ℝ) ≤ c := by exact_mod_cast hc
      calc ((c * tl.1 : ℤ) : ℝ) / (Qn * TP * En * Qn) = (c : ℝ) / (Qn * TP * En) * ((tl.1 : ℝ) / Qn) := by
            push_cast; field_simp
        _ ≤ (c : ℝ) / (Qn * TP * En) * (1 - u) := mul_le_mul_of_nonneg_left hl (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hX hs0.le
    · have hcR : (c : ℝ) < 0 := by exact_mod_cast (not_le.mp hc)
      calc ((c * th.1 : ℤ) : ℝ) / (Qn * TP * En * Qn) = (c : ℝ) / (Qn * TP * En) * ((th.1 : ℝ) / Qn) := by
            push_cast; field_simp
        _ ≤ (c : ℝ) / (Qn * TP * En) * (1 - u) :=
            mul_le_mul_of_nonpos_left hh (div_nonpos_of_nonpos_of_nonneg hcR.le (by positivity))
        _ ≤ _ := mul_le_mul_of_nonneg_right hX hs0.le
  have hu1' : ((((Qn - th.1) * TP * En * Qn : ℕ) : ℤ) : ℝ) / (Qn * TP * En * Qn) ≤ u := by
    push_cast [Nat.cast_sub hnh]
    rw [div_le_iff₀ (by positivity)]
    have e : (1 - (th.1 : ℝ) / Qn) * Qn = Qn - th.1 := by field_simp
    have h' : (Qn : ℝ) - th.1 ≤ u * Qn := by nlinarith [mul_le_mul_of_nonneg_right hu1 hQ.le]
    nlinarith [mul_le_mul_of_nonneg_right h' (show (0 : ℝ) ≤ TP * En * Qn by positivity)]
  have hP : (((Pn tl.1 tl.2.2 cs : ℤ) - Nn th.1 th.2.1 cs) * Qn : ℤ) / ((Qn * TP * En * Qn : ℝ)) ≤ AR cs (1 - u) := by
    have : ((((Pn tl.1 tl.2.2 cs : ℤ) - Nn th.1 th.2.1 cs) * Qn : ℤ) : ℝ) / ((Qn * TP * En * Qn : ℝ)) =
        ((Pn tl.1 tl.2.2 cs : ℝ) - Nn th.1 th.2.1 cs) / (Qn * TP * En) := by
      push_cast; field_simp
    rw [this]; exact hAb
  have hSQ : (SQ : ℝ) = Qn * TP * En * Qn := by simp [SQ]
  simp only [boxG]
  rw [hSQ, ← hcdef]
  push_cast
  rw [add_div, add_div]
  push_cast at hu1' hct hP
  have e : 1 - (1 + AR cs 1) * (1 - u) + AR cs (1 - u) + StepFn.eval ((a, v) :: rest) u * (1 - u) =
      u + (StepFn.eval ((a, v) :: rest) u - AR cs 1) * (1 - u) + AR cs (1 - u) := by ring
  rw [e]
  linarith


theorem box_final (xn xd : ℕ) (hxd : 0 < xd) (hx3 : xd ≤ 3 * xn) (hxU : 85 * xn < 83 * xd) (hxx : xn < xd)
    (a1 : ℤ) (cs : List Cell) (th tl : ℕ × ℕ × ℕ) (hnl : tl.1 ≤ Qn) (hb : boxOK xn xd a1 cs th tl = true)
    (hrel : ¬ ((Qn - tl.1) * (xd - xn) * 85 ≤ 2 * Qn * xd)) (g : ℝ) (hg : (boxG a1 cs th tl : ℝ) / SQ ≤ g)
    (u : ℝ) (hu0 : 0 ≤ u) (hu2 : u ≤ 1 - (tl.1 : ℝ) / Qn) :
    1 / (D0 : ℝ) ≤ g ∧ Wf (u * (1 - (xn : ℝ) / xd) / 2) ≤
      (1 - 1 / (D0 : ℝ)) * (UU - (xn : ℝ) / xd) * (g - 1 / (D0 : ℝ)) ^ 2 := by
  unfold boxOK at hb
  rw [if_neg hrel] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  set G : ℤ := boxG a1 cs th tl
  have hQ := Qn_pos
  have hSQ := SQ_pos
  have hD : (0 : ℝ) < D0 := by norm_num [D0]
  have hD1 : (1 : ℝ) ≤ D0 := by norm_num [D0]
  have hxdR : (0 : ℝ) < xd := by exact_mod_cast hxd
  have h1R : (SQ : ℝ) < G * D0 := by exact_mod_cast h1
  have hγ : 1 / (D0 : ℝ) < (G : ℝ) / SQ := by
    rw [div_lt_div_iff₀ hD hSQ]; linarith
  have hge : 1 / (D0 : ℝ) ≤ g := le_trans hγ.le hg
  refine ⟨hge, ?_⟩
  -- the point t2
  set xl : ℝ := (xn : ℝ) / xd
  have hxl3 : 1 / 3 ≤ xl := by
    simp only [xl]; rw [le_div_iff₀ hxdR]; have : (xd : ℝ) ≤ 3 * xn := by exact_mod_cast hx3
    linarith
  have hxl1 : xl < 1 := by simp only [xl]; rw [div_lt_one hxdR]; exact_mod_cast hxx
  have hUxl : 0 < UU - xl := by
    simp only [xl, UU]; rw [sub_pos, div_lt_iff₀ hxdR]
    have : (85 : ℝ) * xn < 83 * xd := by exact_mod_cast hxU
    linarith
  set t2 : ℝ := (1 - (tl.1 : ℝ) / Qn) * (1 - xl) / 2
  have hsq : ((Qn - tl.1 : ℕ) : ℝ) = Qn - tl.1 := Nat.cast_sub hnl
  have hsx : ((xd - xn : ℕ) : ℝ) = xd - xn := Nat.cast_sub hxx.le
  have ht2 : t2 = (((Qn - tl.1) * (xd - xn) : ℕ) : ℝ) / ((2 * Qn * xd : ℕ) : ℝ) := by
    simp only [t2, xl]; push_cast [hsq, hsx]; field_simp
  have hrelR : ((2 * Qn * xd : ℕ) : ℝ) < (((Qn - tl.1) * (xd - xn) * 85 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_of_not_le hrel
  have hD2 : (0 : ℝ) < ((2 * Qn * xd : ℕ) : ℝ) := by push_cast; positivity
  have ht2m : mm < t2 := by
    rw [ht2, lt_div_iff₀ hD2]; simp only [mm]; push_cast at hrelR ⊢; linarith
  have ht23 : t2 ≤ 1 / 3 := by
    simp only [t2]
    have : 0 ≤ (tl.1 : ℝ) / Qn := by positivity
    nlinarith
  have htt : u * (1 - xl) / 2 ≤ t2 := by
    simp only [t2]; nlinarith
  have hW1 : Wf (u * (1 - xl) / 2) ≤ Wf t2 := Wf_mono (by nlinarith) htt ht23
  rw [Wf_mid ht2m ht23] at hW1
  -- L / Ld
  set L : ℤ := ((D0 - 1 : ℕ) : ℤ) * ((83 * xd : ℕ) - (85 * xn : ℕ) : ℤ) * (G * D0 - SQ) ^ 2
  set Ld : ℤ := ((D0 * 85 * xd * (SQ * D0) ^ 2 : ℕ) : ℤ)
  have hLd : (0 : ℝ) < Ld := by simp only [Ld]; push_cast; positivity
  have hD0s : ((D0 - 1 : ℕ) : ℝ) = D0 - 1 := Nat.cast_sub (by norm_num [D0])
  have hLL : (L : ℝ) / Ld = (1 - 1 / (D0 : ℝ)) * (UU - xl) * ((G : ℝ) / SQ - 1 / (D0 : ℝ)) ^ 2 := by
    simp only [L, Ld, xl, UU]; push_cast [hD0s]; field_simp
  have hfin : (L : ℝ) / Ld ≤ (1 - 1 / (D0 : ℝ)) * (UU - xl) * (g - 1 / (D0 : ℝ)) ^ 2 := by
    rw [hLL]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by rw [sub_nonneg, div_le_one hD]; exact hD1) hUxl.le)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  refine le_trans hW1 (le_trans ?_ hfin)
  rcases h2 with h2 | h2
  · refine le_trans (min_le_left _ _) ?_
    have h2R : (((9999 * ((Qn - tl.1) * (xd - xn)) ^ 2 : ℕ) : ℤ) : ℝ) * Ld ≤
        (L : ℝ) * 1000 * (((2 * Qn * xd) ^ 2 : ℕ) : ℤ) := by exact_mod_cast h2
    rw [le_div_iff₀ hLd, ht2]; simp only [kSq]
    push_cast [hsq, hsx] at h2R ⊢
    have hp : (0 : ℝ) < (2 * Qn * xd) ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, mul_comm, ← mul_div_assoc, div_le_iff₀ hp]
    nlinarith
  · refine le_trans (min_le_right _ _) ?_
    have h2R : ((((85 * ((Qn - tl.1) * (xd - xn)) : ℕ) : ℤ) - ((2 * Qn * xd : ℕ) : ℤ) : ℤ) : ℝ) * Ld ≤
        (L : ℝ) * 85 * ((2 * Qn * xd : ℕ) : ℤ) := by exact_mod_cast h2
    rw [le_div_iff₀ hLd, ht2]; simp only [mm]
    push_cast [hsq, hsx] at h2R hD2 ⊢
    have e : ((((Qn : ℝ) - tl.1) * (xd - xn)) / (2 * Qn * xd) - 1 / 85) =
        (85 * (((Qn : ℝ) - tl.1) * (xd - xn)) - 2 * Qn * xd) / (85 * (2 * Qn * xd)) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

lemma exists_box {α : Type*} (f : α → ℝ) (r : ℝ) : ∀ (l : List α) (t : α), r ≤ f t → (∃ t' ∈ l, f t' ≤ r) →
    ∃ p ∈ List.zip (t :: l) l, f p.2 ≤ r ∧ r ≤ f p.1
  | [], _, _, h => by simp at h
  | t1 :: l, t, ht, h => by
    by_cases h1 : f t1 ≤ r
    · exact ⟨(t, t1), by simp, h1, ht⟩
    · have h' : ∃ t' ∈ l, f t' ≤ r := by
        obtain ⟨t', ht', hr⟩ := h
        simp only [List.mem_cons] at ht'
        rcases ht' with ht' | ht'
        · subst ht'; exact absurd hr h1
        · exact ⟨t', ht', hr⟩
      obtain ⟨p, hp, hp1, hp2⟩ := exists_box f r l t1 (not_le.mp h1).le h'
      exact ⟨p, by simp only [List.zip_cons_cons, List.mem_cons]; right; exact hp, hp1, hp2⟩

/-- The band allowance from the box tests. -/
theorem band_allow (A0 : ℕ) (cs : List Cell) (hcs : ∀ c ∈ cs, CellOK A0 c) (a v : ℚ) (rest : List (ℚ × ℚ))
    (he : stepOfCells cs = (a, v) :: rest) (hG : Good a v rest) (hcr : cellsR a v rest = cs.map rc)
    (t0 : ℕ × ℕ × ℕ) (tr : List (ℕ × ℕ × ℕ)) (ht0 : t0.1 = Qn)
    (hval : ∀ t ∈ t0 :: tr, A0 ≤ t.1 → LogOK t) (hle : ∀ t ∈ t0 :: tr, t.1 ≤ Qn) (hz : ∃ t ∈ tr, t.1 = 0)
    (xn xd : ℕ) (hxd : 0 < xd) (hx3 : xd ≤ 3 * xn) (hxU : 85 * xn < 83 * xd) (hxx : xn < xd)
    (hbox : ∀ p ∈ List.zip (t0 :: tr) tr, boxOK xn xd (A1hi cs) cs p.1 p.2 = true)
    (xr : ℝ) (hxr : xr ≤ 2 * UU - 1) :
    ∀ x t : ℝ, (xn : ℝ) / xd ≤ x → x ≤ xr → mm < t → 2 * t < 1 - x →
      1 / (D0 : ℝ) ≤ gEta ((a, v) :: rest) (2 * t / (1 - x)) ∧
        Wf t ≤ (1 - 1 / (D0 : ℝ)) * (UU - x) * (gEta ((a, v) :: rest) (2 * t / (1 - x)) - 1 / (D0 : ℝ)) ^ 2 := by
  intro x t hx1 hx2 hmt h2t
  have hQ := Qn_pos
  have hxdR : (0 : ℝ) < xd := by exact_mod_cast hxd
  set xl : ℝ := (xn : ℝ) / xd
  have hxl3 : 1 / 3 ≤ xl := by
    simp only [xl]; rw [le_div_iff₀ hxdR]; have : (xd : ℝ) ≤ 3 * xn := by exact_mod_cast hx3
    linarith
  have hUxl : 0 < UU - xl := by
    simp only [xl, UU]; rw [sub_pos, div_lt_iff₀ hxdR]
    have : (85 : ℝ) * xn < 83 * xd := by exact_mod_cast hxU
    linarith
  have hm : mm = 1 / 85 := rfl
  have ht0' : 0 < t := by rw [hm] at hmt; linarith
  have h1x : 0 < 1 - x := by linarith
  set u := 2 * t / (1 - x)
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by simp only [u]; rw [div_lt_one h1x]; exact h2t
  have htu : u * (1 - x) / 2 = t := by simp only [u]; field_simp
  -- the box containing u
  obtain ⟨p, hp, hp1, hp2⟩ := exists_box (fun t : ℕ × ℕ × ℕ => (t.1 : ℝ)) ((1 - u) * Qn) tr t0
    (by simp only [ht0]; nlinarith) (by
      obtain ⟨t', ht', h0⟩ := hz
      exact ⟨t', ht', by simp only [h0, Nat.cast_zero]; nlinarith⟩)
  try simp only at hp1 hp2
  have hpm1 : p.1 ∈ t0 :: tr := (List.of_mem_zip hp).1
  have hpm2 : p.2 ∈ t0 :: tr := List.mem_cons_of_mem _ (List.of_mem_zip hp).2
  have hb1 : 1 - (p.1.1 : ℝ) / Qn ≤ u := by
    have : 1 - u ≤ (p.1.1 : ℝ) / Qn := by rw [le_div_iff₀ hQ]; exact hp2
    linarith
  have hb2 : u ≤ 1 - (p.2.1 : ℝ) / Qn := by
    have : (p.2.1 : ℝ) / Qn ≤ 1 - u := by rw [div_le_iff₀ hQ]; exact hp1
    linarith
  have hg := gEta_box A0 cs hcs a v rest he hG hcr p.1 p.2 (hval p.1 hpm1) (hval p.2 hpm2) (hle p.1 hpm1) u hb1 hb2 hu1
  have hxl1 : xl ≤ 1 := le_trans hx1 (by linarith)
  have hrel : ¬ ((Qn - p.2.1) * (xd - xn) * 85 ≤ 2 * Qn * xd) := by
    intro hcon
    have hcR : (((Qn - p.2.1) * (xd - xn) * 85 : ℕ) : ℝ) ≤ ((2 * Qn * xd : ℕ) : ℝ) := by exact_mod_cast hcon
    push_cast [Nat.cast_sub (hle p.2 hpm2), Nat.cast_sub hxx.le] at hcR
    have e : (1 - (p.2.1 : ℝ) / Qn) * (1 - xl) = ((Qn - p.2.1) * (xd - xn)) / (Qn * xd) := by
      simp only [xl]; field_simp
    have h85 : (1 - (p.2.1 : ℝ) / Qn) * (1 - xl) ≤ 2 / 85 := by
      rw [e, div_le_iff₀ (by positivity)]; linarith
    have h3 : u * (1 - xl) ≤ (1 - (p.2.1 : ℝ) / Qn) * (1 - xl) := mul_le_mul_of_nonneg_right hb2 (by linarith)
    have h4 : u * (1 - x) ≤ u * (1 - xl) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
    rw [hm] at hmt
    have : u * (1 - x) = 2 * t := by rw [← htu]; ring
    linarith
  obtain ⟨hf1, hf2⟩ := box_final xn xd hxd hx3 hxU hxx (A1hi cs) cs p.1 p.2 (hle p.2 hpm2) (hbox p hp) hrel
    (gEta ((a, v) :: rest) u) hg u hu0.le hb2
  refine ⟨hf1, ?_⟩
  have hxU2 : x ≤ 2 * UU - 1 := le_trans hx2 hxr
  have hR := W_ratio hxl3 hx1 hxU2 hu0 hu1.le
  rw [htu] at hR
  have hUx : 0 ≤ UU - x := by simp only [UU] at hxU2 ⊢; linarith
  have hk : 0 ≤ 1 - 1 / (D0 : ℝ) := by rw [sub_nonneg, div_le_one (by norm_num [D0])]; norm_num [D0]
  have h5 : Wf t * (UU - xl) ≤ (1 - 1 / (D0 : ℝ)) * (UU - x) * (gEta ((a, v) :: rest) u - 1 / (D0 : ℝ)) ^ 2 * (UU - xl) := by
    calc Wf t * (UU - xl) ≤ Wf (u * (1 - xl) / 2) * (UU - x) := hR
      _ ≤ ((1 - 1 / (D0 : ℝ)) * (UU - xl) * (gEta ((a, v) :: rest) u - 1 / (D0 : ℝ)) ^ 2) * (UU - x) :=
          mul_le_mul_of_nonneg_right hf2 hUx
      _ = _ := by ring
  exact le_of_mul_le_mul_right h5 hUxl

end S10
end Omega3
