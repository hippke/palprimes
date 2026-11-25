import Omega3.Items.S10_Band
import Omega3.Items.S10_Cost

/-!
# S10 helpers, part 8: the per-band Boolean check and its soundness
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

/-- Real step function of Nat cells. -/
def stepOfCl (cl : List (ℕ × ℕ × ℤ)) : StepFn := cl.map (fun c => ((c.1 : ℚ) / Qn, (c.2.2 : ℚ) / En))

def cellOKb (A0 : ℕ) (sg : List ℕ) (c : ℕ × ℕ × ℤ) : Bool :=
  decide (A0 ≤ c.1) && decide (0 < c.1) && decide (c.1 < c.2.1) && decide (c.2.1 ≤ Qn) && sg.elem c.1 && sg.elem c.2.1

def incB : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => decide (a < b) && incB (b :: r)

theorem incB_pairwise : ∀ l : List ℕ, incB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := incB_pairwise (b :: r) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]; exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.mp ih).1 x hx)

/-- The Boolean check of one band (left edge `xn/xd`, cost bound `cn`). -/
def bandChk (A0 : ℕ) (m0 : ℤ) (es : List ℕ) (ms : List ℤ) (sgr : List ℕ) (xn xd cn : ℕ) : Bool :=
  let tab := logTab A0 Qn 0 0 sgr
  let cl := cellsNat A0 m0 es ms
  let cs := mkCells tab cl
  decide (0 < A0) && decide (es.length = ms.length) && chainOK A0 Qn sgr && sgr.elem 0 &&
    cl.all (cellOKb A0 (Qn :: sgr)) && incB (cl.map Prod.fst) &&
    (List.zip tab tab.tail).all (fun p => boxOK xn xd (A1hi cs) cs p.1 p.2) && costOK cs cn


lemma chain_lt (A0 : ℕ) : ∀ (rest : List ℕ) (n : ℕ), chainOK A0 n rest = true → ∀ x ∈ rest, x < n
  | [], _, _, x, hx => by simp at hx
  | n2 :: rest, n, h, x, hx => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]; exact h.1.1
    · exact lt_trans (chain_lt A0 rest n2 h.2 x hx) h.1.1

lemma logTab_cons (A0 : ℕ) (rest : List ℕ) (n lo hi : ℕ) :
    ∃ tr, logTab A0 n lo hi rest = (n, lo, hi) :: tr ∧ tr.map Prod.fst = rest := by
  have h := logTab_fst A0 rest n lo hi
  cases rest with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons n2 rest =>
    refine ⟨_, rfl, ?_⟩
    simp only [logTab, List.map_cons, List.cons.injEq] at h
    exact h.2

lemma stepOfCl_head (A : ℕ) (m : ℤ) (es : List ℕ) (ms : List ℤ) :
    stepOfCl (cellsNat A m es ms) = ((A : ℚ) / Qn, (m : ℚ) / En) :: (stepOfCl (cellsNat A m es ms)).tail := by
  cases es with
  | nil => rfl
  | cons B es => cases ms with
    | nil => rfl
    | cons m' ms => rfl

/-- `(A/Q, B/Q, m/E)` in ℚ. -/
def toQ3 (c : ℕ × ℕ × ℤ) : ℚ × ℚ × ℚ := ((c.1 : ℚ) / Qn, (c.2.1 : ℚ) / Qn, (c.2.2 : ℚ) / En)

theorem cellsAux_eq : ∀ (es : List ℕ) (ms : List ℤ) (A : ℕ) (m : ℤ), es.length = ms.length →
    cellsAux ((A : ℚ) / Qn) ((m : ℚ) / En) (stepOfCl (cellsNat A m es ms)).tail = (cellsNat A m es ms).map toQ3
  | [], [], A, m, _ => by
    simp [cellsNat, stepOfCl, cellsAux, toQ3, Qn]
  | B :: es, m' :: ms, A, m, h => by
    have h' : es.length = ms.length := by simpa using h
    have ih := cellsAux_eq es ms B m' h'
    simp only [cellsNat, stepOfCl, List.map_cons, List.tail_cons]
    have hh := stepOfCl_head B m' es ms
    simp only [stepOfCl] at hh ih
    rw [hh, cellsAux, ih]
    rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem band_ok (A0 : ℕ) (m0 : ℤ) (es : List ℕ) (ms : List ℤ) (sgr : List ℕ) (xn xd cn : ℕ)
    (hchk : bandChk A0 m0 es ms sgr xn xd cn = true)
    (hxd : 0 < xd) (hx3 : xd ≤ 3 * xn) (hxU : 85 * xn < 83 * xd) (hxx : xn < xd) (xr : ℝ) (hxr : xr ≤ 2 * UU - 1) :
    StepOK (stepOfCl (cellsNat A0 m0 es ms)) ∧
    (∀ x t : ℝ, (xn : ℝ) / xd ≤ x → x ≤ xr → mm < t → 2 * t < 1 - x →
      1 / (D0 : ℝ) ≤ gEta (stepOfCl (cellsNat A0 m0 es ms)) (2 * t / (1 - x)) ∧
        Wf t ≤ (1 - 1 / (D0 : ℝ)) * (UU - x) * (gEta (stepOfCl (cellsNat A0 m0 es ms)) (2 * t / (1 - x)) - 1 / (D0 : ℝ)) ^ 2) ∧
    cEta (stepOfCl (cellsNat A0 m0 es ms)) ≤ 1 + (cn : ℝ) / 1000000 := by
  simp only [bandChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hA0, hlen⟩, hch⟩, hz0⟩, hcl⟩, hinc⟩, hbox⟩, hcost⟩ := hchk
  set tab := logTab A0 Qn 0 0 sgr with htab
  set cl := cellsNat A0 m0 es ms with hcl_def
  set cs := mkCells tab cl with hcs_def
  have hlt := chain_lt A0 sgr Qn hch
  obtain ⟨tr, htr, htrf⟩ := logTab_cons A0 sgr Qn 0 0
  have hval : ∀ t ∈ tab, A0 ≤ t.1 → LogOK t := logTab_ok A0 hA0 sgr Qn 0 0 hch (fun _ => LogOK_Q)
  have hfst : tab.map Prod.fst = Qn :: sgr := logTab_fst A0 sgr Qn 0 0
  have hle : ∀ t ∈ tab, t.1 ≤ Qn := by
    intro t ht
    have : t.1 ∈ Qn :: sgr := by rw [← hfst]; exact List.mem_map_of_mem ht
    simp only [List.mem_cons] at this
    rcases this with h | h
    · exact h.le
    · exact (hlt _ h).le
  have hz : ∃ t ∈ tr, t.1 = 0 := by
    have : (0 : ℕ) ∈ tr.map Prod.fst := by rw [htrf]; exact List.elem_iff.mp hz0
    obtain ⟨t, ht, h0⟩ := List.mem_map.mp this
    exact ⟨t, ht, h0⟩
  -- cells
  have hcok : ∀ c ∈ cs, CellOK A0 c := by
    intro c hc
    simp only [hcs_def, mkCells, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    have hb := hcl c0 hc0
    simp only [cellOKb, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
    have m5 : c0.1 ∈ tab.map Prod.fst := by rw [hfst]; exact List.elem_iff.mp h5
    have m6 : c0.2.1 ∈ tab.map Prod.fst := by rw [hfst]; exact List.elem_iff.mp h6
    exact ⟨h1, h2, h3, h4, hval _ (lkp_mem tab c0.1 m5) h1, hval _ (lkp_mem tab c0.2.1 m6) (le_trans h1 h3.le)⟩
  have hstep : stepOfCells cs = stepOfCl cl := by
    simp only [hcs_def, stepOfCells, mkCells, stepOfCl, List.map_map]; rfl
  have hhead := stepOfCl_head A0 m0 es ms
  set a : ℚ := (A0 : ℚ) / Qn
  set v : ℚ := (m0 : ℚ) / En
  set rest := (stepOfCl cl).tail
  have he : stepOfCells cs = (a, v) :: rest := by rw [hstep]; exact hhead
  -- Good
  have hQq : (0 : ℚ) < Qn := by norm_num [Qn]
  have hsorted : Sorted (stepOfCl cl) := by
    simp only [Sorted, stepOfCl, List.pairwise_map]
    have hp := incB_pairwise _ hinc
    rw [List.pairwise_map] at hp
    exact hp.imp (fun h => div_lt_div_of_pos_right (by exact_mod_cast h) hQq)
  have hG : Good a v rest := by
    refine ⟨?_, ?_, ?_⟩
    · have := hsorted; rwa [hhead] at this
    · simp only [a]; exact div_pos (by exact_mod_cast hA0) hQq
    · intro p hp
      rw [← hhead] at hp
      simp only [stepOfCl, List.mem_map] at hp
      obtain ⟨c0, hc0, rfl⟩ := hp
      have hb := hcl c0 hc0
      simp only [cellOKb, Bool.and_eq_true, decide_eq_true_eq] at hb
      show ((c0.1 : ℕ) : ℚ) / Qn < 1
      rw [div_lt_one hQq]; exact_mod_cast lt_of_lt_of_le hb.1.1.1.2 hb.1.1.2
  have hcr : cellsR a v rest = cs.map rc := by
    simp only [cellsR]
    rw [cellsAux_eq es ms A0 m0 hlen]
    simp only [hcs_def, mkCells, List.map_map]
    apply List.map_congr_left
    intro c _
    simp [toQ3, rc]
  have hbox' : ∀ p ∈ List.zip ((Qn, 0, 0) :: tr) tr, boxOK xn xd (A1hi cs) cs p.1 p.2 = true := by
    intro p hp
    have htr' : tab = (Qn, 0, 0) :: tr := htr
    rw [htr'] at hbox
    exact hbox p (by simpa using hp)
  have htr' : tab = (Qn, 0, 0) :: tr := htr
  have hval' : ∀ t ∈ (Qn, 0, 0) :: tr, A0 ≤ t.1 → LogOK t := by rw [← htr']; exact hval
  have hle' : ∀ t ∈ (Qn, 0, 0) :: tr, t.1 ≤ Qn := by rw [← htr']; exact hle
  have hE : stepOfCl cl = (a, v) :: rest := hhead
  rw [hE]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [List.pairwise_map]; exact hG.sorted
    · intro pr hpr
      exact ⟨by
        have := hG.cells
        rw [← hE] at hpr
        simp only [stepOfCl, List.mem_map] at hpr
        obtain ⟨c0, hc0, rfl⟩ := hpr
        have hb := hcl c0 hc0
        simp only [cellOKb, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact div_pos (by exact_mod_cast hb.1.1.1.1.2) hQq, hG.lt1 pr hpr⟩
  · exact band_allow A0 cs hcok a v rest he hG hcr (Qn, 0, 0) tr rfl hval' hle' hz xn xd hxd hx3 hxU hxx hbox' xr hxr
  · rw [cEta_eq hG, hcr]
    simp only [List.map_map]
    exact cEta_bound A0 cs hcok cn hcost

end S10
end Omega3
