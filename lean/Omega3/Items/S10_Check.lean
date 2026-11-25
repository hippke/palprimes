import Omega3.Items.S10_Real
import Omega3.Items.S10_Log

/-!
# S10 helpers, part 4: the Nat/Int checker and its soundness (log table, cells, `φ` bounds)
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

/-! ## Log table -/

def logTab (A0 : ℕ) : ℕ → ℕ → ℕ → List ℕ → List (ℕ × ℕ × ℕ)
  | n, lo, hi, [] => [(n, lo, hi)]
  | n, lo, hi, n2 :: rest => (n, lo, hi) ::
      (if A0 ≤ n2 then logTab A0 n2 (lo + lstepLo n n2) (hi + lstepHi n n2) rest else logTab A0 n2 lo hi rest)

def chainOK (A0 : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | n, n2 :: rest => decide (n2 < n) && (decide (n2 < A0) || decide (n < 2 * n2)) && chainOK A0 n2 rest

lemma logTab_fst (A0 : ℕ) : ∀ (rest : List ℕ) (n lo hi : ℕ), (logTab A0 n lo hi rest).map Prod.fst = n :: rest
  | [], n, lo, hi => rfl
  | n2 :: rest, n, lo, hi => by
    simp only [logTab, List.map_cons]
    split_ifs <;> rw [logTab_fst A0 rest]

lemma NL_step {n n2 : ℕ} (h0 : 0 < n2) (h1 : n2 < n) : NL n2 = NL n + Real.log ((n : ℝ) / n2) := by
  have : (0 : ℝ) < n2 := by exact_mod_cast h0
  have : (0 : ℝ) < n := by exact_mod_cast (lt_trans h0 h1)
  unfold NL; rw [Real.log_div (by positivity) (by positivity)]; ring

theorem logTab_ok (A0 : ℕ) (hA0 : 0 < A0) : ∀ (rest : List ℕ) (n lo hi : ℕ), chainOK A0 n rest = true →
    (A0 ≤ n → LogOK (n, lo, hi)) → ∀ t ∈ logTab A0 n lo hi rest, A0 ≤ t.1 → LogOK t
  | [], n, lo, hi, _, h, t, ht, hA => by
    simp only [logTab, List.mem_singleton] at ht; subst ht; exact h hA
  | n2 :: rest, n, lo, hi, hc, h, t, ht, hA => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    simp only [logTab, List.mem_cons] at ht
    rcases ht with ht | ht
    · subst ht; exact h hA
    · split_ifs at ht with hn2
      · apply logTab_ok A0 hA0 rest n2 _ _ h3 _ t ht hA
        intro _
        have h2' : n < 2 * n2 := by rcases h2 with h2 | h2 <;> omega
        obtain ⟨l1, l2⟩ := h (le_trans hn2 h1.le)
        obtain ⟨s1, s2⟩ := lstep_ok n n2 h1 h2'
        simp only [LogOK] at l1 l2 ⊢
        rw [NL_step (lt_of_lt_of_le hA0 hn2) h1]
        push_cast
        constructor <;> nlinarith
      · exact logTab_ok A0 hA0 rest n2 lo hi h3 (fun h' => absurd h' hn2) t ht hA

/-- Lookup of a log entry. -/
def lkp : List (ℕ × ℕ × ℕ) → ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | t :: r, A => if t.1 = A then t.2 else lkp r A

lemma lkp_mem : ∀ (tab : List (ℕ × ℕ × ℕ)) (A : ℕ), A ∈ tab.map Prod.fst → (A, lkp tab A) ∈ tab
  | [], A, h => by simp at h
  | t :: r, A, h => by
    simp only [lkp]
    split_ifs with ht
    · rw [← ht]; simp
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm ht
      · exact List.mem_cons_of_mem _ (lkp_mem r A h)

/-! ## Cells -/

def cellsNat : ℕ → ℤ → List ℕ → List ℤ → List (ℕ × ℕ × ℤ)
  | A, m, B :: es, m' :: ms => (A, B, m) :: cellsNat B m' es ms
  | A, m, _, _ => [(A, Qn, m)]

structure Cell where
  A : ℕ
  lA : ℕ
  hA : ℕ
  B : ℕ
  lB : ℕ
  hB : ℕ
  m : ℤ

def mkCells (tab : List (ℕ × ℕ × ℕ)) (cl : List (ℕ × ℕ × ℤ)) : List Cell :=
  cl.map (fun c => ⟨c.1, (lkp tab c.1).1, (lkp tab c.1).2, c.2.1, (lkp tab c.2.1).1, (lkp tab c.2.1).2, c.2.2⟩)

/-- Real cell of a Nat cell. -/
noncomputable def rc (c : Cell) : ℝ × ℝ × ℝ := ((c.A : ℝ) / Qn, (c.B : ℝ) / Qn, (c.m : ℝ) / En)

/-- Validity of a cell. -/
def CellOK (A0 : ℕ) (c : Cell) : Prop :=
  A0 ≤ c.A ∧ 0 < c.A ∧ c.A < c.B ∧ c.B ≤ Qn ∧ LogOK (c.A, c.lA, c.hA) ∧ LogOK (c.B, c.lB, c.hB)

def phiLo (n hn : ℕ) (c : Cell) : ℕ :=
  if n ≤ c.A then 0 else if n ≤ c.B then n * (c.lA - hn) - (n - c.A) * TP else n * (c.lA - c.hB) - (c.B - c.A) * TP

def phiHi (n ln : ℕ) (c : Cell) : ℕ :=
  if n ≤ c.A then 0 else if n ≤ c.B then n * (c.hA - ln) - (n - c.A) * TP else n * (c.hA - c.lB) - (c.B - c.A) * TP

lemma log_div_Q (n : ℕ) (hn : 0 < n) : Real.log ((n : ℝ) / Qn) = -NL n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold NL; rw [Real.log_div this.ne' Qn_pos.ne']; ring

lemma NL_anti {n n' : ℕ} (hn : 0 < n) (h : n ≤ n') : NL n' ≤ NL n := by
  unfold NL
  have : Real.log n ≤ Real.log n' := Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast h)
  linarith

theorem phi_ok (A0 : ℕ) (c : Cell) (hc : CellOK A0 c) (n ln hn : ℕ) (hn0 : 0 < n)
    (hlog : c.A < n → LogOK (n, ln, hn)) :
    (phiLo n hn c : ℝ) ≤ Qn * TP * phiC (rc c).1 (rc c).2.1 ((n : ℝ) / Qn) ∧
    Qn * TP * phiC (rc c).1 (rc c).2.1 ((n : ℝ) / Qn) ≤ phiHi n ln c := by
  obtain ⟨_, hA0, hAB, hBQ, ⟨la1, la2⟩, ⟨lb1, lb2⟩⟩ := hc
  simp only [LogOK] at la1 la2 lb1 lb2
  have hQ := Qn_pos
  have hT := TP_pos
  simp only [rc]
  have hAr : (0 : ℝ) < c.A := by exact_mod_cast hA0
  have hABr : (c.A : ℝ) < c.B := by exact_mod_cast hAB
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hpa : 0 < (c.A : ℝ) / Qn := div_pos hAr hQ
  have hpab : (c.A : ℝ) / Qn ≤ (c.B : ℝ) / Qn := div_le_div_of_nonneg_right hABr.le hQ.le
  have hps : 0 < (n : ℝ) / Qn := div_pos hnr hQ
  have hnn := phiC_nonneg hpa hpab hps
  unfold phiLo phiHi
  by_cases h1 : n ≤ c.A
  · rw [if_pos h1, if_pos h1]
    have : (n : ℝ) / Qn ≤ (c.A : ℝ) / Qn := div_le_div_of_nonneg_right (by exact_mod_cast h1) hQ.le
    have h0 : phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((n : ℝ) / Qn) = 0 := by
      unfold phiC; rw [min_eq_right this, min_eq_right (le_trans this hpab)]; simp
    rw [h0]; simp
  rw [if_neg h1, if_neg h1]
  have h1' : c.A < n := Nat.lt_of_not_le h1
  obtain ⟨ln1, ln2⟩ := hlog h1'
  simp only at ln1 ln2
  have hAn : (c.A : ℝ) / Qn ≤ (n : ℝ) / Qn := div_le_div_of_nonneg_right (by exact_mod_cast h1'.le) hQ.le
  have hsub : ((n - c.A : ℕ) : ℝ) = n - c.A := Nat.cast_sub h1'.le
  have hNLa := NL_anti hA0 h1'.le
  by_cases h2 : n ≤ c.B
  · rw [if_pos h2, if_pos h2]
    have hnB : (n : ℝ) / Qn ≤ (c.B : ℝ) / Qn := div_le_div_of_nonneg_right (by exact_mod_cast h2) hQ.le
    have hval : (Qn : ℝ) * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((n : ℝ) / Qn) =
        n * (TP * NL c.A - TP * NL n) - (n - c.A) * TP := by
      unfold phiC
      rw [min_eq_right hnB, min_eq_left hAn, log_div_Q n hn0, log_div_Q c.A hA0]
      field_simp; ring
    have hnn' : (0 : ℝ) ≤ n * (TP * NL c.A - TP * NL n) - (n - c.A) * TP := by
      rw [← hval]; exact mul_nonneg (by positivity) hnn
    rw [hval]
    constructor
    · apply tsub_lo _ _ _ _ hnn'
      push_cast [Nat.cast_mul, hsub]
      have : ((c.lA - hn : ℕ) : ℝ) ≤ TP * NL c.A - TP * NL n :=
        tsub_lo _ _ _ (by linarith) (by nlinarith)
      nlinarith
    · apply tsub_hi
      push_cast [Nat.cast_mul, hsub]
      have : TP * NL c.A - TP * NL n ≤ ((c.hA - ln : ℕ) : ℝ) := tsub_hi _ _ _ (by linarith)
      nlinarith
  · rw [if_neg h2, if_neg h2]
    have h2' : c.B < n := Nat.lt_of_not_le h2
    have hnB : (c.B : ℝ) / Qn ≤ (n : ℝ) / Qn := div_le_div_of_nonneg_right (by exact_mod_cast h2'.le) hQ.le
    have hsubB : ((c.B - c.A : ℕ) : ℝ) = c.B - c.A := Nat.cast_sub hAB.le
    have hNLb := NL_anti hA0 hAB.le
    have hval : (Qn : ℝ) * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((n : ℝ) / Qn) =
        n * (TP * NL c.A - TP * NL c.B) - (c.B - c.A) * TP := by
      unfold phiC
      rw [min_eq_left hnB, min_eq_left hAn, log_div_Q c.B (lt_trans hA0 hAB), log_div_Q c.A hA0]
      field_simp; ring
    have hnn' : (0 : ℝ) ≤ n * (TP * NL c.A - TP * NL c.B) - (c.B - c.A) * TP := by
      rw [← hval]; exact mul_nonneg (by positivity) hnn
    rw [hval]
    constructor
    · apply tsub_lo _ _ _ _ hnn'
      push_cast [Nat.cast_mul, hsubB]
      have : ((c.lA - c.hB : ℕ) : ℝ) ≤ TP * NL c.A - TP * NL c.B :=
        tsub_lo _ _ _ (by linarith) (by nlinarith)
      nlinarith
    · apply tsub_hi
      push_cast [Nat.cast_mul, hsubB]
      have : TP * NL c.A - TP * NL c.B ≤ ((c.hA - c.lB : ℕ) : ℝ) := tsub_hi _ _ _ (by linarith)
      nlinarith

end S10
end Omega3
