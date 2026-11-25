import Omega3.Items.S10_Check

/-!
# S10 helpers, part 5: grid sums, the lower bound of `g_η` on a box, the box test
-/

set_option linter.style.longLine false

open Real Set

namespace Omega3
namespace S10

def Pn (n hn : ℕ) (cs : List Cell) : ℕ := (cs.map (fun c => if 0 < c.m then c.m.toNat * phiLo n hn c else 0)).sum
def Nn (n ln : ℕ) (cs : List Cell) : ℕ := (cs.map (fun c => if c.m < 0 then (-c.m).toNat * phiHi n ln c else 0)).sum
def A1hi (cs : List Cell) : ℤ :=
  (cs.map (fun c => if 0 < c.m then c.m * (phiHi Qn 0 c : ℤ) else c.m * (phiLo Qn 0 c : ℤ))).sum

/-- `Â(s)` as a sum over real cells. -/
noncomputable def AR (cs : List Cell) (s : ℝ) : ℝ := (cs.map (fun c => (rc c).2.2 * phiC (rc c).1 (rc c).2.1 s)).sum

lemma En_pos : (0 : ℝ) < En := by norm_num [En]

lemma LogOK_Q : LogOK (Qn, 0, 0) := by simp [LogOK, NL]

lemma phi_nonneg_c (A0 : ℕ) (c : Cell) (hc : CellOK A0 c) (s : ℝ) (hs : 0 < s) : 0 ≤ phiC (rc c).1 (rc c).2.1 s := by
  obtain ⟨_, hA0, hAB, _, _, _⟩ := hc
  simp only [rc]
  apply phiC_nonneg (div_pos (by exact_mod_cast hA0) Qn_pos)
    (div_le_div_of_nonneg_right (by exact_mod_cast hAB.le) Qn_pos.le) hs

lemma phiC_mono_c (A0 : ℕ) (c : Cell) (hc : CellOK A0 c) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    phiC (rc c).1 (rc c).2.1 s ≤ phiC (rc c).1 (rc c).2.1 s' := by
  obtain ⟨_, hA0, hAB, _, _, _⟩ := hc
  simp only [rc]
  exact phiC_mono (div_pos (by exact_mod_cast hA0) Qn_pos)
    (div_le_div_of_nonneg_right (by exact_mod_cast hAB.le) Qn_pos.le) hs hss

/-- Lower bound of `Â(s)` on `[nl/Q, nh/Q]`. -/
theorem AR_box (A0 : ℕ) (cs : List Cell) (hcs : ∀ c ∈ cs, CellOK A0 c) (nl ll hl nh lh hh : ℕ)
    (hnl : A0 ≤ nl → LogOK (nl, ll, hl)) (hnh : A0 ≤ nh → LogOK (nh, lh, hh)) (s : ℝ) (hs0 : 0 < s)
    (hs1 : (nl : ℝ) / Qn ≤ s) (hs2 : s ≤ (nh : ℝ) / Qn) :
    ((Pn nl hl cs : ℝ) - Nn nh lh cs) / (Qn * TP * En) ≤ AR cs s := by
  have hK : (0 : ℝ) < Qn * TP * En := by have := Qn_pos; have := TP_pos; have := En_pos; positivity
  induction cs with
  | nil => simp [Pn, Nn, AR]
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have ih' := ih (fun c' hc' => hcs c' (by simp [hc']))
    simp only [Pn, Nn, AR, List.map_cons, List.sum_cons] at ih' ⊢
    have hterm : ((if 0 < c.m then c.m.toNat * phiLo nl hl c else 0 : ℕ) : ℝ) -
        ((if c.m < 0 then (-c.m).toNat * phiHi nh lh c else 0 : ℕ) : ℝ) ≤
        Qn * TP * En * ((rc c).2.2 * phiC (rc c).1 (rc c).2.1 s) := by
      have hA0 := hc.1
      simp only [rc]
      rcases lt_trichotomy c.m 0 with hm | hm | hm
      · rw [if_neg (not_lt.mpr hm.le), if_pos hm]
        have hnh0 : 0 < nh := by
          have : (0 : ℝ) < nh / Qn := lt_of_lt_of_le hs0 hs2
          have : (0 : ℝ) < nh := by have := Qn_pos; exact (div_pos_iff_of_pos_right this).mp ‹_›
          exact_mod_cast this
        obtain ⟨_, p2⟩ := phi_ok A0 c hc nh lh hh hnh0 (fun h => hnh (le_trans hA0 h.le))
        have hmono := phiC_mono_c A0 c hc hs0 hs2
        have hmR : ((-c.m).toNat : ℝ) = -(c.m : ℝ) := by
          have : (((-c.m).toNat : ℤ) : ℝ) = ((-c.m : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
          push_cast at this; exact this
        push_cast [hmR]
        simp only [rc] at p2
        have hmneg : (c.m : ℝ) < 0 := by exact_mod_cast hm
        have : (c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) s ≥
            (c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((nh : ℝ) / Qn) :=
          mul_le_mul_of_nonpos_left hmono (div_nonpos_of_nonpos_of_nonneg hmneg.le En_pos.le)
        have hE := En_pos
        have e1 : (Qn : ℝ) * TP * En * ((c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((nh : ℝ) / Qn)) =
            (c.m : ℝ) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) ((nh : ℝ) / Qn)) := by
          field_simp
        nlinarith [mul_le_mul_of_nonpos_left p2 hmneg.le]
      · simp [hm]
      · rw [if_pos hm, if_neg (not_lt.mpr hm.le)]
        have hmR : (c.m.toNat : ℝ) = (c.m : ℝ) := by
          have : ((c.m.toNat : ℤ) : ℝ) = ((c.m : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
          push_cast at this; exact this
        push_cast [hmR]
        have hmpos : (0 : ℝ) < c.m := by exact_mod_cast hm
        have hE := En_pos
        rcases Nat.eq_zero_or_pos nl with h0 | h0
        · subst h0
          have : phiLo 0 hl c = 0 := by simp [phiLo]
          rw [this]; simp only [Nat.cast_zero, mul_zero, sub_zero]
          have := phi_nonneg_c A0 c hc s hs0
          simp only [rc] at this
          positivity
        · obtain ⟨p1, _⟩ := phi_ok A0 c hc nl ll hl h0 (fun h => hnl (le_trans hA0 h.le))
          have hmono := phiC_mono_c A0 c hc (div_pos (by exact_mod_cast h0) Qn_pos) hs1
          simp only [rc] at p1 hmono
          have e1 : (Qn : ℝ) * TP * En * ((c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) s) =
              (c.m : ℝ) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) s) := by
            field_simp
          rw [e1]
          have hQT : (0 : ℝ) ≤ Qn * TP := by have := Qn_pos; have := TP_pos; positivity
          nlinarith [mul_le_mul_of_nonneg_left hmono hQT, mul_le_mul_of_nonneg_left p1 hmpos.le]
    rw [div_le_iff₀ hK] at ih' ⊢
    rw [Nat.cast_add, Nat.cast_add]
    nlinarith [hterm, ih']

theorem AR_one (A0 : ℕ) (cs : List Cell) (hcs : ∀ c ∈ cs, CellOK A0 c) :
    AR cs 1 ≤ (A1hi cs : ℝ) / (Qn * TP * En) := by
  have hK : (0 : ℝ) < Qn * TP * En := by have := Qn_pos; have := TP_pos; have := En_pos; positivity
  have hQ1 : (Qn : ℝ) / Qn = 1 := div_self Qn_pos.ne'
  induction cs with
  | nil => simp [A1hi, AR]
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have ih' := ih (fun c' hc' => hcs c' (by simp [hc']))
    simp only [A1hi, AR, List.map_cons, List.sum_cons] at ih' ⊢
    rw [le_div_iff₀ hK] at ih' ⊢
    obtain ⟨p1, p2⟩ := phi_ok A0 c hc Qn 0 0 (by norm_num [Qn]) (fun _ => LogOK_Q)
    rw [hQ1] at p1 p2
    simp only [rc] at p1 p2 ⊢
    have hE := En_pos
    have e1 : (Qn : ℝ) * TP * En * ((c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1) =
        (c.m : ℝ) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1) := by field_simp
    have hterm : (c.m : ℝ) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1) ≤
        (((if 0 < c.m then c.m * (phiHi Qn 0 c : ℤ) else c.m * (phiLo Qn 0 c : ℤ)) : ℤ) : ℝ) := by
      split_ifs with hm
      · push_cast; exact mul_le_mul_of_nonneg_left p2 (by exact_mod_cast hm.le)
      · push_cast; exact mul_le_mul_of_nonpos_left p1 (by exact_mod_cast (not_lt.mp hm))
    rw [Int.cast_add, add_mul]
    have e2 : (c.m : ℝ) / En * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1 * (Qn * TP * En) =
        (c.m : ℝ) * (Qn * TP * phiC ((c.A : ℝ) / Qn) ((c.B : ℝ) / Qn) 1) := by rw [mul_comm]; exact e1
    simp only [rc] at ih'
    rw [e2]
    linarith

/-! ## The minimum of the step function on a box -/

noncomputable def eminR : ℝ → List (ℚ × ℚ) → ℝ → ℝ → ℝ
  | acc, [], _, _ => acc
  | acc, p :: rest, u1, u2 =>
    if (p.1 : ℝ) ≤ u1 then eminR (p.2 : ℝ) rest u1 u2 else if u2 < (p.1 : ℝ) then acc else min acc (eminR (p.2 : ℝ) rest u1 u2)

theorem eval_ge_emin : ∀ (l : List (ℚ × ℚ)) (acc u1 u2 u : ℝ), Sorted l → u1 ≤ u → u ≤ u2 →
    eminR acc l u1 u2 ≤ l.foldl (stp u) acc
  | [], acc, u1, u2, u, _, _, _ => le_rfl
  | p :: rest, acc, u1, u2, u, hs, h1, h2 => by
    have hs' : Sorted rest := (List.pairwise_cons.mp hs).2
    have hlt : ∀ q ∈ rest, (p.1 : ℝ) < (q.1 : ℝ) := fun q hq => by
      exact_mod_cast (List.pairwise_cons.mp hs).1 q hq
    simp only [eminR, List.foldl_cons]
    by_cases ha : (p.1 : ℝ) ≤ u1
    · rw [if_pos ha]
      have : stp u acc p = (p.2 : ℝ) := by simp only [stp]; rw [if_pos (le_trans ha h1)]
      rw [this]; exact eval_ge_emin rest _ u1 u2 u hs' h1 h2
    · rw [if_neg ha]
      by_cases hb : u2 < (p.1 : ℝ)
      · rw [if_pos hb]
        have hu : u < (p.1 : ℝ) := lt_of_le_of_lt h2 hb
        have : stp u acc p = acc := by simp only [stp]; rw [if_neg (not_le.mpr hu)]
        rw [this, foldl_stp_const u rest acc (fun q hq => lt_trans hu (hlt q hq))]
      · rw [if_neg hb]
        by_cases hu : (p.1 : ℝ) ≤ u
        · have : stp u acc p = (p.2 : ℝ) := by simp only [stp]; rw [if_pos hu]
          rw [this]; exact le_trans (min_le_right _ _) (eval_ge_emin rest _ u1 u2 u hs' h1 h2)
        · have hu' : u < (p.1 : ℝ) := not_le.mp hu
          have : stp u acc p = acc := by simp only [stp]; rw [if_neg hu]
          rw [this, foldl_stp_const u rest acc (fun q hq => lt_trans hu' (hlt q hq))]
          exact min_le_left _ _

def eminN : ℤ → List Cell → ℕ → ℕ → ℤ
  | acc, [], _, _ => acc
  | acc, c :: rest, U1, U2 => if c.A ≤ U1 then eminN c.m rest U1 U2 else if U2 < c.A then acc else min acc (eminN c.m rest U1 U2)

/-- The step function of a cell list. -/
def stepOfCells (cs : List Cell) : StepFn := cs.map (fun c => ((c.A : ℚ) / Qn, (c.m : ℚ) / En))

theorem eminN_eq : ∀ (cs : List Cell) (acc : ℤ) (U1 U2 : ℕ),
    eminR ((acc : ℝ) / En) (stepOfCells cs) ((U1 : ℝ) / Qn) ((U2 : ℝ) / Qn) = (eminN acc cs U1 U2 : ℝ) / En
  | [], acc, U1, U2 => rfl
  | c :: rest, acc, U1, U2 => by
    simp only [stepOfCells, List.map_cons, eminR, eminN] at *
    have hQ := Qn_pos
    have e1 : (((c.A : ℚ) / Qn : ℚ) : ℝ) = (c.A : ℝ) / Qn := by push_cast; rfl
    have e2 : (((c.m : ℚ) / En : ℚ) : ℝ) = (c.m : ℝ) / En := by push_cast; rfl
    rw [e1, e2]
    have c1 : (c.A : ℝ) / Qn ≤ (U1 : ℝ) / Qn ↔ c.A ≤ U1 := by
      rw [div_le_div_iff_of_pos_right hQ]; exact_mod_cast Iff.rfl
    have c2 : (U2 : ℝ) / Qn < (c.A : ℝ) / Qn ↔ U2 < c.A := by
      rw [div_lt_div_iff_of_pos_right hQ]; exact_mod_cast Iff.rfl
    have ih := eminN_eq rest c.m U1 U2
    simp only [stepOfCells] at ih
    by_cases h1 : c.A ≤ U1
    · rw [if_pos (c1.mpr h1), if_pos h1, ih]
    · rw [if_neg (fun h => h1 (c1.mp h)), if_neg h1]
      by_cases h2 : U2 < c.A
      · rw [if_pos (c2.mpr h2), if_pos h2]
      · rw [if_neg (fun h => h2 (c2.mp h)), if_neg h2, ih]
        push_cast
        rw [min_div_div_right En_pos.le]

end S10
end Omega3
