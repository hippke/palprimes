import KappaOmega2.StatementsK
import Palprimes.ExpSum.Collision

/-!
# QK01_Exp: the product formula for the κ-sequence (shared by QK01 and LK14)

`f(α) = Σ_{u, w} (Π_k g(u_k)/W) e(n(u, w) α)` with `n(u, w) = Σ_k u_k c_k + w b^m`, and `A_q` written over the
index set `KVec × Fin W`.
-/

namespace KappaOmega2

namespace QK01

open Finset Palprimes

set_option linter.style.longLine false

/-- Index set `(u, w)`. -/
abbrev KIdx (b N : ℕ) := KVec b N × Fin (WK b N)

/-- `n(u, w)`. -/
def kv (b N : ℕ) (x : KIdx b N) : ℕ := kpalVal b N x.1 x.2

/-- `Π_k g(u_k) / W`. -/
noncomputable def kw (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (x : KIdx b N) : ℝ := wK b g N x.1 / (WK b N : ℝ)

lemma kpal_prod (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (α : ℝ) :
    ∏ k ∈ range (mK N), Gg b g ((cK b N k : ℝ) * α) =
      ∑ u : KVec b N, (wK b g N u : ℂ) * ee (((∑ k : Fin (mK N), (u k : ℕ) * cK b N k : ℕ) : ℝ) * α) := by
  unfold Gg
  rw [Finset.prod_range (fun k => ∑ a ∈ range b, (g a : ℂ) * ee ((a : ℝ) * ((cK b N k : ℝ) * α)))]
  simp_rw [Finset.sum_range (fun a => (g a : ℂ) * ee ((a : ℝ) * (_ * α)))]
  rw [Finset.prod_univ_sum (fun _ : Fin (mK N) => (Finset.univ : Finset (Fin b)))
    (fun k (a : Fin b) => (g a : ℂ) * ee (((a : ℕ) : ℝ) * ((cK b N k : ℝ) * α)))]
  rw [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib]
  unfold wK
  congr 1
  · push_cast; rfl
  · rw [← ee_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- The product formula `f(α) = Σ_{u,w} w(u)/W · e(n(u,w) α)`. -/
lemma fK_exp (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (α : ℝ) :
    fK b g N α = ∑ x : KIdx b N, (kw b g N x : ℂ) * ee ((kv b N x : ℝ) * α) := by
  unfold fK Mmid
  rw [kpal_prod, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun w => (1 / (WK b N : ℂ)) * ee ((w : ℝ) * ((b : ℝ) ^ mK N * α))),
    Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro w _
  unfold kw kv kpalVal
  have : (((∑ k : Fin (mK N), (u k : ℕ) * cK b N k + (w : ℕ) * b ^ mK N : ℕ) : ℝ) * α) =
      ((∑ k : Fin (mK N), (u k : ℕ) * cK b N k : ℕ) : ℝ) * α + ((w : ℕ) : ℝ) * ((b : ℝ) ^ mK N * α) := by
    push_cast; ring
  simp only
  rw [this, ee_add]
  push_cast
  ring

/-- `A_q` over the index set. -/
lemma AK_eq (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) :
    AK b g N q = ∑ x : KIdx b N,
      if Nat.Coprime (kv b N x) (bigB b) ∧ q ∣ kv b N x then kw b g N x else 0 := by
  unfold AK
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  rw [← Fin.sum_univ_eq_sum_range (fun w => if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ q ∣ kpalVal b N u w then
    wK b g N u / (WK b N : ℝ) else 0)]
  rfl

end QK01

end KappaOmega2
