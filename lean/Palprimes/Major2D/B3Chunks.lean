import Palprimes.Major2D.Chunk
import Palprimes.Major2D.B3C000
import Palprimes.Major2D.B3C001
import Palprimes.Major2D.B3C002

/-! # Base 3: the cell certificate from its 3 chunks -/

namespace Palprimes.M2

/-- the chunks `(offset, size)`. -/
def chunks3 : List (ℕ × ℕ) := [(0, 61), (61, 60), (121, 27)]

theorem chainOK3 : chainOK 0 chunks3 L3.length = true := by decide +kernel

theorem chunks3_ok : ∀ c ∈ chunks3, ((L3.drop c.1).take c.2).all
    (fun jk => checkRec cfg3 cfg3.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true :=
  List.forall_mem_cons.2 ⟨chk3_000, List.forall_mem_cons.2 ⟨chk3_001, List.forall_mem_cons.2 ⟨chk3_002, List.forall_mem_nil _⟩⟩⟩

/-- **The base-3 cell certificate** (all 148 level-0 cells). -/
theorem chk3 : checkList cfg3 L3 = true := by
  unfold checkList
  have := all_chunks2 _ L3 chunks3 0 chunks3_ok chainOK3
  simpa using this

end Palprimes.M2
