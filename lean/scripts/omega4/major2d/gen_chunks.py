"""major2d: write the base-2 chunk files B2Cxxx.lean (node budget per chunk) and B2Chunks.lean.
usage: gen_chunks.py budget"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, glob, os
LEAN = os.path.join(HERE, '..', '..', '..', 'Palprimes', 'Major2D') + os.sep
budget = int(sys.argv[1])
B = sys.argv[2] if len(sys.argv) > 2 else "2"
nodes = json.load(open(os.path.join(HERE, f"nodes_b{B}.json")))
chunks = []; o = 0; acc = 0; start = 0
for i, n in enumerate(nodes):
    if acc + n > budget and i > start:
        chunks.append((start, i - start)); start = i; acc = 0
    acc += n
chunks.append((start, len(nodes) - start))
SKIP = os.environ.get("SKIP") == "1"
if not SKIP:
    for f in glob.glob(LEAN + f"B{B}C[0-9][0-9]*.lean"):
        os.remove(f)
k = len(chunks)
for i, (o, s) in enumerate(chunks):
    nn = sum(nodes[o:o + s])
    if SKIP:
        continue
    open(LEAN + f"B{B}C{i:03d}.lean", "w").write(f"""import Palprimes.Major2D.B{B}Cfg

/-! # Base {B}: cell certificate, chunk {i} of {k} (level-0 cells {o} … {o + s - 1}, {nn} checker nodes) -/

namespace Palprimes.M2

set_option maxRecDepth 100000 in
theorem chk{B}_{i:03d} : ((L{B}.drop {o}).take {s}).all
    (fun jk => checkRec cfg{B} cfg{B}.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true := by decide +kernel

end Palprimes.M2
""")
imports = "\n".join(f"import Palprimes.Major2D.B{B}C{i:03d}" for i in range(k))
cs = ", ".join(f"({o}, {s})" for (o, s) in chunks)
proof = "List.forall_mem_nil _"
for i in reversed(range(k)):
    proof = f"List.forall_mem_cons.2 ⟨chk{B}_{i:03d}, {proof}⟩"
open(LEAN + f"B{B}Chunks.lean", "w").write(f"""import Palprimes.Major2D.Chunk
{imports}

/-! # Base {B}: the cell certificate from its {k} chunks -/

namespace Palprimes.M2

/-- the chunks `(offset, size)`. -/
def chunks{B} : List (ℕ × ℕ) := [{cs}]

theorem chainOK{B} : chainOK 0 chunks{B} L{B}.length = true := by decide +kernel

theorem chunks{B}_ok : ∀ c ∈ chunks{B}, ((L{B}.drop c.1).take c.2).all
    (fun jk => checkRec cfg{B} cfg{B}.dmax 0 (2 * jk.1 + 1) (2 * jk.2 + 1)) = true :=
  {proof}

/-- **The base-{B} cell certificate** (all {len(nodes)} level-0 cells). -/
theorem chk{B} : checkList cfg{B} L{B} = true := by
  unfold checkList
  have := all_chunks2 _ L{B} chunks{B} 0 chunks{B}_ok chainOK{B}
  simpa using this

end Palprimes.M2
""")
print("chunks", k, "max nodes", max(sum(nodes[o:o+s]) for o, s in chunks))
