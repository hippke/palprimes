# Generators of the Ω ≤ 4 certificate files

These scripts write the generated Lean files of `Palprimes/Major1D/` and `Palprimes/Major2D/`. The proof
does not depend on them: the Lean files hold all the data, and the kernel checks every inequality
(`decide +kernel`). They are here so that the generated files can be reproduced.

```bash
lean/scripts/omega4/regen.sh   # needs python3 with mpmath, takes a few seconds
git status                     # expected: no change
```

| script | writes |
|---|---|
| `major1d/gen_lean.py` (uses `cells.py`, `conds.py`) | `Major1D/Data.lean`: 1D majorants for b = 4 to 9, cell lists, kernel checks |
| `major2d/gen.py b` (uses `ref.py`) | `Major2D/B2Data.lean`, `B3Data.lean`: majorant terms, phase tables, power tables, level-0 cells |
| `major2d/gen_chunks.py budget b` | `Major2D/B2C000` … `B2C110`, `B2Chunks` (budget 650), `B3C000` … `B3C002`, `B3Chunks` (budget 600) |
| `major2d/gen_tabs.py b` | `Major2D/B2Tab00` … `B2Tab10`, `B2Tab`, `B3Tab`; `tablv2.txt`, `tablv3.txt` are the `TabGood` lemmas pasted into `B2Check.lean`, `B3Check.lean` |
| `major2d/nodes.py b` | `nodes_b2.json`, `nodes_b3.json`: checker nodes per level-0 cell, the input of the chunking (minutes for b = 2) |

`majorants/` holds the eight majorants (JSON, coefficients over 2^52): `maj1d_b*_H*_p*.json` for b = 4 to 9,
`maj_b2_l7_*.json` (seven-digit blocks) and `maj_b3_l3_*.json` (three-digit blocks).
`ref.py` and `cells.py` are exact-integer mirrors of the Lean checkers.

The headers of the generated Lean files name the scripts by their paths in the development tree
(`lean/major1d/gen_lean.py`, `lean/major2d/gen.py`); here they are under `lean/scripts/omega4/`.
The search for the majorants (linear programming and ball-arithmetic certification, HiGHS and arb) is not
included. It only produced candidates, which the Lean kernel checks.
